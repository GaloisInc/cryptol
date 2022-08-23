{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant pure" #-}
{-# LANGUAGE NamedFieldPuns #-}


module Cryptol.TypeCheck.Solver.Numeric.Sampling where

import Cryptol.Testing.Random
import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.TCon
import System.Random.TF.Gen (RandomGen)
import Cryptol.Utils.Panic (panic)
import Cryptol.TypeCheck.Solver.InfNat
import Cryptol.TypeCheck.Subst
import Control.Monad.Trans
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Base as Base
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Preconstraints as Precons
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Constraints as Cons
import Cryptol.TypeCheck.Solver.Numeric.Sampling.System as Sys
import qualified Cryptol.TypeCheck.Solver.Numeric.Sampling.Exp as Exp
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Q
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Sampling as Sampling
import Data.Vector.Primitive (Vector(Vector))
import qualified Data.Vector as V
import Control.Monad
import Data.Bifunctor (Bifunctor(first, bimap))
import Cryptol.TypeCheck.Solver.Numeric.Sampling.SolvedConstraints (toSolvedConstraints, elimDens)

-- Tries to make a sampler of type `[(TParam, Nat')]` if the input is in the
-- handled domain and a solution is found by the algorithm.
{-
Steps:
1. Translate Prop -> Preconstraints
2. Solve system of equations and cast from domain Q to Int
  1. Solve system
  2. Cast everything from Q to Nat'
3. Sample constraints
  1. Collect upper bounds on each var
  2. Sampling procedure:
    1. Evaluate each var in order, statefully keeping track of evaluations so far
    2. To evaluate a var:
      - if it's already been evaluated, use that value
      - if it's not been evaluated and it's assigned to an expression 
-}

type Sample = [(TParam, Integer)]

sample ::
  [TParam] ->
  [Prop] ->
  Int ->
  SamplingM [Sample]
sample tparams props nLiteralSamples = do
  liftIO (runSamplingM m) >>= \case
    Left err -> panic "sample" ["Error during sampling literals: " ++ show err]
    Right sampling -> pure sampling
  where
    m :: SamplingM [Sample]
    m = do
      precons <- fromProps tparams props
      debug' 0 $ "precons = " ++ show precons
      cons <- toConstraints precons
      debug' 0 $ "cons <- toConstraints precons"
      debug' 0 $ "cons = " ++ show cons
      -- solve constraints system
      solcons <- do
        -- gaussian elimination
        cons <- overSystem (solveGauss (Cons.countVars cons)) cons
        debug' 0 $ "cons <- overSystem solveGauss cons"
        debug' 0 $ "cons = " ++ show cons
        -- verify gaussian-eliminated form
        solcons <- toSolvedConstraints cons
        debug' 0 $ "solcons <- toSolvedConstraints cons"
        debug' 0 $ "solcons = " ++ show solcons
        -- eliminate denomenators
        solcons <- elimDens solcons
        debug' 0 $ "solcons <- elimDens solcons"
        debug' 0 $ "solcons = " ++ show solcons
        --
        pure solcons
      -- 
      -- sample `nLiteralSamples` number of times
      replicateM nLiteralSamples do
        vals <- V.toList <$> Sampling.sample solcons
        debug' 0 $ "vals = " ++ show vals
        -- pure (tparams `zip` ((\v -> TCon (TC (TCNum v)) []) <$> vals))
        pure (tparams `zip` vals)

applySample :: Sample -> Schema -> Schema
applySample sample Forall {sVars, sProps, sType} =
  Forall {
    -- only keep vars that are not substituted by sample
    sVars = filter (not . (`elem` (fst <$> sample))) sVars,
    sProps = apSubst subst sProps,
    sType = apSubst subst sType
  }
  where
    subst = listSubst $ bimap TVBound (\n -> TCon (TC (TCNum n)) []) <$> sample