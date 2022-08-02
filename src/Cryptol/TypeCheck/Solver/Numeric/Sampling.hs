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
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Base
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Preconstraints
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Constraints
import Cryptol.TypeCheck.Solver.Numeric.Sampling.System
import qualified Cryptol.TypeCheck.Solver.Numeric.Sampling.Exp as Exp
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Q
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Sampling as Sampling
import Data.Vector.Primitive (Vector(Vector))
import Cryptol.TypeCheck.Solver.Numeric.Sampling.SolvedSystem (toSolvedSystem, elimDens)
import qualified Data.Vector as V
import Control.Monad
import Data.Bifunctor (Bifunctor(first))

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

type Sample = [(TParam, Type)]

sample ::
  forall g.
  RandomGen g =>
  [TParam] ->
  [Prop] ->
  Int ->
  -- GenM g [Sample]
  SamplingM (GenM g) [Sample] -- TODO
sample tparams props nLiteralSamples = do
  lift (runSamplingM m) >>= \case
    Left err -> panic "sample" ["Error during sampling literals: " ++ show err]
    Right sampling -> pure sampling
  where
    m :: SamplingM (GenM g) [Sample]
    m = do
      precons <- fromProps tparams props
      cons <- fromPreconstraints precons
      -- solve system
      cons <- do
        -- gaussian elimination
        cons <- overSystem solveGauss cons
        -- verify gaussian-eliminated form
        cons <- solveSystemVia toSolvedSystem cons
        -- eliminate denomenators
        cons <- elimDens cons
        -- 
        pure cons
      -- sample `nLiteralSamples` number of times
      replicateM nLiteralSamples do
        vals <- V.toList <$> Sampling.sample cons
        pure (tparams `zip` ((\v -> TCon (TC (TCNum v)) []) <$> vals))

applySample :: Sample -> Schema -> Schema
applySample sample Forall {sVars, sProps, sType} = 
  Forall {
    -- only keep vars that are not substituted by sample
    sVars = filter (not . (`elem` (fst <$> sample))) sVars,
    sProps = apSubst subst sProps,
    sType = apSubst subst sType
  }
  where
    subst = listSubst $ first TVBound <$> sample