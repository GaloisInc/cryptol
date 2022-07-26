{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant pure" #-}


module Cryptol.TypeCheck.Solver.Numeric.Sampling where

import Cryptol.Testing.Random
import Cryptol.TypeCheck.AST
import System.Random.TF.Gen (RandomGen)
import Cryptol.Utils.Panic (panic)
import Cryptol.TypeCheck.Solver.InfNat
import GHC.TypeNats

import Cryptol.TypeCheck.Solver.Numeric.Sampling.Base
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Preconstraints
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Constraints
import Cryptol.TypeCheck.Solver.Numeric.Sampling.System
import qualified Cryptol.TypeCheck.Solver.Numeric.Sampling.Exp as Exp
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Q
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Sampling (sample)
import Data.Vector.Primitive (Vector(Vector))
import Cryptol.TypeCheck.Solver.Numeric.Sampling.SolvedSystem (toSolvedSystem, elimDens)
import qualified Data.Vector as V

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
makeSampler ::
  forall g.
  RandomGen g =>
  [TParam] ->
  [Prop] ->
  GenM g [(TParam, Nat')]
makeSampler tparams props =
  runSamplingM m >>= \case 
    Left err -> panic "makeSampler" ["Error during sampling literals: " ++ show err]
    Right sampling -> pure sampling
  where
    m :: SamplingM (GenM g) [(TParam, Nat')]
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
      vals <- V.toList <$> sample cons
      pure (tparams `zip` vals)

