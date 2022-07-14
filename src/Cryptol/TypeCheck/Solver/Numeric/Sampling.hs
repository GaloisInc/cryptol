{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Cryptol.TypeCheck.Solver.Numeric.Sampling where

import Cryptol.Testing.Random
import Cryptol.TypeCheck.AST
import System.Random.TF.Gen (RandomGen)
import Cryptol.Utils.Panic (panic)
import Cryptol.TypeCheck.Solver.InfNat

import Cryptol.TypeCheck.Solver.Numeric.Sampling.Base
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Preconstraints
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Constraints
import Cryptol.TypeCheck.Solver.Numeric.Sampling.System
import qualified Cryptol.TypeCheck.Solver.Numeric.Sampling.Exp as Exp
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Q
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Sampling (sample)

-- Tries to make a sampler of type `Gen g (TParam, Type)` if the input is in the
-- handled domain and a solution is found by the algorithm.
makeSampler ::
  forall g.
  RandomGen g =>
  [TParam] ->
  [Prop] ->
  Maybe (Gen g (TParam, Type))
makeSampler tparams props = do
  case runsamplingM m of
    Left err -> panic "makeSampler" ["Error during sampler generation: " ++ show err]
    Right Nothing -> Nothing
    Right (Just _) -> undefined
  where 
    m :: SamplingM (Gen g (TParam, Type))
    m = do
      somePrecons <- fromProps tparams props
      someCon <- fromPreconstraints somePrecons
      -- gaussian elimination
      someCon <- case someCon of
        SomeConstraints con -> do
          sys' <- elimGauss (sys con)
          pure $ SomeConstraints (con {sys = sys'})
      -- cast everything from Q to Nat'
      someCon <- case someCon of
        SomeConstraints con -> do
          sys' <- elimDens (sys con)
          tcs' <- pure $ (\(Tc tcName e) -> Tc tcName (Exp.extendN e)) <$> tcs con
          tcs' <- mapM (\(Tc tcName e) -> do
            case mapM fromQ e of
              Just e' -> pure $ Tc tcName $ Nat <$> e'
              Nothing -> throwSamplingError undefined 
            ) tcs'
          pure $ SomeConstraints $ Constraints {
            sys = sys',
            tcs = tcs'
          }
      -- produce sampler
      pure $ sample someCon
  
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