{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# HLINT ignore "Redundant pure" #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Cryptol.TypeCheck.Solver.Numeric.Sampling.SolvedSystem where

import Control.Monad
import Cryptol.TypeCheck.Solver.InfNat (Nat')
import qualified Cryptol.TypeCheck.Solver.InfNat as Nat'
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Base
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Exp (Exp (..), Var (..))
import qualified Cryptol.TypeCheck.Solver.Numeric.Sampling.Exp as Exp
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Q
import Cryptol.TypeCheck.Solver.Numeric.Sampling.System (IxEqu (..), System)
import qualified Cryptol.TypeCheck.Solver.Numeric.Sampling.System as System
import Data.Bifunctor (Bifunctor (bimap, first, second))
import qualified Data.List as L
import Data.Maybe
import Data.Vector (Vector)
import qualified Data.Vector as V
import GHC.Real

-- | SolvedSystem If equ `i` is `Nothing`, then var `i` is free. If equ `i` is
-- `Just e`, then var `i` is bound to expression `e`. A `SolvedSystem`
-- corresponds to an `n` by `n + 1` matrix, or `n` equations of the form:
-- ```
--   x0 = ...
--   x1 = ...
--   ...
--   x{n} = ...
-- ```
-- where the RHS expression for equation `i` must have `0*xi`. Since each
-- equation corresponds to a var, a SolvedSystem is indexed by `Var`.
type SolvedSystem a = Vector (Maybe (Exp a))

countVars :: SolvedSystem a -> Int
countVars sys = case V.find isJust sys of
  Just (Just e) -> Exp.countVars e
  _ -> error "countVars mempty"

(!) :: SolvedSystem a -> Var -> Maybe (Exp a)
solsys ! j = solsys V.! unVar j

(//) :: SolvedSystem a -> [(Var, Maybe (Exp a))] -> SolvedSystem a
solsys // mods = solsys V.// (first unVar <$> mods)

-- A valid `System` is converted to a `SolvedSystem`. If the `System` is in an
-- invalid form, then throws `invalidGaussElim`.
toSolvedSystem :: forall m a. Monad m => (Num a, Eq a) => System a -> SamplingM m (SolvedSystem a)
toSolvedSystem sys = do
  let n = System.countVars sys
  foldM fold (V.replicate n Nothing) sys
  where
    fold :: SolvedSystem a -> Exp a -> SamplingM m (SolvedSystem a)
    fold solsys e = do
      -- if `e` solves for a var `j`, then insert the appropriate equ into
      -- `solsys`, otherwise ignore
      extractSolution e >>= \case
        Just (j, e) -> pure $ solsys // [(j, Just e)]
        Nothing -> pure solsys
      where
        -- 1*x0 + 2*x1 = 10 ==> Just (0, 0*x0 + (-2)*x1 + 10)
        -- 0*x0 + 0*x1 = 0  ==> Nothing
        -- _                ==> error noSampling (invalid form)
        extractSolution :: Exp a -> SamplingM m (Maybe (Var, Exp a))
        extractSolution e@(Exp as c) =
          -- find index of first var with non-0 coeff
          -- if coeff is 1, then Just solve for this var, else error
          -- if there is no non-0 coeff, then Nothing
          case Var <$> V.findIndex (0 /=) as of
            Just i 
              | e Exp.! i == 1 -> pure $ Just (i, Exp.solveFor i e)
              | otherwise -> throwSamplingError $ 
                SamplingError "toSolvedSystem"
                  "A leftmost non-0 coeff in row is not 1"
            Nothing -> pure Nothing

-- SolvedSystem n -> SolvedSystem (n + m)
extendN :: Num a => Int -> SolvedSystem a -> SolvedSystem a
extendN m sys = fmap (Exp.extendN m) <$> sys

-- | Expands all variables with non-integral coefficients to be written in terms
-- of newly-introduced variables with integral coefficients. For example
-- consider the following solved system:
-- ```
--    x = (1/2)z
--    y = (1/3)z
-- ```
-- We can expand `z` so that the system contains only integral coefficients by
-- introducing a new variable `z'`.
-- ```
--    x  = 3z'
--    y  = 2z'
--    z' = 6z
-- ```
-- This expansion process introduces at most `n` new variables, so the result is
-- a system of `n + n` variables.
--
-- elimDens :: SolvedSystem n -> SolvedSystem (n + n)
elimDens :: forall m. Monad m => SolvedSystem Q -> SamplingM m (SolvedSystem Nat')
elimDens solsys = do
  -- solsys <- V.foldM fold (extendN n solsys) (V.generate n Var)
  -- mapM (maybe (pure Nothing) (fmap pure . cast_ExpQ_ExpNat')) solsys
  --
  -- extend exps to have `n + n` variables
  solsys <- pure $ fmap (Exp.extendN (n + n)) <$> solsys
  -- init equs `n` through `n + n - 1` with `Nothing`
  solsys <- pure $ solsys <> V.replicate n Nothing
  -- elim dens
  solsys <- foldM fold solsys (Var <$> [0 .. n -1])
  -- cast to Nat'
  mapM (maybe (pure Nothing) (fmap pure . cast_ExpQ_ExpNat')) solsys
  where
    n = countVars solsys

    fold ::
      SolvedSystem Q ->
      Var ->
      SamplingM m (SolvedSystem Q)
    fold solsys j = do
      let -- collect coeffs of `xj` in `solsys`, excluding coeffs 0, 1
          coeffs :: Vector Q
          coeffs =
            -- ignore Nothing, Just 0, and Just 1
            foldMap
              ( maybe
                  mempty
                  (\a -> if a `elem` [0, 1] then mempty else pure a)
              )
              $ fmap (Exp.! j) <$> solsys
          -- compute lcm of denoms of coeffs
          a :: Q
          a = toRational $ foldr lcm (1 :: Int) dens
            where
              dens = fromInteger . denominator <$> coeffs
      -- replcate all appearances `aj*xj` with `0*xj + (a*aj)*x{j+1}`
      solsys <-
        pure $
          fmap (\e -> e Exp.// [(j, 0), (j + Var n, a * e Exp.! j)])
            <$> solsys
      -- include new equation `a{j+1} = a*xj`
      solsys <- pure $ solsys // [(j + Var n, Just $ Exp.fromConstant (n + n) 0 Exp.// [(j + 1, a)])]
      --
      pure solsys

    -- preserves number of vars
    cast_ExpQ_ExpNat' :: Exp Q -> SamplingM m (Exp Nat')
    cast_ExpQ_ExpNat' e = mapM cast_Q_Nat' e

    cast_Q_Nat' :: Q -> SamplingM m Nat'
    cast_Q_Nat' q = case fromQ q of
      Just n -> pure . Nat'.Nat $ n
      Nothing -> throwSamplingError (SamplingError "elimDens" "After eliminating denomenators, there are still some nonintegral values left in equations.")

{-
example
--------------------------------------------------
x + (1/2)y = 10
    (1/3)y = 10
--------------------------------------------------
j = 1
coeffs = [(1/2), (1/3)]
jDenLcm = 6
--------------------------------------------------
x + ((1/2) * 6)z = 10
x + ((1/3) * 6)z = 10
--------------------------------------------------
x + 3z = 10
x + 2z = 10
y = 6z
--------------------------------------------------
-}
