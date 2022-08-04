{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# HLINT ignore "Redundant pure" #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Cryptol.TypeCheck.Solver.Numeric.Sampling.SolvedConstraints where

import Control.Monad
import Cryptol.TypeCheck.Solver.InfNat (Nat')
import qualified Cryptol.TypeCheck.Solver.InfNat as Nat'
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Base
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Constraints (Constraints, Equ (..), System, Tc)
import qualified Cryptol.TypeCheck.Solver.Numeric.Sampling.Constraints as Cons
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Exp (Exp (..), Var (..))
import qualified Cryptol.TypeCheck.Solver.Numeric.Sampling.Exp as Exp
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Preconstraints (SamplingParam)
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Q
import qualified Cryptol.TypeCheck.Solver.Numeric.Sampling.System as Sys
import Cryptol.Utils.PP (pp, ppList)
import Data.Bifunctor (Bifunctor (first))
import Data.Vector (Vector)
import qualified Data.Vector as V
import GHC.Real

-- | SolvedConstraints
data SolvedConstraints a = SolvedConstraints
  { solsys :: SolvedSystem a,
    tcs :: [Tc a],
    params :: Vector SamplingParam
  }

instance Show a => Show (SolvedConstraints a) where
  show solcons@SolvedConstraints {..} =
    unlines
      [ "SolvedConstraints:",
        "  solsys:\n"
          ++ (unlines . V.toList)
            ( fmap
                ( ("    " ++)
                    . (\(i, s) -> "x{" ++ show i ++ "} = " ++ s)
                )
                . V.zip (V.generate (countVars solcons) id)
                . fmap (maybe "free" show)
                $ solsys
            ),
        "  tcs:    " ++ show tcs,
        "  params: " ++ show (ppList (V.toList (pp <$> params)))
      ]

-- includes generated vars
countVars :: SolvedConstraints a -> Int
countVars solcons = V.length (solsys solcons)

toSolvedConstraints :: (Num a, Eq a) => Constraints a -> SamplingM (SolvedConstraints a)
toSolvedConstraints cons = do
  solsys <- toSolvedSystem (Cons.sys cons)
  pure
    SolvedConstraints
      { solsys = solsys,
        tcs = Cons.tcs cons,
        params = Cons.params cons
      }

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

-- countVars :: SolvedSystem a -> Int
-- countVars sys = case V.find isJust sys of
--   Just (Just e) -> Exp.countVars e
--   _ -> error "countVars mempty"

(!) :: SolvedSystem a -> Var -> Maybe (Exp a)
solsys ! j = solsys V.! unVar j

(//) :: SolvedSystem a -> [(Var, Maybe (Exp a))] -> SolvedSystem a
solsys // mods = solsys V.// (first unVar <$> mods)

-- A valid `System` is converted to a `SolvedSystem`. If the `System` is in an
-- invalid form, then throws `invalidGaussElim`.
toSolvedSystem :: forall a. (Num a, Eq a) => System a -> SamplingM (SolvedSystem a)
toSolvedSystem sys = do
  if null sys
    then pure $ V.fromList []
    else do
      let n = Sys.countVars sys
      foldM fold (V.replicate n Nothing) sys
  where
    fold :: SolvedSystem a -> Equ a -> SamplingM (SolvedSystem a)
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
        extractSolution :: Equ a -> SamplingM (Maybe (Var, Exp a))
        extractSolution (Equ e@(Exp as _c)) =
          -- find index of first var with non-0 coeff
          -- if coeff is 1, then Just solve for this var, else error
          -- if there is no non-0 coeff, then Nothing
          case Var <$> V.findIndex (0 /=) as of
            Just i
              | e Exp.! i == 1 -> pure $ Just (i, Exp.solveFor i e)
              | otherwise ->
                throwSamplingError $
                  SamplingError
                    "toSolvedSystem"
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
elimDens :: SolvedConstraints Q -> SamplingM (SolvedConstraints Nat')
elimDens solcons = do
  solsys <- pure $ solsys solcons
  -- pad exps to have `n + n` variables
  solsys <- pure $ fmap (Exp.pad (n + n)) <$> solsys
  -- init equs `n` through `n + n - 1` with `Nothing`
  solsys <- pure $ solsys <> V.replicate n Nothing
  -- elim dens
  solsys <- foldM fold solsys (Var <$> [0 .. n - 1])
  -- cast to Nat'
  solsys <- mapM (maybe (pure Nothing) (fmap pure . cast_ExpQ_ExpNat')) solsys
  tcs <- mapM (Cons.overTcExp cast_ExpQ_ExpNat') (tcs solcons)
  pure solcons {solsys = solsys, tcs = tcs}
  where
    n = countVars solcons

    fold ::
      SolvedSystem Q ->
      Var ->
      SamplingM (SolvedSystem Q)
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
              $ V.concat
                [ -- coeffs from solsys
                  fmap (Exp.! j) <$> solsys,
                  -- coeffs from tcs
                  V.fromList (fmap (Exp.! j) . Cons.expFromTc <$> tcs solcons)
                ]
          -- compute lcm of denoms of coeffs
          a :: Q
          a = toQ $ foldr lcm (1 :: Int) dens
            where
              dens = fromInteger . denom <$> coeffs
      -- replace all appearances `aj*xj` with `0*xj + (a*aj)*x{j+n}`
      solsys <-
        pure $
          fmap
            ( \e ->
                let aj = e Exp.! j
                 in e Exp.// [(j, 0), (j + Var n, a * aj)]
            )
            <$> solsys
      -- include new equation `a{j+1} = a*xj`
      solsys <-
        pure $
          solsys
            // [(j + Var n, Just $ Exp.fromConstant (n + n) 0 Exp.// [(j, a)])]
      --
      pure solsys

    -- preserves number of vars
    cast_ExpQ_ExpNat' :: Exp Q -> SamplingM (Exp Nat')
    cast_ExpQ_ExpNat' e = mapM cast_Q_Nat' e

    cast_Q_Nat' :: Q -> SamplingM Nat'
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
