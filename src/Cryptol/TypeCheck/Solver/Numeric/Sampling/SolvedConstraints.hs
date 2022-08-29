{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Q
import Cryptol.TypeCheck.Type (TParam)
import Cryptol.Utils.PP (pp, ppList)
import Data.Bifunctor (Bifunctor (first))
import Data.Vector (Vector)
import qualified Data.Vector as V

-- | SolvedConstraints
data SolvedConstraints a = SolvedConstraints
  { solsys :: SolvedSystem a,
    tcs :: [Tc a],
    tparams :: Vector TParam,
    nVars :: Int,
    depOrder :: Vector Var
  }

instance Show a => Show (SolvedConstraints a) where
  show SolvedConstraints {..} =
    unlines
      [ "SolvedConstraints:",
        "  solsys:\n"
          ++ (unlines . V.toList)
            ( fmap
                ( ("    " ++)
                    . (\(i, s) -> "x{" ++ show i ++ "} = " ++ s)
                )
                . V.zip (V.generate nVars id)
                . fmap (maybe "free" show)
                $ solsys
            ),
        "  tcs:     " ++ show tcs,
        "  tparams: " ++ show (ppList (V.toList (pp <$> tparams))),
        "  nVars:  " ++ show nVars
      ]

toSolvedConstraints :: (Num a, Eq a) => Constraints a -> SamplingM (SolvedConstraints a)
toSolvedConstraints cons@Cons.Constraints {..} = do
  solsys <- toSolvedSystem nVars (Cons.sys cons)
  pure
    SolvedConstraints
      { solsys = solsys,
        tcs = tcs,
        tparams = tparams,
        nVars = nVars,
        depOrder = inferDepOrd solsys
      }

-- |
-- Infers the dependency order on a system of solved equations. For example,
-- consider the following system of equations over the variables @<x,y,z,w>@.
-- @
--   x = z + 1
--   y = z + 2
--   w = x + 4
-- @
-- Then the dependency order is
-- @
--   z -> y -> x -> w
-- @
-- since @z@ determined @y@ and @x@, and @x@ determines @w@. Since @x@ doesn't
-- depend on @y@ and visa versa, and permutation of @x@ and @y@ is a valid
-- dependency order. This result is encoded by the vector
-- @
--   <z,y,x,w>
-- @
inferDepOrd :: forall a. (Eq a, Num a) => SolvedSystem a -> Vector Var
inferDepOrd solsys = go deps V.empty
  where
    go :: Vector (Vector Var) -> Vector Var -> Vector Var
    go deps depOrd =
      -- collect vars that depend only on `depOrd`
      -- partition vars by whether they depend only on `depOrd`
      let vs = Var <$> V.findIndices (`depOnly` depOrd) deps
       in if V.null deps
            then if V.null vs then error "impossible" else depOrd
            else go (removeVarDeps vs deps) (depOrd <> vs)

    deps :: Vector (Vector Var)
    deps = maybe V.empty inferDeps <$> solsys

    -- whether `xs` depends only on `ys`
    depOnly :: Vector Var -> Vector Var -> Bool
    depOnly xs ys = all (`elem` ys) xs

    inferDeps :: Exp a -> Vector Var
    inferDeps (Exp as _) = Var <$> V.findIndices (0 /=) as

    removeVarDeps :: Vector Var -> Vector (Vector Var) -> Vector (Vector Var)
    removeVarDeps is deps =
      fst $
        V.partitionWith
          (\(i, deps) -> if i `elem` is then Left deps else Right ())
          (V.zipWith (,) (V.generate (V.length deps) Var) deps)

freshFreeVar :: Num a => SolvedConstraints a -> (SolvedConstraints a, Var)
freshFreeVar cons@SolvedConstraints {..} =
  ( cons
      { solsys = V.snoc (extendN (nVars + 1) solsys) Nothing,
        nVars = nVars + 1
      },
    Var nVars
  )

setEquation :: SolvedConstraints a -> Var -> Maybe (Exp a) -> SolvedConstraints a
setEquation solcons i mb_e = solcons {solsys = solsys solcons // [(i, mb_e)]}

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
-- invalid form, then throws error.
toSolvedSystem :: forall a. (Num a, Eq a) => Int -> System a -> SamplingM (SolvedSystem a)
toSolvedSystem nVars sys = do
  if null sys
    then pure $ V.fromList []
    else foldM fold (V.replicate nVars Nothing) sys
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
        -- _                ==> error (invalid form)
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

-- | SolvedSystem n -> SolvedSystem (n + m)
extendN :: Num a => Int -> SolvedSystem a -> SolvedSystem a
extendN m sys = fmap (Exp.extendN m) <$> sys

{-
{ x free
, y = x + 3
, z = y/2 }

~~>

{ x' free
, x = 2x'
, y' = x' + 3/2
, y = 2y'
, z = y' }
-}

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
  -- elim dens
  solcons <- foldM fold solcons (Var <$> [0 .. nVars solcons - 1])
  -- cast to Nat'
  solcons <- do
    solsys <- mapM (maybe (pure Nothing) (fmap pure . cast_ExpQ_ExpNat')) (solsys solcons)
    tcs <- Cons.overTcExpM cast_ExpQ_ExpNat' `traverse` tcs solcons
    -- mapM (Cons.overTcExp cast_ExpQ_ExpNat') (tcs solcons)
    pure solcons {solsys = solsys, tcs = tcs}
  pure solcons
  where
    fold ::
      SolvedConstraints Q ->
      Var ->
      SamplingM (SolvedConstraints Q)
    fold solcons j = do
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
                  fmap (Exp.! j) <$> solsys solcons,
                  -- coeffs from tcs
                  V.fromList (fmap (Exp.! j) . Cons.expFromTc <$> tcs solcons)
                ]
          -- compute lcm of denoms of coeffs
          a :: Q
          a = toQ $ foldr lcm (1 :: Int) dens
            where
              dens = fromInteger . denom <$> coeffs

      solcons <-
        if a /= 1
          then do
            -- intro fresh free var `xk`
            (solcons, k) <- pure $ freshFreeVar solcons
            debug' 1 $ "in order to elim den of " ++ show j ++ ", intro fresh var " ++ show k

            -- set equ `xk = ...`
            solcons <- case solsys solcons ! j of
              Nothing -> do
                -- set equ `xk = free` if we had `xj = free`
                pure solcons
              Just e -> do
                -- set equ `xk = e/a` if we had `xj = e`
                pure $ setEquation solcons k (Just $ (/ a) <$> e)

            -- set equ `xj = a*xk`
            solcons <- pure $ setEquation solcons j (Just $ Exp.single (nVars solcons) a k)

            -- substitute appearances of `b*xj` with `(a*b)xk`
            solcons <- do
              let subst e =
                    if b /= 0
                      then e Exp.// [(j, 0), (k, a * b)]
                      else e
                    where
                      b = e Exp.! j
              pure
                solcons
                  { solsys = fmap subst <$> solsys solcons,
                    tcs = Cons.overTcExp subst <$> tcs solcons
                  }

            --
            pure solcons
          else pure solcons

      --
      pure solcons

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
