{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BlockArguments #-}

-- infers instances such as KnownNat n => KnownNat (n + n)
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Cryptol.TypeCheck.Solver.Numeric.Sampling.System where

import Control.Monad
import GHC.Real
import Data.Maybe
import qualified Data.List as L
import Data.Proxy
import GHC.TypeNats
import qualified Data.Vector.Sized as V
import Data.Finite

import qualified Cryptol.TypeCheck.Solver.Numeric.Sampling.Exp as Exp
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Exp (Exp(..), Var)
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Base
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Q
import Cryptol.TypeCheck.Solver.InfNat (Nat')
import qualified Cryptol.TypeCheck.Solver.InfNat as Nat'

-- | System
-- A system of linear equations over domain `a`
-- The expression `a1*x1 + ... + aN*xN + c` encodes the equation
-- `a1*x1 + ... + aN*aN = c`.
type System (n :: Nat) a = [Exp n a]

countSystemVars :: KnownNat n => System n a -> Int
countSystemVars [Exp as _] = V.length as
countSystemVars _ = error "nVars []"

countSystemEqus :: System n a -> Int
countSystemEqus = Prelude.length

isSolvable :: System n a -> Bool
isSolvable = undefined

extend :: Num a => System n a -> System (n + 1) a
extend sys = Exp.extend <$> sys

extendN :: (Num a, KnownNat m) => System n a -> System (n + m) a
extendN sys = Exp.extendN <$> sys

-- | Solve system of equations via gaussian elimination and denomenator 
-- elimination. The resulting system has the form
-- ```
--    1*x0 + a11*x1 + a12*x2 + ... + a1N*xN = c1
--    0*x0 +   1*x1 + a22*x2 + ... + a2N*xN = c2
--    ...
-- ```
-- where all coefficients are integral.
-- TODO: do I even want this? or just use elimGauss and elimDens manually
solveSystem :: KnownNat n => System n Q -> SamplingM (System (n + n) Nat')
solveSystem = elimGauss >=> elimDens

elimGauss :: forall n. KnownNat n => System n Q -> SamplingM (System n Q)
elimGauss sys = do
  sys <- go sys 0
  if isSolvable sys 
    then pure sys 
    else noSampling
  where
    nVars = countSystemVars sys
    nEqus = countSystemEqus sys

    go :: System n Q -> Var n -> SamplingM (System n Q)
    go sys j | L.null sys || fromEnum j > min (nVars - 1) (nEqus - 1) = pure sys
    go sys j = do
      -- find an index of an equ that has j leadings 0s
      -- case L.findIndex ((Just (fromEnum j) ==) . countLeadingZeros) sys of
      case findSolvedEqu j sys of
        Just i -> do
          let e = sys !! i
          let aj = Exp.coefficient j e
          -- remove equ i from system
          sys <- pure $ L.delete e sys
          -- solve for var j by div by coeff j
          e <- pure $ fmap (/ aj) e
          -- eliminate var j from rest of sys by sub appropriate multiple of e
          sys <- pure $ 
            (\e' -> let aj' = Exp.coefficient j e' in
                      e' - (((aj'/aj) *) <$> e))
            <$> sys
          -- solve rest of sys without equ i, then re-append equ i
          (e :) <$> goNext sys j
        Nothing -> do
          -- skip solving for var j
          goNext sys j
    
    goNext :: KnownNat n => System n Q -> Var n -> SamplingM (System n Q)
    goNext sys j = case packFinite (fromIntegral $ fromEnum j + 1) of
      -- if there are vars left to solve for, recurse
      Just j' -> go sys j'
      -- otherwise done
      Nothing -> pure sys

elimDens :: forall n. KnownNat n => System n Q -> SamplingM (System (n + n) Nat')
elimDens sys =
  mapM cast_ExpQ_ExpNat' =<< 
  foldM fold (extendN sys) finites
  where
    -- `j` ranges from `0` to `n - 1`
    fold :: System (n + n) Q -> Finite n -> SamplingM (System (n + n) Q)
    fold sys j = do
      let
        j' :: Finite (n + n)
        j' = weakenProxy Proxy j

      -- check if `xj` has been solved for
      case findSolvedEqu j sys of
        Just _ ->
          -- if `xj` has been solved for, skip
          pure sys
        Nothing -> do
          -- otherwise, `xj` may appear with non-[1,0] coefficients, so lets process it
          let 
            -- collect coeffs of j in all rows (excluding 0, 1 coeffs)
            coeffs :: [Q]
            coeffs = Exp.coefficient j' <$> sys

            -- denomenators of coeffs
            dens :: [Int]
            dens = fromInteger . denominator <$> coeffs

            -- compute lcm of denoms of coeffs
            jDenLcm :: Q
            jDenLcm = toRational $ foldr lcm 1 dens
          
          -- replace all appearances `aj*xj` with `0*xj + (aj*jDenLcm)*x{j+1}`
          sys <- pure $ (\e -> e Exp.// [(j', 0), (j' + 1, Exp.coefficient j' e * jDenLcm)]) <$> sys
          
          -- add new equation `1*xj - jDenLcm*x{j+1} = 0` i.e `xj = jDenLcm*x{j+1}`
          pure $ (Exp.fromConstant 0 Exp.// [(j', 1), (j' + 1, -jDenLcm)]) : sys

    cast_ExpQ_ExpNat' :: Exp (n + n) Q -> SamplingM (Exp (n + n) Nat')
    cast_ExpQ_ExpNat' e = mapM cast_Q_Nat' e

    cast_Q_Nat' :: Q -> SamplingM Nat'
    cast_Q_Nat' q = case fromQ q of
      Just n -> pure . Nat'.Nat $ n
      Nothing -> throwSamplingError (SamplingError "elimDens" "After eliminating denomenators, there are still some nonintegral values left in equations.")

{-
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

countLeadingZeros :: Exp n Q -> Maybe Int
countLeadingZeros (Exp as _) = L.elemIndex 0 (V.toList as)

-- finds the index of the first equation that has j leading zeros
findSolvedEqu :: KnownNat n => Var n -> System m Q -> Maybe Int
findSolvedEqu j sys = L.findIndex isJust (fmap (fromEnum j ==) . countLeadingZeros <$> sys)
