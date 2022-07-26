{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Cryptol.TypeCheck.Solver.Numeric.Sampling.System where

import Control.Monad
import Cryptol.TypeCheck.Solver.InfNat (Nat')
import qualified Cryptol.TypeCheck.Solver.InfNat as Nat'
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Base
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Exp (Exp (..), Var(..))
import qualified Cryptol.TypeCheck.Solver.Numeric.Sampling.Exp as Exp
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Q
import Data.Bifunctor (Bifunctor (bimap, second))
import qualified Data.List as L
import Data.Maybe
import qualified Data.Vector as V
import GHC.Real

-- | System
-- A system of linear equations over domain `a`
-- The expression `a1*x1 + ... + aN*xN + c` encodes the equation
-- `a1*x1 + ... + aN*aN = c`.
type System a = [Exp a]

-- | IxEqu
-- Index of an equation in the system.
newtype IxEqu = IxEqu {unIxEqu :: Int}
  deriving (Eq, Ord, Num)

getEqu :: IxEqu -> System a -> Exp a
getEqu i sys = sys !! unIxEqu i

countVars :: System a -> Int
countVars sys = case L.uncons sys of
  Just (e, _) -> Exp.countVars e
  Nothing -> error "countVars mempty"

countEqus :: System a -> Int
countEqus = Prelude.length

isSolvable :: System a -> Bool
isSolvable = undefined

-- extend :: Exp n -> Exp (n + 1)
extend :: (Functor f, Num a) => f (Exp a) -> f (Exp a)
extend sys = Exp.extend <$> sys

-- extendN :: Exp n -> Exp (n + m)
extendN :: (Functor f, Num a) => Int -> f (Exp a) -> f (Exp a)
extendN m sys = Exp.extendN m <$> sys

-- | Solve system of equations via gaussian elimination and denomenator
-- elimination. The resulting system has the form
-- ```
--    1*x0 + a11*x1 + a12*x2 + ... + a1N*xN = c1
--    0*x0 +   1*x1 + a22*x2 + ... + a2N*xN = c2
--    ...
-- ```
-- where the coefficients are not necessarily integral (this will be handled in
-- the elimDens function.). The resulting system is a `SolvedSystem`, but you
-- will have to embed it yourself.
-- 
-- solveGauss :: System n -> System n
solveGauss :: forall m. Monad m => System Q -> SamplingM m (System Q)
solveGauss sys = go 0 sys
  where
    go :: Var -> System Q -> SamplingM m (System Q)
    go _ [] = pure sys
    go j sys = do
      case extractSolvedEq j sys of
        -- e is removed from sys
        Just (e, sys) -> do
          -- divide e by coeff of var j to make coeff of var j be 1
          let aj = e Exp.! j
          e <- pure $ (/ aj) <$> e
          -- eliminate var j from rest of sys by sub appropriate multiple of e
          sys <-
            pure $
              ( \e' ->
                  let aj' = e' Exp.! j
                   in e' - (((aj' / aj) *) <$> e)
              )
                <$> sys
          -- solve rest of sys without e, then re-append e
          (e :) <$> go (j + 1) sys
        Nothing ->
          -- skip solving for var j
          go (j + 1) sys

    extractSolvedEq :: (Num a, Eq a) => Var -> System a -> Maybe (Exp a, System a)
    extractSolvedEq j [] = Nothing
    extractSolvedEq j (e : sys) =
      if countLeadingZeros e == Just (Exp.unVar j)
        then -- doesn't add `e` back into the system
          Just (e, sys)
        else -- add back `e` into the system
          second (e :) <$> extractSolvedEq j sys

countLeadingZeros :: (Num a, Eq a) => Exp a -> Maybe Int
countLeadingZeros (Exp as _) = L.elemIndex 0 (V.toList as)
