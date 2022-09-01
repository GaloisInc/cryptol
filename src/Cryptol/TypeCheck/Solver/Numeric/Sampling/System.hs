{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Cryptol.TypeCheck.Solver.Numeric.Sampling.System where

import Cryptol.TypeCheck.Solver.Numeric.Sampling.Base
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Constraints (Equ, System)
import qualified Cryptol.TypeCheck.Solver.Numeric.Sampling.Constraints as Cons
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Exp (Exp (..), Var (..))
import qualified Cryptol.TypeCheck.Solver.Numeric.Sampling.Exp as Exp
import Data.Bifunctor (Bifunctor (second))
import qualified Data.Vector as V

-- | IxEqu
-- Index of an equation in the system.
newtype IxEqu = IxEqu {unIxEqu :: Int}
  deriving (Eq, Ord, Num)

getEqu :: IxEqu -> System a -> Equ a
getEqu i sys = sys !! unIxEqu i

countEqus :: System a -> Int
countEqus = Prelude.length

-- A system is solvable if every equation with a 0 constant also has 0
-- coefficients for all variables
isSolvable :: (Eq a, Num a) => System a -> Bool
isSolvable = all (\(Cons.Equ (Exp as c)) -> c /= 0 || all (0 ==) as)

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
solveGauss :: Int -> System Rational -> SamplingM (System Rational)
solveGauss nVars sys = go 0 sys
  where
    go :: Var -> System Rational -> SamplingM (System Rational)
    go (Var j) sys | j >= nVars || null sys = pure sys
    go j sys = do
      debug' 1 $ "j   = " ++ show j
      debug' 1 $ "sys = " ++ show sys
      case extractSolvedEqu j sys of
        -- eq is removed from sys
        Just (eq, sys') -> do
          debug' 1 $ "extractSolvedEqu (" ++ show j ++ ") sys = Just (" ++ show eq ++ ", " ++ show sys' ++ ")"
          -- divide e by coeff of var j to make coeff of var j be 1
          let aj = Cons.asExp (Exp.! j) eq
          eq <- pure $ (/ aj) <$> eq
          -- eliminate var j from rest of sys by sub appropriate multiple of e
          sys' <-
            pure $
              ( Cons.overExp \e' ->
                  flip Cons.asExp eq \e ->
                    let aj' = e' Exp.! j
                     in e' `Exp.sub` ((aj' *) <$> e)
              )
                <$> sys'
          --
          -- solve rest of sys' for var `j + 1`
          go (j + 1) (eq : sys')
        Nothing -> do
          debug' 1 $ "could not extract equation for `j = " ++ show j ++ "`"
          -- skip solving for var j
          go (j + 1) sys

    extractSolvedEqu :: (Num a, Eq a) => Var -> System a -> Maybe (Equ a, System a)
    extractSolvedEqu _j [] = Nothing
    extractSolvedEqu j (e : sys) =
      if Cons.asExp countLeadingZeros e == Just (Exp.unVar j)
        then -- doesn't add `e` back into the system
          Just (e, sys)
        else -- add back `e` into the system
          second (e :) <$> extractSolvedEqu j sys

countLeadingZeros :: (Num a, Eq a) => Exp a -> Maybe Int
countLeadingZeros (Exp as _) = V.findIndex (0 /=) as
