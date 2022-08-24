{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RecordWildCards #-}

module Cryptol.TypeCheck.Solver.Numeric.Sampling.Exp where

import Data.Bifunctor (Bifunctor (first))
import qualified Data.List as L
import Data.Vector (Vector)
import qualified Data.Vector as V

-- | Exp
-- A linear polynomial over domain `a` with `n` variables.
data Exp a = Exp (Vector a) a -- a1*x1 + ... + aN*xN + c
  deriving (Eq, Functor, Foldable, Traversable)

instance Show a => Show (Exp a) where
  show (Exp as c) =
    L.intercalate " + " . V.toList $
      ( (\(i, a) -> show a ++ "*" ++ "x{" ++ show i ++ "}")
          <$> V.zip (V.generate (V.length as) id) as
      )
        <> pure (show c)

newtype Var = Var {unVar :: Int}
  deriving (Eq, Ord, Num)

instance Show Var where 
  show Var{..} = "x{" ++ show unVar ++ "}"

instance Num a => Num (Exp a) where
  Exp as1 c1 + Exp as2 c2 = Exp (V.zipWith (+) as1 as2) (c1 + c2)
  abs = fmap abs
  negate = fmap negate

  (*) = undefined
  signum = undefined
  fromInteger = undefined

countVars :: Exp a -> Int
countVars (Exp as _) = V.length as

fromConstant :: Num a => Int -> a -> Exp a
fromConstant n = Exp (V.replicate n 0)

single :: Num a => Int -> a -> Var -> Exp a
single n a i = fromConstant n 0 // [(i, a)]

-- ... + a*xi + ... => a*xi
extractTerm :: Num a => Var -> Exp a -> Exp a
extractTerm i e = single (countVars e) (e ! i) i

-- Exp a -> Exp (n + 1) a
extend :: Num a => Exp a -> Exp a
extend (Exp as c) = Exp (V.snoc as 0) c

-- Exp n a -> Exp (n + m) a
extendN :: Num a => Int -> Exp a -> Exp a
extendN m (Exp as c) = Exp (as <> V.replicate m 0) c

-- Exp n a -> Exp m a
pad :: Num a => Int -> Exp a -> Exp a
pad m e@(Exp as _)
  | n <- V.length as, n <= m = extendN (m - n) e
  | otherwise = error "tried to pad an `Exp` that is larger than the padding"

(!) :: Exp a -> Var -> a
Exp as _ ! i = as V.! unVar i

(//) :: Exp a -> [(Var, a)] -> Exp a
Exp as c // mods = Exp (as V.// (first unVar <$> mods)) c

solveFor :: Num a => Var -> Exp a -> Exp a
solveFor i (Exp as c) =
  Exp
    ( (\(i', a) -> if i == i' then 0 else -a)
        <$> V.zip (V.generate (V.length as) Var) as
    )
    c
