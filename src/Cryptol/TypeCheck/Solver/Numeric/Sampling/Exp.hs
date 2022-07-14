{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module Cryptol.TypeCheck.Solver.Numeric.Sampling.Exp where

import GHC.TypeNats
import qualified Data.Vector.Sized as V
import Data.Proxy

import Data.Finite

-- | Exp
-- A linear polynomial over domain `a` with `n` variables.
data Exp (n :: Nat) a = Exp (V.Vector n a) a -- a1*x1 + ... + aN*xN + c
  deriving (Show, Eq, Functor, Foldable, Traversable)
type Var n = Finite n

instance Num a => Num (Exp n a) where
  Exp as1 c1 + Exp as2 c2 = Exp (V.zipWith (+) as1 as2) (c1 + c2)
  abs = fmap abs
  negate = fmap negate
  
  (*) = undefined
  signum = undefined
  fromInteger = undefined

fromConstant :: KnownNat n => Num a => a -> Exp n a
fromConstant = Exp (V.replicate 0)

extend :: Num a => Exp n a -> Exp (n + 1) a
extend (Exp as c) = Exp (V.snoc as 0) c

extendProxy :: (Num a, KnownNat m) => Proxy m -> Exp n a -> Exp (n + m) a
extendProxy _ (Exp as c) = Exp (as V.++ V.replicate 0) c

extendN :: (Num a, KnownNat m) => Exp n a -> Exp (n + m) a
extendN (Exp as c) = Exp (as V.++ V.replicate 0) c

coefficient :: Var n -> Exp n a -> a
coefficient i (Exp as _) = V.index as i

(//) :: Exp n a -> [(Finite n, a)] -> Exp n a
Exp as c // mods = Exp (as V.// mods) c