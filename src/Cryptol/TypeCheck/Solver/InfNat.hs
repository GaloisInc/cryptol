-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- This module defines natural numbers with an additional infinity
-- element, and various arithmetic operators on them.

{-# LANGUAGE Safe #-}
module Cryptol.TypeCheck.Solver.InfNat where

-- | Natural numbers with an infinity element
data Nat' = Nat Integer | Inf
            deriving (Show,Eq,Ord)

fromNat :: Nat' -> Maybe Integer
fromNat n' =
  case n' of
    Nat i -> Just i
    _     -> Nothing

nAdd :: Nat' -> Nat' -> Nat'
nAdd Inf _           = Inf
nAdd _ Inf           = Inf
nAdd (Nat x) (Nat y) = Nat (x + y)

{-| Some algerbaic properties of interest:

> 1 * x = x
> x * (y * z) = (x * y) * z
> 0 * x = 0
> x * y = y * x
> x * (a + b) = x * a + x * b

-}
nMul :: Nat' -> Nat' -> Nat'
nMul (Nat 0) _       = Nat 0
nMul _ (Nat 0)       = Nat 0
nMul Inf _           = Inf
nMul _ Inf           = Inf
nMul (Nat x) (Nat y) = Nat (x * y)


{-| Some algeibraic properties of interest:

> x ^ 0        = 1
> x ^ (n + 1)  = x * (x ^ n)
> x ^ (m + n)  = (x ^ m) * (x ^ n)
> x ^ (m * n)  = (x ^ m) ^ n

-}
nExp :: Nat' -> Nat' -> Nat'
nExp _ (Nat 0)       = Nat 1
nExp Inf _           = Inf
nExp (Nat 0) Inf     = Nat 0
nExp (Nat 1) Inf     = Nat 1
nExp (Nat _) Inf     = Inf
nExp (Nat x) (Nat y) = Nat (x ^ y)

nMin :: Nat' -> Nat' -> Nat'
nMin Inf x            = x
nMin x Inf            = x
nMin (Nat x) (Nat y)  = Nat (min x y)

nMax :: Nat' -> Nat' -> Nat'
nMax Inf _            = Inf
nMax _ Inf            = Inf
nMax (Nat x) (Nat y)  = Nat (max x y)

{- | @nSub x y = Just z@ iff @z@ is the unique value
such that @Add y z = Just x@.  -}
nSub :: Nat' -> Nat' -> Maybe Nat'
nSub Inf (Nat _)              = Just Inf
nSub (Nat x) (Nat y)
  | x >= y                    = Just (Nat (x - y))
nSub _ _                      = Nothing


{- | Rounds down.

> y * q + r = x
> x / y     = q with remainder r
> 0 <= r && r < y

We don't allow `Inf` in the first argument for two reasons:
  1. It matches the behavior of `nMod`,
  2. The well-formedness constraints can be expressed as a conjunction.
-}
nDiv :: Nat' -> Nat' -> Maybe Nat'
nDiv _       (Nat 0)  = Nothing
nDiv Inf _            = Nothing
nDiv (Nat x) (Nat y)  = Just (Nat (div x y))
nDiv (Nat _) Inf      = Just (Nat 0)

nMod :: Nat' -> Nat' -> Maybe Nat'
nMod _       (Nat 0)  = Nothing
nMod Inf     _        = Nothing
nMod (Nat x) (Nat y)  = Just (Nat (mod x y))
nMod (Nat x) Inf      = Just (Nat x)          -- inf * 0 + x = 0 + x

-- | Rounds up.
-- @lg2 x = y@, iff @y@ is the smallest number such that @x <= 2 ^ y@
nLg2 :: Nat' -> Nat'
nLg2 Inf      = Inf
nLg2 (Nat 0)  = Nat 0
nLg2 (Nat n)  = case genLog n 2 of
                  Just (x,exact) | exact     -> Nat x
                                 | otherwise -> Nat (x + 1)
                  Nothing -> error "genLog returned Nothing"

-- | @nWidth n@ is number of bits needed to represent all numbers
-- from 0 to n, inclusive. @nWidth x = nLg2 (x + 1)@.
nWidth :: Nat' -> Nat'
nWidth Inf      = Inf
nWidth (Nat 0)  = Nat 0
nWidth (Nat n)  = case genLog n 2 of
                    Just (x,_) -> Nat (x + 1)
                    Nothing -> error "genLog returned Nothing"


nLenFromThen :: Nat' -> Nat' -> Nat' -> Maybe Nat'
nLenFromThen a@(Nat x) b@(Nat y) (Nat w)
  | y > x = nLenFromThenTo a b (Nat (2^w - 1))
  | y < x = nLenFromThenTo a b (Nat 0)

nLenFromThen _ _ _ = Nothing

nLenFromThenTo :: Nat' -> Nat' -> Nat' -> Maybe Nat'
nLenFromThenTo (Nat x) (Nat y) (Nat z)
  | step /= 0 = let len   = div dist step + 1
                in Just $ Nat $ max 0 (if x > y then if z > x then 0 else len
                                         else if z < x then 0 else len)
  where
  step = abs (x - y)
  dist = abs (x - z)

nLenFromThenTo _ _ _ = Nothing


--------------------------------------------------------------------------------

-- | Compute the logarithm of a number in the given base, rounded down to the
-- closest integer.  The boolean indicates if we the result is exact
-- (i.e., True means no rounding happened, False means we rounded down).
-- The logarithm base is the second argument.
genLog :: Integer -> Integer -> Maybe (Integer, Bool)
genLog x 0    = if x == 1 then Just (0, True) else Nothing
genLog _ 1    = Nothing
genLog 0 _    = Nothing
genLog x base = Just (exactLoop 0 x)
  where
  exactLoop s i
    | i == 1     = (s,True)
    | i < base   = (s,False)
    | otherwise  =
        let s1 = s + 1
        in s1 `seq` case divMod i base of
                      (j,r)
                        | r == 0    -> exactLoop s1 j
                        | otherwise -> (underLoop s1 j, False)

  underLoop s i
    | i < base  = s
    | otherwise = let s1 = s + 1 in s1 `seq` underLoop s1 (div i base)



