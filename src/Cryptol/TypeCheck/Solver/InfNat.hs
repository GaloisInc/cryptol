-- |
-- Module      :  Cryptol.TypeCheck.Solver.InfNat
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- This module defines natural numbers with an additional infinity
-- element, and various arithmetic operators on them.

{-# LANGUAGE Trustworthy #-}

{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
module Cryptol.TypeCheck.Solver.InfNat where

import Data.Bits
import Cryptol.Utils.Panic

import GHC.Generics (Generic)
import Control.DeepSeq

-- | Natural numbers with an infinity element
data Nat' = Nat Integer | Inf
            deriving (Eq, Ord, Generic, NFData)

instance Show Nat' where 
  show = \case
    Nat n -> show n
    Inf -> "inf"

fromNat :: Nat' -> Maybe Integer
fromNat n' =
  case n' of
    Nat i -> Just i
    _     -> Nothing

instance Num Nat' where
  (+) = nAdd
  (*) = nMul

  abs (Nat i) = Nat (abs i)
  abs Inf = Inf

  signum (Nat i) = Nat (signum i)
  signum Inf = Nat 1

  fromInteger = Nat

  l - m = case nSub l m of 
    Just n -> n
    Nothing -> panic "Nat.(-)" 
      ["Invalid arithmetic over `Nat'`: " ++ show l ++ " - " ++ show m]

--------------------------------------------------------------------------------


nAdd :: Nat' -> Nat' -> Nat'
nAdd Inf _           = Inf
nAdd _ Inf           = Inf
nAdd (Nat x) (Nat y) = Nat (x + y)

{-| Some algebraic properties of interest:

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


{-| Some algebraic properties of interest:

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


-- XXX:
-- Does it make sense to define:
--   nDiv Inf (Nat x)  = Inf
--   nMod Inf (Nat x)  = Nat 0

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

-- | @nCeilDiv msgLen blockSize@ computes the least @n@ such that
-- @msgLen <= blockSize * n@. It is undefined when @blockSize = 0@,
-- or when @blockSize = inf@. @inf@ divided by any positive
-- finite value is @inf@.
nCeilDiv :: Nat' -> Nat' -> Maybe Nat'
nCeilDiv _       Inf      = Nothing
nCeilDiv _       (Nat 0)  = Nothing
nCeilDiv Inf     (Nat _)  = Just Inf
nCeilDiv (Nat x) (Nat y)  = Just (Nat (- div (- x) y))

-- | @nCeilMod msgLen blockSize@ computes the least @k@ such that
-- @blockSize@ divides @msgLen + k@. It is undefined when @blockSize = 0@
-- or @blockSize = inf@.  @inf@ modulus any positive finite value is @0@.
nCeilMod :: Nat' -> Nat' -> Maybe Nat'
nCeilMod _       Inf      = Nothing
nCeilMod _       (Nat 0)  = Nothing
nCeilMod Inf     (Nat _)  = Just (Nat 0)
nCeilMod (Nat x) (Nat y)  = Just (Nat (mod (- x) y))

-- | Rounds up.
-- @lg2 x = y@, iff @y@ is the smallest number such that @x <= 2 ^ y@
nLg2 :: Nat' -> Nat'
nLg2 Inf      = Inf
nLg2 (Nat 0)  = Nat 0
nLg2 (Nat n)  = case genLog n 2 of
                  Just (x,exact) | exact     -> Nat x
                                 | otherwise -> Nat (x + 1)
                  Nothing -> panic "Cryptol.TypeCheck.Solver.InfNat.nLg2"
                               [ "genLog returned Nothing" ]

-- | @nWidth n@ is number of bits needed to represent all numbers
-- from 0 to n, inclusive. @nWidth x = nLg2 (x + 1)@.
nWidth :: Nat' -> Nat'
nWidth Inf      = Inf
nWidth (Nat n)  = Nat (widthInteger n)



-- | @length [ x, y .. z ]@
nLenFromThenTo :: Nat' -> Nat' -> Nat' -> Maybe Nat'
nLenFromThenTo (Nat x) (Nat y) (Nat z)
  | step /= 0 = let len = div dist step + 1
                in Just $ Nat $ if x > y
                                  -- decreasing
                                  then (if z > x then 0 else len)
                                  -- increasing
                                  else (if z < x then 0 else len)
  where
  step = abs (x - y)
  dist = abs (x - z)

nLenFromThenTo _ _ _ = Nothing

{- Note [Sequences of Length 0]

  nLenFromThenTo x y z == 0
    case 1: x > y  && z > x
    case 2: x <= y && z < x
-}

{- Note [Sequences of Length 1]

  `nLenFromThenTo x y z == 1`

  dist < step && (x > y && z <= x   ||   y >= x && z >= x)

  case 1: dist < step && x > y && z <= x
  case 2: dist < step && y >= x && z >= x

  case 1: if    `z <= x`,
          then  `x - z >= 0`,
          hence `dist = x - z`    (a)

          if    `x > y`
          then  `x - y` > 0
          hence `step = x - y`    (b)

          from (a) and (b):
            `dist < step`
            `x - z < x - y`
            `-z < -y`
            `z > y`

  case 1 summary:  x >= z && z > y



  case 2: if y >= x, then step = y - x   (a)
          if z >= x, then dist = z - x   (b)

          dist < step =
          (z - x) < (y - x) =
          (z < y)

  case 2 summary: y > z, z >= x

-}


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


-- | Compute the number of bits required to represent the given integer.
widthInteger :: Integer -> Integer
widthInteger x = go' 0 (if x < 0 then complement x else x)
  where
    go s 0 = s
    go s n = let s' = s + 1 in s' `seq` go s' (n `shiftR` 1)

    go' s n
      | n < bit 32 = go s n
      | otherwise  = let s' = s + 32 in s' `seq` go' s' (n `shiftR` 32)


-- | Compute the exact root of a natural number.
-- The second argument specifies which root we are computing.
rootExact :: Integer -> Integer -> Maybe Integer
rootExact x y = do (z,True) <- genRoot x y
                   return z



{- | Compute the the n-th root of a natural number, rounded down to
the closest natural number.  The boolean indicates if the result
is exact (i.e., True means no rounding was done, False means rounded down).
The second argument specifies which root we are computing. -}
genRoot :: Integer -> Integer -> Maybe (Integer, Bool)
genRoot _  0    = Nothing
genRoot x0 1    = Just (x0, True)
genRoot x0 root = Just (search 0 (x0+1))
  where
  search from to = let x = from + div (to - from) 2
                       a = x ^ root
                   in case compare a x0 of
                        EQ              -> (x, True)
                        LT | x /= from  -> search x to
                           | otherwise  -> (from, False)
                        GT | x /= to    -> search from x
                           | otherwise  -> (from, False)




