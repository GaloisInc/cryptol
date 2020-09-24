-----------------------------------------------------------------------------
-- |
-- Module    : Cryptol.PrimeEC
-- Copyright : (c) Galois, Inc.
-- License   : BSD3
-- Maintainer: rdockins@galois.com
-- Stability : experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Cryptol.PrimeEC
  ( PrimeModulus
  , primeModulus
  , ProjectivePoint(..)
  , integerToBigNat
  , Integer.bigNatToInteger

  , ec_double
  , ec_add
  , ec_mult
  , ec_twin_mult
  ) where


import           GHC.Integer.GMP.Internals (BigNat)
import qualified GHC.Integer.GMP.Internals as Integer
import GHC.Prim

import Data.Bits
import Data.List (foldl')

import Cryptol.TypeCheck.Solver.InfNat (widthInteger)
import Cryptol.Utils.Panic

data ProjectivePoint =
  ProjectivePoint
  { px :: !BigNat
  , py :: !BigNat
  , pz :: !BigNat
  }

zro :: ProjectivePoint
zro = ProjectivePoint Integer.oneBigNat Integer.oneBigNat Integer.zeroBigNat

integerToBigNat :: Integer -> BigNat
integerToBigNat (Integer.S# i)  = Integer.wordToBigNat (int2Word# i)
integerToBigNat (Integer.Jp# b) = b
integerToBigNat (Integer.Jn# b) = b

newtype PrimeModulus = PrimeModulus { primeMod :: BigNat }

{-# INLINE primeModulus #-}
primeModulus :: Integer -> PrimeModulus
primeModulus = PrimeModulus . integerToBigNat

-- Barrett reduction replaces a division by the modulus with
-- two multiplications and some shifting, masking, and additions
-- (and some fairly negligable pre-processing). For the size of
-- moduli we are working with for ECC, this does not appear to be
-- a performance win.  Even for largest NIST curve (P-521) Barrett
-- reduction is about 20% slower than naive modular reduction.
-- Smaller curves are worse WRT the baseline.

-- {-# INLINE primeModulus #-}
-- primeModulus :: Integer -> PrimeModulus
-- primeModulus = untrie modulusParameters

-- data PrimeModulus = PrimeModulus
--   { primeMod :: !Integer
--   , barrettInverse :: !Integer
--   , barrettK       :: !Int
--   , barrettMask    :: !Integer
--   }
--  deriving (Show, Eq)

-- {-# NOINLINE modulusParameters #-}
-- modulusParameters :: Integer :->: PrimeModulus
-- modulusParameters = trie computeModulusParameters

-- computeModulusParameters :: Integer -> PrimeModulus
-- computeModulusParameters p = PrimeModulus p inv k mask
--   where
--   k = fromInteger w

--   b :: Integer
--   b = 2 ^ (64::Int)

--   -- w is the number of 64-bit words required to express p
--   w = (widthInteger p + 63) `div` 64

--   mask = b^(k+1) - 1

--   -- inv = floor ( b^(2*k) / p )
--   inv = b^(2*k) `div` p

-- barrettReduction :: PrimeModulus -> Integer -> Integer
-- barrettReduction p x = go r3
--   where
--     m    = primeMod p
--     k    = barrettK p
--     inv  = barrettInverse p
--     mask = barrettMask p

--     -- q1 <- floor (x / b^(k-1))
--     q1 = x `shiftR` (64 * (k-1))

--     -- q2 <- q1 * floor ( b^(2*k) / m )
--     q2 = q1 * inv

--     -- q3 <- floor (q2 / b^(k+1))
--     q3 = q2 `shiftR` (64 * (k+1))

--     -- r1 <- x mod b^(k+1)
--     r1 = x .&. mask

--     -- r2 <- (q3 * m) mod b^(k+1)
--     r2 = (q3 * m) .&. mask

--     -- r3 <- r1 - r2
--     r3 = r1 - r2

--     -- up to 2 multiples of m must be removed
--     go z = if z > m then go (z - m) else z

mod_add :: PrimeModulus -> BigNat -> BigNat -> BigNat
mod_add p !x !y =
    case Integer.isNullBigNat# rmp of
      0# -> rmp
      _  -> r
  where r = Integer.plusBigNat x y
        rmp = Integer.minusBigNat r (primeMod p)

mod_half :: PrimeModulus -> BigNat -> BigNat
mod_half p x = if Integer.testBitBigNat x 0# then qodd else qeven
  where
  qodd  = (Integer.plusBigNat x (primeMod p)) `Integer.shiftRBigNat` 1#
  qeven = x `Integer.shiftRBigNat` 1#

mod_mul :: PrimeModulus -> BigNat -> BigNat -> BigNat
mod_mul p !x !y = (Integer.timesBigNat x y) `Integer.remBigNat` (primeMod p)

mod_sub :: PrimeModulus -> BigNat -> BigNat -> BigNat
mod_sub p !x !y = mod_add p x (Integer.minusBigNat (primeMod p) y)

mod_square :: PrimeModulus -> BigNat -> BigNat
mod_square p !x = Integer.sqrBigNat x `Integer.remBigNat` primeMod p

mul2 :: PrimeModulus -> BigNat -> BigNat
mul2 p !x =
    case Integer.isNullBigNat# rmp of
      0# -> rmp
      _  -> r
 where
   r = x `Integer.shiftLBigNat` 1#
   rmp = Integer.minusBigNat r (primeMod p)

mul3 :: PrimeModulus -> BigNat -> BigNat
mul3 p x = mod_add p x $! mul2 p x

mul4 :: PrimeModulus -> BigNat -> BigNat
mul4 p x = mul2 p $! mul2 p x

mul8 :: PrimeModulus -> BigNat -> BigNat
mul8 p x = mul2 p $! mul4 p x

ec_double :: PrimeModulus -> ProjectivePoint -> ProjectivePoint
ec_double p (ProjectivePoint sx sy sz) =
    if Integer.isZeroBigNat sz then zro else ProjectivePoint r18 r23 r13

  where
  r7  = mod_square p sz                   {-  7: t4 <- (t3)^2  -}
  r8  = mod_sub    p sx r7                {-  8: t5 <- t1 - t4 -}
  r9  = mod_add    p sx r7                {-  9: t4 <- t1 + t4 -}
  r10 = mod_mul    p r9 r8                {- 10: t5 <- t4 * t5 -}
  r11 = mul3       p r10                  {- 11: t4 <- 3 * t5 -}
  r12 = mod_mul    p sz sy                {- 12: t3 <- t3 * t2 -}
  r13 = mul2       p r12                  {- 13: t3 <- 2 * t3 -}
  r14 = mod_square p sy                   {- 14: t2 <- (t2)^2 -}
  r15 = mod_mul    p sx r14               {- 15: t5 <- t1 * t2 -}
  r16 = mul4       p r15                  {- 16: t5 <- 4 * t5 -}
  r17 = mod_square p r11                  {- 17: t1 <- (t4)^2 -}
  r18 = mod_sub    p r17 (mul2 p r16)     {- 18: t1 <- t1 - 2 * t5 -}
  r19 = mod_square p r14                  {- 19: t2 <- (t2)^2 -}
  r20 = mul8       p r19                  {- 20: t2 <- 8 * t2 -}
  r21 = mod_sub    p r16 r18              {- 21: t5 <- t5 - t1 -}
  r22 = mod_mul    p r11 r21              {- 22: t5 <- t4 * t5 -}
  r23 = mod_sub    p r22 r20              {- 23: t2 <- t5 - t2 -}

{-# INLINE ec_full_add #-}
ec_full_add :: PrimeModulus -> ProjectivePoint -> ProjectivePoint -> ProjectivePoint
ec_full_add p s t
  | Integer.isZeroBigNat (pz s) = t
  | Integer.isZeroBigNat (pz t) = s
  | otherwise = ec_add p s t

{-# INLINE ec_full_sub #-}
ec_full_sub :: PrimeModulus -> ProjectivePoint -> ProjectivePoint -> ProjectivePoint
ec_full_sub p s t = ec_full_add p s u
  where u = t{ py = Integer.minusBigNat (primeMod p) (py t) }

ec_add :: PrimeModulus -> ProjectivePoint -> ProjectivePoint -> ProjectivePoint
ec_add p s@(ProjectivePoint sx sy sz)
           (ProjectivePoint tx ty tz) =
    if Integer.isZeroBigNat r13 then
      if Integer.isZeroBigNat r14 then
        ec_double p s
      else
        zro
    else
      ProjectivePoint r32 r37 r27

  where
  tNormalized = Integer.eqBigNat tz Integer.oneBigNat

  tz2 = mod_square p tz
  tz3 = mod_mul p tz tz2

  r5  = if tNormalized then sx else mod_mul p sx tz2
  r7  = if tNormalized then sy else mod_mul p sy tz3

  r9  = mod_square p sz                  {-  9: t7 <- (t3)^2 -}
  r10 = mod_mul    p tx r9               {- 10: t4 <- t4 * t7 -}
  r11 = mod_mul    p sz r9               {- 11: t7 <- t3 * t7 -}
  r12 = mod_mul    p ty r11              {- 12: t5 <- t5 * t7 -}
  r13 = mod_sub    p r5 r10              {- 13: t4 <- t1 - t4 -}
  r14 = mod_sub    p r7 r12              {- 14: t5 <- t2 - t5 -}

  r22 = mod_sub    p (mul2 p r5) r13     {- 22: t1 <- 2*t1 - t4 -}
  r23 = mod_sub    p (mul2 p r7) r14     {- 23: t2 <- 2*t2 - t5 -}

  r25 = if tNormalized then sz else mod_mul p sz tz

  r27 = mod_mul    p r25 r13             {- 27: t3 <- t3 * t4 -}
  r28 = mod_square p r13                 {- 28: t7 <- (t4)^2 -}
  r29 = mod_mul    p r13 r28             {- 29: t4 <- t4 * t7 -}
  r30 = mod_mul    p r22 r28             {- 30: t7 <- t1 * t7 -}
  r31 = mod_square p r14                 {- 31: t1 <- (t5)^2 -}
  r32 = mod_sub    p r31 r30             {- 32: t1 <- t1 - t7 -}
  r33 = mod_sub    p r30 (mul2 p r32)    {- 33: t7 <- t7 - 2*t1 -}
  r34 = mod_mul    p r14 r33             {- 34: t5 <- t5 * t7 -}
  r35 = mod_mul    p r23 r29             {- 35: t4 <- t2 * t4 -}
  r36 = mod_sub    p r34 r35             {- 36: t2 <- t5 - t4 -}
  r37 = mod_half   p r36                 {- 37: t2 <- t2/2 -}


ec_normalize :: PrimeModulus -> ProjectivePoint -> ProjectivePoint
ec_normalize p s@(ProjectivePoint x y z)
  | Integer.eqBigNat z Integer.oneBigNat = s
  | otherwise = ProjectivePoint x' y' Integer.oneBigNat
 where
  m = primeMod p

  l  = Integer.recipModBigNat z m
  l2 = Integer.sqrBigNat l
  l3 = Integer.timesBigNat l l2

  x' = (Integer.timesBigNat x l2) `Integer.remBigNat` m
  y' = (Integer.timesBigNat y l3) `Integer.remBigNat` m

ec_mult :: PrimeModulus -> Integer -> ProjectivePoint -> ProjectivePoint
ec_mult p d s
  | d == 0    = zro
  | d == 1    = s
  | Integer.isZeroBigNat (pz s) = zro
  | otherwise = foldl' step zro (reverse [ 1 .. highbit ])

 where
   s' = ec_normalize p s
   h  = 3*d

   highbit
     | w <= toInteger (maxBound :: Int) = fromInteger w
     | otherwise = error "ec_mult: Integer width too large"
    where w = widthInteger h

   step r i
     | testBit h i && not (testBit d i) = ec_full_add p r2 s'
     | not (testBit h i) && testBit d i = ec_full_sub p r2 s'
     | otherwise = r2
    where
      r2 = ec_double p r


{-# INLINE normalizeForTwinMult #-}
normalizeForTwinMult ::
  PrimeModulus -> ProjectivePoint -> ProjectivePoint ->
  (ProjectivePoint, ProjectivePoint, ProjectivePoint, ProjectivePoint)
normalizeForTwinMult p s t = (s',t',spt',smt')
 where

  s' = ec_normalize p s
  t' = ec_normalize p t

  spt  = ec_full_add p s' t'
  spt' = ec_normalize p spt

  smt  = ec_full_sub p s' t'
  smt' = ec_normalize p smt


ec_twin_mult :: PrimeModulus ->
  Integer -> ProjectivePoint ->
  Integer -> ProjectivePoint ->
 ProjectivePoint
ec_twin_mult p (integerToBigNat -> d0) s (integerToBigNat -> d1) t =
   case m of
     0# -> panic "ec_twin_mult" ["modulus too large", show (Integer.bigNatToInteger (primeMod p))]
     _  -> go m init_c0 init_c1 zro

 where
  (s',t',spt',smt') = normalizeForTwinMult p s t

  m = case max 4 (widthInteger (Integer.bigNatToInteger (primeMod p))) of
        Integer.S# mint -> mint
        _ -> 0# -- if `m` doesn't fit into an Int, should be impossible

  init_c0 = C False False (tst d0 (m -# 1#)) (tst d0 (m -# 2#)) (tst d0 (m -# 3#)) (tst d0 (m -# 4#))
  init_c1 = C False False (tst d1 (m -# 1#)) (tst d1 (m -# 2#)) (tst d1 (m -# 3#)) (tst d1 (m -# 4#))

  tst x i
    | tagToEnum# (i >=# 0#) = Integer.testBitBigNat x i
    | otherwise = False

  f i =
    if tagToEnum# (i <# 18#) then
      if tagToEnum# (i <# 12#) then
        if tagToEnum# (i <# 4#) then
          12#
        else
          14#
      else
        if tagToEnum# (i <# 14#) then
          12#
        else
          10#
    else
      if tagToEnum# (i <# 22#) then
        9#
      else
        if tagToEnum# (i <# 24#) then
          11#
        else
          12#

  go !k !c0 !c1 !r = if tagToEnum# (k <# 0#) then r else go (k -# 1#) c0' c1' r'
    where
      h0  = cStateToH c0
      h1  = cStateToH c1
      u0  = if tagToEnum# (h0 <# f h1) then 0# else (if cHead c0 then -1# else 1#)
      u1  = if tagToEnum# (h1 <# f h0) then 0# else (if cHead c1 then -1# else 1#)
      c0' = cStateUpdate u0 c0 (tst d0 (k -# 5#))
      c1' = cStateUpdate u1 c1 (tst d1 (k -# 5#))

      r2 = ec_double p r

      r' =
        case u0 of
          -1# ->
            case u1 of
              -1# -> ec_full_sub p r2 spt'
              1#  -> ec_full_sub p r2 smt'
              _   -> ec_full_sub p r2 s'
          1#  ->
            case u1 of
              -1# -> ec_full_add p r2 smt'
              1#  -> ec_full_add p r2 spt'
              _   -> ec_full_add p r2 s'
          _   ->
            case u1 of
              -1# -> ec_full_sub p r2 t'
              1#  -> ec_full_add p r2 t'
              _   -> r2

data CState = C !Bool !Bool !Bool !Bool !Bool !Bool

{-# INLINE cHead #-}
cHead :: CState -> Bool
cHead (C c0 _ _ _ _ _) = c0

{-# INLINE cStateToH #-}
cStateToH :: CState -> Int#
cStateToH c@(C c0 _ _ _ _ _) =
  if c0 then 31# -# cStateToInt c else cStateToInt c

{-# INLINE cStateToInt #-}
cStateToInt :: CState -> Int#
cStateToInt (C _ c1 c2 c3 c4 c5) =
  (dataToTag# c1 `uncheckedIShiftL#` 4#) +#
  (dataToTag# c2 `uncheckedIShiftL#` 3#) +#
  (dataToTag# c3 `uncheckedIShiftL#` 2#) +#
  (dataToTag# c4 `uncheckedIShiftL#` 1#) +#
  (dataToTag# c5)

{-# INLINE cStateUpdate #-}
cStateUpdate :: Int# -> CState -> Bool -> CState
cStateUpdate u (C _ c1 c2 c3 c4 c5) e =
  case u of
    0# -> C c1 c2 c3 c4 c5 e
    _  -> C (complement c1) c2 c3 c4 c5 e
