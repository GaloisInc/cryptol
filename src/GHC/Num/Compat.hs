{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UnboxedSums #-}
{-# LANGUAGE UnboxedTuples #-}

-- |
-- Module      :  GHC.Num.Compat
-- Description :  Defines numeric compatibility shims that work with both
--                ghc-bignum (GHC 9.0+) and integer-gmp (older GHCs).
-- Copyright   :  (c) 2021 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
module GHC.Num.Compat
  ( -- * BigNat#
    BigNat#
  , bigNatAdd
  , bigNatIsOne
  , bigNatIsZero
  , bigNatMul
  , bigNatRem
  , bigNatSqr
  , bigNatSub
  , bigNatSubUnsafe
  , oneBigNat
  , recipModBigNat
  , shiftLBigNat
  , shiftRBigNat
  , testBitBigNat
  , zeroBigNat

    -- * Integer
  , Integer(IS, IP, IN)
  , integerRecipMod

    -- * Conversions
  , bigNatToInteger
  , integerToBigNat
  ) where

#if defined(MIN_VERSION_ghc_bignum)
import           GHC.Num.BigNat (BigNat#, bigNatAdd, bigNatIsOne, bigNatIsZero, bigNatMul, bigNatRem, bigNatSqr, bigNatSub, bigNatSubUnsafe)
import qualified GHC.Num.Backend as BN
import qualified GHC.Num.BigNat as BN
import           GHC.Num.Integer (Integer(IS, IP, IN))
import qualified GHC.Num.Integer as Integer
import           GHC.Exts

-- | Coerce a @BigNat#@ to an integer value.
bigNatToInteger :: BigNat# -> Integer
bigNatToInteger = Integer.integerFromBigNat#

-- | @'integerRecipMod' x m@ computes the modular inverse of @x@ mod @m@.
--
-- PRECONDITION: @m@ must be strictly positive.
integerRecipMod :: Integer -> Integer -> Maybe Integer
integerRecipMod x y =
  case Integer.integerRecipMod# x (Integer.integerToNaturalClamp y) of
    (# r | #)  -> Just (toInteger r)
    (# | () #) -> Nothing

-- | Coerce an integer value to a @BigNat#@.  This operation only really makes
--   sense for nonnegative values, but this condition is not checked.
integerToBigNat :: Integer -> BigNat#
integerToBigNat = Integer.integerToBigNatClamp#

-- Top-level unlifted bindings aren't allowed, so we fake one with a thunk.
oneBigNat :: (# #) -> BigNat#
oneBigNat _ = BN.bigNatFromWord# 1##

recipModBigNat :: BigNat# -> BigNat# -> BigNat#
recipModBigNat = BN.sbignat_recip_mod 0#

shiftLBigNat :: BigNat# -> Int# -> BigNat#
shiftLBigNat bn i = BN.bigNatShiftL# bn (int2Word# i)

shiftRBigNat :: BigNat# -> Int# -> BigNat#
shiftRBigNat bn i = BN.bigNatShiftR# bn (int2Word# i)

testBitBigNat :: BigNat# -> Int# -> Bool
testBitBigNat bn i = isTrue# (BN.bigNatTestBit# bn (int2Word# i))

-- Top-level unlifted bindings aren't allowed, so we fake one with a thunk.
zeroBigNat :: (# #) -> BigNat#
zeroBigNat _ = BN.bigNatFromWord# 0##
#else
import           GHC.Integer.GMP.Internals (bigNatToInteger, recipModBigNat, shiftLBigNat, shiftRBigNat, testBitBigNat)
import qualified GHC.Integer.GMP.Internals as GMP
import           GHC.Exts

type BigNat# = GMP.BigNat

{-# COMPLETE IS, IP, IN #-}

pattern IS :: Int# -> Integer
pattern IS i = GMP.S# i

pattern IP :: ByteArray# -> Integer
pattern IP ba = GMP.Jp# (GMP.BN# ba)

pattern IN :: ByteArray# -> Integer
pattern IN ba = GMP.Jn# (GMP.BN# ba)

bigNatAdd :: BigNat# -> BigNat# -> BigNat#
bigNatAdd = GMP.plusBigNat

bigNatIsOne :: BigNat# -> Bool
bigNatIsOne bn = GMP.eqBigNat bn GMP.oneBigNat

bigNatIsZero :: BigNat# -> Bool
bigNatIsZero = GMP.isZeroBigNat

bigNatMul :: BigNat# -> BigNat# -> BigNat#
bigNatMul = GMP.timesBigNat

bigNatRem :: BigNat# -> BigNat# -> BigNat#
bigNatRem = GMP.remBigNat

bigNatSqr :: BigNat# -> BigNat#
bigNatSqr = GMP.sqrBigNat

bigNatSub :: BigNat# -> BigNat# -> (# (# #) | BigNat# #)
bigNatSub x y =
  case GMP.isNullBigNat# res of
    0# -> (# | res #)
    _  -> (# (# #) | #)
  where
    res = GMP.minusBigNat x y

bigNatSubUnsafe :: BigNat# -> BigNat# -> BigNat#
bigNatSubUnsafe = GMP.minusBigNat

integerToBigNat :: Integer -> BigNat#
integerToBigNat (GMP.S# i)  = GMP.wordToBigNat (int2Word# i)
integerToBigNat (GMP.Jp# b) = b
integerToBigNat (GMP.Jn# b) = b

-- | @'integerRecipMod' x m@ computes the modular inverse of @x@ mod @m@.
--
-- PRECONDITION: @m@ must be strictly positive.
integerRecipMod :: Integer -> Integer -> Maybe Integer
integerRecipMod x y
  | res == 0  = Nothing
  | otherwise = Just res
  where
    res = GMP.recipModInteger x y

oneBigNat :: (##) -> BigNat#
oneBigNat _ = GMP.oneBigNat

zeroBigNat :: (##) -> BigNat#
zeroBigNat _ = GMP.zeroBigNat
#endif
