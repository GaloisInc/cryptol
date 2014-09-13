-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Cryptol.Symbolic.BitVector where

import Data.Bits
import Control.Monad (replicateM)
import System.Random

import Data.SBV.Bridge.Yices
import Data.SBV.Internals
import Data.SBV.BitVectors.Data

import Cryptol.Utils.Panic

-- BitVector type --------------------------------------------------------------

data BitVector = BV { signedcxt :: Bool, width :: !Int, val :: !Integer }
    deriving (Eq, Ord, Show)
-- ^ Invariant: BV w x requires that 0 <= w and 0 <= x < 2^w.

bitMask :: Int -> Integer
bitMask w = bit w - 1

-- | Smart constructor for bitvectors.
bv :: Int -> Integer -> BitVector
bv = sbv False

sbv :: Bool -> Int -> Integer -> BitVector
sbv b w x = BV b w (x .&. bitMask w)

unsigned :: Int -> Integer -> Integer
unsigned w x = x + bit w

signed :: Int -> Integer -> Integer
signed w x
  | w > 0 && testBit x (w - 1) = x - bit w
  | otherwise                  = x

same :: Int -> Int -> Int
same m n | m == n = m
         | otherwise = panic "Cryptol.Symbolic.BitVector.same"
                         [ "BitVector size mismatch: " ++ show (m, n) ]

instance SignCast SWord SWord where
  signCast (SBV (KBounded _ w) (Left (cwVal -> (CWInteger x)))) =
    SBV k (Left (CW k (CWInteger (signed w x)))) where
      k = KBounded True w
  signCast x@(SBV (KBounded _ w) _) = SBV k (Right (cache y)) where
    k = KBounded True w
    y st = do xsw <- sbvToSW st x
              newExpr st k (SBVApp (Extract (intSizeOf x-1) 0) [xsw])
  signCast _ = panic "Cryptol.Symbolic.BitVector"
                 [ "signCast called on non-bitvector value" ]
  unsignCast (SBV (KBounded _ w) (Left (cwVal -> (CWInteger x)))) =
    SBV k (Left (CW k (CWInteger (unsigned w x)))) where
      k = KBounded False w
  unsignCast x@(SBV (KBounded _ w) _) = SBV k (Right (cache y)) where
    k = KBounded False w
    y st = do xsw <- sbvToSW st x
              newExpr st k (SBVApp (Extract (intSizeOf x-1) 0) [xsw])
  unsignCast _ = panic "Cryptol.Symbolic.BitVector"
                   [ "unsignCast called on non-bitvector value" ]

instance Num BitVector where
  fromInteger n = panic "Cryptol.Symbolic.BitVector"
                    [ "fromInteger " ++ show n ++ " :: BitVector" ]
  BV s m x + BV _ n y = sbv s (same m n) (x + y)
  BV s m x - BV _ n y = sbv s (same m n) (x - y)
  BV s m x * BV _ n y = sbv s (same m n) (x * y)
  negate (BV s m x) = sbv s m (- x)
  abs = id
  signum (BV s m _) = sbv s m 1

instance Bits BitVector where
  BV s m x .&. BV _ n y        = BV s (same m n) (x .&. y)
  BV s m x .|. BV _ n y        = BV s (same m n) (x .|. y)
  BV s m x `xor` BV _ n y      = BV s (same m n) (x `xor` y)
  complement (BV s m x)        = BV s m (x `xor` bitMask m)
  shift (BV s m x) i           = sbv s m (shift x i)
  rotate (BV s m x) i          = sbv s m (shift x j .|. shift x (j - m))
                                  where j = i `mod` m
  bit _i                       = panic "Cryptol.Symbolic.BitVector"
                                   [ "bit: can't determine width" ]
  setBit (BV s m x) i          = BV s m (setBit x i)
  clearBit (BV s m x) i        = BV s m (clearBit x i)
  complementBit (BV s m x) i   = BV s m (complementBit x i)
  testBit (BV _ _ x) i         = testBit x i
  bitSize (BV _ m _)           = m
#if __GLASGOW_HASKELL__ >= 708
  bitSizeMaybe (BV _ m _)      = Just m
#endif
  isSigned (BV s _ _)          = s
  popCount (BV _ _ x)          = popCount x

--------------------------------------------------------------------------------
-- SBV class instances

type SWord = SBV BitVector

instance HasKind BitVector where
  kindOf (BV s w _) = KBounded s w

instance SymWord BitVector where
  literal (BV s w x) = SBV k (Left (mkConstCW k x))
      where k = KBounded s w
  fromCW c@(CW (KBounded s w) _) = BV s w (fromCW c)
  fromCW c = panic "Cryptol.Symbolic.BitVector"
               [ "fromCW: Unsupported non-integral value: " ++ show c ]
  mkSymWord _ _ = panic "Cryptol.Symbolic.BitVector"
                    [ "mkSymWord unimplemented for type BitVector" ]

instance SIntegral BitVector where

instance FromBits (SBV BitVector) where
  fromBitsLE bs = go (literal (bv (length bs) 0)) 0 bs
    where go !acc _  []     = acc
          go !acc !i (x:xs) = go (ite x (setBit acc i) acc) (i+1) xs

instance SDivisible BitVector where
  sQuotRem (BV _ m x) (BV _ n y) = (BV False w q, BV False w r)
    where (q, r) = quotRem x y
          w = same m n
  sDivMod (BV _ m x) (BV _ n y) = (BV False w q, BV False w r)
    where (q, r) = divMod x y
          w = same m n

instance SDivisible (SBV BitVector) where
  sQuotRem = liftQRem
  sDivMod  = liftDMod

extract :: Int -> Int -> SWord -> SWord
extract i j x@(SBV (KBounded s _) _) =
  case x of
    _ | i < j -> SBV k (Left (CW k (CWInteger 0)))
    SBV _ (Left cw) ->
      case cw of
        CW _ (CWInteger v) -> SBV k (Left (normCW (CW k (CWInteger (v `shiftR` j)))))
        _ -> panic "Cryptol.Symbolic.BitVector.extract" [ "non-integer concrete word" ]
    _ -> SBV k (Right (cache y))
      where y st = do sw <- sbvToSW st x
                      newExpr st k (SBVApp (Extract i j) [sw])
  where
    k = KBounded s (i - j + 1)
extract _ _ _ = panic "Cryptol.Symbolic.BitVector.extract" [ "non-bitvector value" ]

cat :: SWord -> SWord -> SWord
cat x y | bitSize x == 0 = y
        | bitSize y == 0 = x
cat x@(SBV _ (Left a)) y@(SBV _ (Left b)) =
  case (a, b) of
    (CW _ (CWInteger m), CW _ (CWInteger n)) ->
      SBV k (Left (CW k (CWInteger ((m `shiftL` (bitSize y) .|. n)))))
    _ -> panic "Cryptol.Symbolic.BitVector.cat" [ "non-integer concrete word" ]
  where k = KBounded False (bitSize x + bitSize y)
cat x y = SBV k (Right (cache z))
  where k = KBounded False (bitSize x + bitSize y)
        z st = do xsw <- sbvToSW st x
                  ysw <- sbvToSW st y
                  newExpr st k (SBVApp Join [xsw, ysw])

randomSBVBitVector :: Int -> IO (SBV BitVector)
randomSBVBitVector w = do
  bs <- replicateM w randomIO
  let x = sum [ bit i | (i, b) <- zip [0..] bs, b ]
  return (literal (bv w x))

mkSymBitVector :: Maybe Quantifier -> Maybe String -> Int -> Symbolic (SBV BitVector)
mkSymBitVector mbQ mbNm w =
  mkSymSBVWithRandom (randomSBVBitVector w) mbQ (KBounded False w) mbNm

forallBV :: String -> Int -> Symbolic (SBV BitVector)
forallBV nm w = mkSymBitVector (Just ALL) (Just nm) w

forallBV_ :: Int -> Symbolic (SBV BitVector)
forallBV_ w = mkSymBitVector (Just ALL) Nothing w

existsBV :: String -> Int -> Symbolic (SBV BitVector)
existsBV nm w = mkSymBitVector (Just EX) (Just nm) w

existsBV_ :: Int -> Symbolic (SBV BitVector)
existsBV_ w = mkSymBitVector (Just EX) Nothing w
