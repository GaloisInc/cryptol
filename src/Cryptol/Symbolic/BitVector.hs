-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Cryptol.Symbolic.BitVector where

import Data.Bits
import Control.Monad (replicateM)
import Control.Monad.IO.Class
import Control.Monad.Reader (MonadReader, ReaderT, ask, runReaderT)
import Data.Bits
import Data.IORef
import System.Random
import Test.QuickCheck (quickCheck)

import Data.SBV.Bridge.Yices
import Data.SBV.Internals
import Data.SBV.BitVectors.Data

-- BitVector type --------------------------------------------------------------

data BitVector = BV { width :: !Int, val :: !Integer }
    deriving (Eq, Ord, Show)
-- ^ Invariant: BV w x requires that 0 <= w and 0 <= x < 2^w.

bitMask :: Int -> Integer
bitMask w = bit w - 1

-- | Smart constructor for bitvectors.
bv :: Int -> Integer -> BitVector
bv w x = BV w (x .&. bitMask w)

unsigned :: BitVector -> Integer
unsigned = val

signed :: BitVector -> Integer
signed (BV w x)
  | w > 0 && testBit x (w - 1) = x - bit w
  | otherwise                  = x

same :: Int -> Int -> Int
same m n = if m == n then m else error $ "BitVector size mismatch: " ++ show (m, n)

instance Num BitVector where
  fromInteger n = error $ "fromInteger " ++ show n ++ " :: BitVector"
  BV m x + BV n y = bv (same m n) (x + y)
  BV m x - BV n y = bv (same m n) (x - y)
  BV m x * BV n y = bv (same m n) (x * y)
  negate (BV m x) = bv m (- x)
  abs = id
  signum (BV m _) = bv m 1

instance Bits BitVector where
  BV m x .&. BV n y        = BV (same m n) (x .&. y)
  BV m x .|. BV n y        = BV (same m n) (x .|. y)
  BV m x `xor` BV n y      = BV (same m n) (x `xor` y)
  complement (BV m x)      = BV m (x `xor` bitMask m)
  shift (BV m x) i         = bv m (shift x i)
  rotate (BV m x) i        = bv m (shift x j .|. shift x (j - m))
                               where j = i `mod` m
  bit _i                   = error "bit: can't determine width"
  setBit (BV m x) i        = BV m (setBit x i)
  clearBit (BV m x) i      = BV m (clearBit x i)
  complementBit (BV m x) i = BV m (complementBit x i)
  testBit (BV _ x) i       = testBit x i
  bitSize (BV m _)         = m
  isSigned _               = False
  popCount (BV _ x)        = popCount x

--------------------------------------------------------------------------------
-- SBV class instances

type SWord = SBV BitVector

instance HasKind BitVector where
  kindOf (BV w _) = KBounded False w

instance SymWord BitVector where
  literal (BV w x) = SBV k (Left (mkConstCW k x))
      where k = KBounded False w
  fromCW c@(CW (KBounded False w) _) = BV w (fromCW c)
  fromCW c = error $ "fromCW: Unsupported non-integral value: " ++ show c
  mkSymWord _ _ = error "mkSymWord unimplemented for type BitVector"

instance SIntegral BitVector where

instance FromBits (SBV BitVector) where
  fromBitsLE bs = go (literal (bv (length bs) 0)) 0 bs
    where go !acc _  []     = acc
          go !acc !i (x:xs) = go (ite x (setBit acc i) acc) (i+1) xs

instance SDivisible BitVector where
  sQuotRem (BV m x) (BV n y) = (BV w q, BV w r)
    where (q, r) = quotRem x y
          w = same m n
  sDivMod (BV m x) (BV n y) = (BV w q, BV w r)
    where (q, r) = divMod x y
          w = same m n

instance SDivisible (SBV BitVector) where
  sQuotRem = liftQRem
  sDivMod  = liftDMod

extract :: Int -> Int -> SWord -> SWord
extract i j x =
  case x of
    SBV _ (Left cw) ->
      case cw of
        CW _ (CWInteger v) -> SBV k (Left (normCW (CW k (CWInteger (v `shiftR` j)))))
        _ -> error "extract"
    _ -> SBV k (Right (cache y))
      where y st = do sw <- sbvToSW st x
                      newExpr st k (SBVApp (Extract i j) [sw])
  where
    k = KBounded False (i - j + 1)

cat :: SWord -> SWord -> SWord
cat x y | bitSize x == 0 = y
        | bitSize y == 0 = x
cat x@(SBV _ (Left a)) y@(SBV _ (Left b)) =
  case (a, b) of
    (CW _ (CWInteger m), CW _ (CWInteger n)) ->
      SBV k (Left (CW k (CWInteger ((m `shiftL` (bitSize y) .|. n)))))
    _ -> error "cat"
  where k = KBounded False (bitSize x + bitSize y)
cat x y = SBV k (Right (cache z))
  where k = KBounded False (bitSize x + bitSize y)
        z st = do xsw <- sbvToSW st x
                  ysw <- sbvToSW st y
                  newExpr st k (SBVApp Join [xsw, ysw])

randomSBVBitVector :: Int -> IO (SBV BitVector)
randomSBVBitVector width = do
  bs <- replicateM width randomIO
  let x = sum [ bit i | (i, b) <- zip [0..] bs, b ]
  return (literal (bv width x))

mkSymBitVector :: Maybe Quantifier -> Maybe String -> Int -> Symbolic (SBV BitVector)
mkSymBitVector mbQ mbNm width =
  mkSymSBVWithRandom (randomSBVBitVector width) mbQ (KBounded False width) mbNm

forallBV :: String -> Int -> Symbolic (SBV BitVector)
forallBV name width = mkSymBitVector (Just ALL) (Just name) width

forallBV_ :: Int -> Symbolic (SBV BitVector)
forallBV_ width = mkSymBitVector (Just ALL) Nothing width

existsBV :: String -> Int -> Symbolic (SBV BitVector)
existsBV name width = mkSymBitVector (Just EX) (Just name) width

existsBV_ :: Int -> Symbolic (SBV BitVector)
existsBV_ width = mkSymBitVector (Just EX) Nothing width
