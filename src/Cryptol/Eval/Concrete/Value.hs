-- |
-- Module      :  Cryptol.Eval.Concrete.Value
-- Copyright   :  (c) 2013-2020 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
module Cryptol.Eval.Concrete.Value
  ( BV(..)
  , binBV
  , unaryBV
  , bvVal
  , ppBV
  , mkBv
  , mask
  , integerToChar
  , Value
  , Concrete(..)
  , liftBinIntMod
  ) where

import Data.Bits
import Numeric (showIntAtBase)

import qualified Cryptol.Eval.Arch as Arch
import Cryptol.Eval.Monad
import Cryptol.Eval.Value
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.PP

data Concrete = Concrete deriving Show

type Value = GenValue Concrete

-- | Concrete bitvector values: width, value
-- Invariant: The value must be within the range 0 .. 2^width-1
data BV = BV !Integer !Integer

instance Show BV where
  show = show . bvVal

-- | Apply an integer function to the values of bitvectors.
--   This function assumes both bitvectors are the same width.
binBV :: Applicative m => (Integer -> Integer -> Integer) -> BV -> BV -> m BV
binBV f (BV w x) (BV _ y) = pure $ mkBv w (f x y)

-- | Apply an integer function to the values of a bitvector.
--   This function assumes the function will not require masking.
unaryBV :: (Integer -> Integer) -> BV -> BV
unaryBV f (BV w x) = mkBv w $ f x

bvVal :: BV -> Integer
bvVal (BV _w x) = x

-- | Smart constructor for 'BV's that checks for the width limit
mkBv :: Integer -> Integer -> BV
mkBv w i = BV w (mask w i)


integerToChar :: Integer -> Char
integerToChar = toEnum . fromInteger


ppBV :: PPOpts -> BV -> Doc
ppBV opts (BV width i)
  | base > 36 = integer i -- not sure how to rule this out
  | asciiMode opts width = text (show (toEnum (fromInteger i) :: Char))
  | otherwise = prefix <.> text value
  where
  base = useBase opts

  padding bitsPerDigit = text (replicate padLen '0')
    where
    padLen | m > 0     = d + 1
           | otherwise = d

    (d,m) = (fromInteger width - (length value * bitsPerDigit))
                   `divMod` bitsPerDigit

  prefix = case base of
    2  -> text "0b" <.> padding 1
    8  -> text "0o" <.> padding 3
    10 -> empty
    16 -> text "0x" <.> padding 4
    _  -> text "0"  <.> char '<' <.> int base <.> char '>'

  value  = showIntAtBase (toInteger base) (digits !!) i ""
  digits = "0123456789abcdefghijklmnopqrstuvwxyz"

-- Concrete Big-endian Words ------------------------------------------------------------

mask ::
  Integer  {- ^ Bit-width -} ->
  Integer  {- ^ Value -} ->
  Integer  {- ^ Masked result -}
mask w i | w >= Arch.maxBigIntWidth = wordTooWide w
         | otherwise                = i .&. ((1 `shiftL` fromInteger w) - 1)

instance Backend Concrete where
  type SBit Concrete = Bool
  type SWord Concrete = BV
  type SInteger Concrete = Integer
  type SEval Concrete = Eval

  wordLen _ (BV w _) = w
  wordAsChar _ (BV _ x) = Just $! integerToChar x

  wordBit _ (BV w x) idx = pure $! testBit x (fromInteger (w - 1 - idx))

  wordUpdate _ (BV w x) idx True  = pure $! BV w (setBit   x (fromInteger (w - 1 - idx)))
  wordUpdate _ (BV w x) idx False = pure $! BV w (clearBit x (fromInteger (w - 1 - idx)))

  isReady _ (Ready _) = True
  isReady _ _ = False

  mergeEval _sym f c mx my =
    do x <- mx
       y <- my
       f c x y

  sDelay _ = delay
  sDeclareHole _ = blackhole
  sDelayFill _ = delayFill

  ppBit _ b | b         = text "True"
            | otherwise = text "False"

  ppWord _ = ppBV

  ppInteger _ _opts i = integer i

  bitLit _ b = pure b
  bitAsLit _ b = Just b

  iteBit _ b x y  = pure $! if b then x else y
  iteWord _ b x y = pure $! if b then x else y
  iteInteger _ b x y = pure $! if b then x else y

  wordLit _ w i = pure $! mkBv w i
  integerLit _ i = pure i

  packWord _ bits = pure $! BV (toInteger w) a
    where
      w = case length bits of
            len | toInteger len >= Arch.maxBigIntWidth -> wordTooWide (toInteger len)
                | otherwise                  -> len
      a = foldl setb 0 (zip [w - 1, w - 2 .. 0] bits)
      setb acc (n,b) | b         = setBit acc n
                     | otherwise = acc

  unpackWord _ (BV w a) = pure [ testBit a n | n <- [w' - 1, w' - 2 .. 0] ]
    where
      w' = fromInteger w

  joinWord _ (BV i x) (BV j y) =
    pure $! BV (i + j) (shiftL x (fromInteger j) + y)

  splitWord _ leftW rightW (BV _ x) =
    pure ( BV leftW (x `shiftR` (fromInteger rightW)), mkBv rightW x )

  extractWord _ n i (BV _ x) = pure $! mkBv n (x `shiftR` (fromInteger i))

  wordPlus _ (BV i x) (BV j y)
    | i == j = pure $! mkBv i (x+y)
    | otherwise = panic "Attempt to add words of different sizes: wordPlus" []

  wordMinus _ (BV i x) (BV j y)
    | i == j = pure $! mkBv i (x-y)
    | otherwise = panic "Attempt to subtract words of different sizes: wordMinus" []

  wordMult _ (BV i x) (BV j y)
    | i == j = pure $! mkBv i (x*y)
    | otherwise = panic "Attempt to multiply words of different sizes: wordMult" []

  intPlus  _ x y = pure $! x + y
  intMinus _ x y = pure $! x - y
  intMult  _ x y = pure $! x * y

  intModPlus  _ = liftBinIntMod (+)
  intModMinus _ = liftBinIntMod (-)
  intModMult  _ = liftBinIntMod (*)

  wordToInt _ (BV _ x) = pure x
  wordFromInt _ w x = pure $! mkBv w x

liftBinIntMod :: Monad m =>
  (Integer -> Integer -> Integer) -> Integer -> Integer -> Integer -> m Integer
liftBinIntMod op m x y
  | m == 0    = pure $ op x y
  | otherwise = pure $ (op x y) `mod` m
