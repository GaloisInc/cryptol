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
  , signedBV
  , signedValue
  , integerToChar
  , lg2
  , Value
  , Concrete(..)
  , liftBinIntMod
  ) where

import qualified Control.Exception as X
import Data.Bits
import Numeric (showIntAtBase)

import qualified Cryptol.Eval.Arch as Arch
import Cryptol.Eval.Monad
import Cryptol.Eval.Value
import Cryptol.TypeCheck.Solver.InfNat (genLog)
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
binBV f (BV w x) (BV _ y) = pure $! mkBv w (f x y)
{-# INLINE binBV #-}

-- | Apply an integer function to the values of a bitvector.
--   This function assumes the function will not require masking.
unaryBV :: (Integer -> Integer) -> BV -> BV
unaryBV f (BV w x) = mkBv w $! f x
{-# INLINE unaryBV #-}

bvVal :: BV -> Integer
bvVal (BV _w x) = x
{-# INLINE bvVal #-}

-- | Smart constructor for 'BV's that checks for the width limit
mkBv :: Integer -> Integer -> BV
mkBv w i = BV w (mask w i)

signedBV :: BV -> Integer
signedBV (BV i x) = signedValue i x

signedValue :: Integer -> Integer -> Integer
signedValue i x = if testBit x (fromInteger (i-1)) then x - (bit (fromInteger i)) else x

integerToChar :: Integer -> Char
integerToChar = toEnum . fromInteger

lg2 :: Integer -> Integer
lg2 i = case genLog i 2 of
  Just (i',isExact) | isExact   -> i'
                    | otherwise -> i' + 1
  Nothing                       -> 0


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
         | otherwise                = i .&. (bit (fromInteger w) - 1)

instance Backend Concrete where
  type SBit Concrete = Bool
  type SWord Concrete = BV
  type SInteger Concrete = Integer
  type SEval Concrete = Eval

  raiseError _ err = io (X.throwIO err)

  assertSideCondition _ True _ = return ()
  assertSideCondition _ False err = io (X.throwIO err)

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

  sDeclareHole _ = blackhole
  sDelayFill _ = delayFill

  ppBit _ b | b         = text "True"
            | otherwise = text "False"

  ppWord _ = ppBV

  ppInteger _ _opts i = integer i

  bitLit _ b = b
  bitAsLit _ b = Just b

  bitEq _  x y = pure $! x == y
  bitOr _  x y = pure $! x .|. y
  bitAnd _ x y = pure $! x .&. y
  bitXor _ x y = pure $! x `xor` y
  bitComplement _ x = pure $! complement x

  iteBit _ b x y  = pure $! if b then x else y
  iteWord _ b x y = pure $! if b then x else y
  iteInteger _ b x y = pure $! if b then x else y

  wordLit _ w i = pure $! mkBv w i
  wordAsLit _ (BV w i) = Just (w,i)
  integerLit _ i = pure i
  integerAsLit _ = Just

  wordToInt _ (BV _ x) = pure x
  wordFromInt _ w x = pure $! mkBv w x

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

  wordEq _ (BV i x) (BV j y)
    | i == j = pure $! x == y
    | otherwise = panic "Attempt to compare words of different sizes: wordEq" [show i, show j]

  wordSignedLessThan _ (BV i x) (BV j y)
    | i == j = pure $! signedValue i x < signedValue i y
    | otherwise = panic "Attempt to compare words of different sizes: wordSignedLessThan" [show i, show j]

  wordLessThan _ (BV i x) (BV j y)
    | i == j = pure $! x < y
    | otherwise = panic "Attempt to compare words of different sizes: wordLessThan" [show i, show j]

  wordGreaterThan _ (BV i x) (BV j y)
    | i == j = pure $! x > y
    | otherwise = panic "Attempt to compare words of different sizes: wordGreaterThan" [show i, show j]

  wordAnd _ (BV i x) (BV j y)
    | i == j = pure $! mkBv i (x .&. y)
    | otherwise = panic "Attempt to AND words of different sizes: wordPlus" [show i, show j]

  wordOr _ (BV i x) (BV j y)
    | i == j = pure $! mkBv i (x .|. y)
    | otherwise = panic "Attempt to OR words of different sizes: wordPlus" [show i, show j]

  wordXor _ (BV i x) (BV j y)
    | i == j = pure $! mkBv i (x `xor` y)
    | otherwise = panic "Attempt to XOR words of different sizes: wordPlus" [show i, show j]

  wordComplement _ (BV i x) = pure $! mkBv i (complement x)

  wordPlus _ (BV i x) (BV j y)
    | i == j = pure $! mkBv i (x+y)
    | otherwise = panic "Attempt to add words of different sizes: wordPlus" [show i, show j]

  wordNegate _ (BV i x) = pure $! mkBv i (negate x)

  wordMinus _ (BV i x) (BV j y)
    | i == j = pure $! mkBv i (x-y)
    | otherwise = panic "Attempt to subtract words of different sizes: wordMinus" [show i, show j]

  wordMult _ (BV i x) (BV j y)
    | i == j = pure $! mkBv i (x*y)
    | otherwise = panic "Attempt to multiply words of different sizes: wordMult" [show i, show j]

  wordDiv sym (BV i x) (BV j y)
    | i == 0 && j == 0 = pure $! mkBv 0 0
    | i == j =
        do assertSideCondition sym (y /= 0) DivideByZero
           pure $! mkBv i (x `div` y)
    | otherwise = panic "Attempt to divide words of different sizes: wordDiv" [show i, show j]

  wordMod sym (BV i x) (BV j y)
    | i == 0 && j == 0 = pure $! mkBv 0 0
    | i == j =
        do assertSideCondition sym (y /= 0) DivideByZero
           pure $! mkBv i (x `mod` y)
    | otherwise = panic "Attempt to mod words of different sizes: wordMod" [show i, show j]

  wordSignedDiv sym (BV i x) (BV j y)
    | i == 0 && j == 0 = pure $! mkBv 0 0
    | i == j =
        do assertSideCondition sym (y /= 0) DivideByZero
           let sx = signedValue i x
               sy = signedValue i y
           pure $! mkBv i (sx `quot` sy)
    | otherwise = panic "Attempt to divide words of different sizes: wordSignedDiv" [show i, show j]

  wordSignedMod sym (BV i x) (BV j y)
    | i == 0 && j == 0 = pure $! mkBv 0 0
    | i == j =
        do assertSideCondition sym (y /= 0) DivideByZero
           let sx = signedValue i x
               sy = signedValue i y
           pure $! mkBv i (sx `rem` sy)
    | otherwise = panic "Attempt to mod words of different sizes: wordSignedMod" [show i, show j]

  wordLg2 _ (BV i x) = pure $! mkBv i (lg2 x)

  intEq _ x y = pure $! x == y
  intLessThan _ x y = pure $! x < y
  intGreaterThan _ x y = pure $! x > y

  intPlus  _ x y = pure $! x + y
  intMinus _ x y = pure $! x - y
  intNegate _ x  = pure $! negate x
  intMult  _ x y = pure $! x * y
  intDiv sym x y =
    do assertSideCondition sym (y /= 0) DivideByZero
       pure $! x `div` y
  intMod sym x y =
    do assertSideCondition sym (y /= 0) DivideByZero
       pure $! x `mod` y
  intLg2 sym x =
    do assertSideCondition sym (x >= 0) LogNegative
       pure $! lg2 x

  intToZn _ 0 _ = evalPanic "intToZn" ["0 modulus not allowed"]
  intToZn _ m x = pure $! x `mod` m

  -- NB: requires we maintain the invariant that
  --     Z_n is in reduced form
  znToInt _ _m x = pure x
  znEq _ _m x y = pure $! x == y

  znPlus  _ = liftBinIntMod (+)
  znMinus _ = liftBinIntMod (-)
  znMult  _ = liftBinIntMod (*)
  znNegate _ 0 _ = evalPanic "znNegate" ["0 modulus not allowed"]
  znNegate _ m x = pure $! (negate x) `mod` m

{-# INLINE liftBinIntMod #-}
liftBinIntMod :: Monad m =>
  (Integer -> Integer -> Integer) -> Integer -> Integer -> Integer -> m Integer
liftBinIntMod op m x y
  | m == 0    = evalPanic "znArithmetic" ["0 modulus not allowed"]
  | otherwise = pure $ (op x y) `mod` m
