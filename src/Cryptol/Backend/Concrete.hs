-- |
-- Module      :  Cryptol.Backend.Concrete
-- Copyright   :  (c) 2013-2020 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
module Cryptol.Backend.Concrete
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
  , Concrete(..)
  , liftBinIntMod
  , fpBinArith
  , fpRoundMode
  ) where

import qualified Control.Exception as X
import Data.Bits
import Data.Ratio
import Numeric (showIntAtBase)
import qualified LibBF as FP
import qualified GHC.Num.Compat as Integer

import qualified Cryptol.Backend.Arch as Arch
import qualified Cryptol.Backend.FloatHelpers as FP
import Cryptol.Backend
import Cryptol.Backend.Monad
import Cryptol.TypeCheck.Solver.InfNat (genLog)
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.PP

data Concrete = Concrete deriving Show

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
    10 -> mempty
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
  type SFloat Concrete = FP.BF
  type SEval Concrete = Eval

  raiseError _ err =
    do stk <- getCallStack
       io (X.throwIO (EvalErrorEx stk err))

  assertSideCondition _ True _ = return ()
  assertSideCondition sym False err = raiseError sym err

  wordLen' _ (BV w _) = w
  {-# INLINE wordLen' #-}
  
  wordAsChar _ (BV _ x) = Just $! integerToChar x

  wordBit _ (BV w x) idx = pure $! testBit x (fromInteger (w - 1 - idx))

  wordUpdate _ (BV w x) idx True  = pure $! BV w (setBit   x (fromInteger (w - 1 - idx)))
  wordUpdate _ (BV w x) idx False = pure $! BV w (clearBit x (fromInteger (w - 1 - idx)))

  isReady _ = maybeReady

  mergeEval _sym f c mx my =
    do x <- mx
       y <- my
       f c x y

  sDeclareHole _ = blackhole
  sDelayFill _ = delayFill
  sSpark _ = evalSpark
  sModifyCallStack _ f m = modifyCallStack f m
  sGetCallStack _ = getCallStack

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
  iteFloat _ b x y   = pure $! if b then x else y

  wordLit _ w i = pure $! mkBv w i
  wordAsLit _ (BV w i) = Just (w,i)
  integerLit _ i = pure i
  integerAsLit _ = Just

  wordToInt _ (BV _ x) = pure x
  wordToSignedInt _ (BV w x) = pure $! signedValue w x
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

  wordShiftLeft _sym (BV w ival) (BV _ by)
    | by >= w   = pure $! BV w 0
    | by > toInteger (maxBound :: Int) = panic "shl" ["Shift amount too large", show by]
    | otherwise = pure $! mkBv w (shiftL ival (fromInteger by))

  wordShiftRight _sym (BV w ival) (BV _ by)
    | by >= w   = pure $! BV w 0
    | by > toInteger (maxBound :: Int) = panic "lshr" ["Shift amount too large", show by]
    | otherwise = pure $! BV w (shiftR ival (fromInteger by))

  wordSignedShiftRight _sym (BV w ival) (BV _ by) =
    let by' = min w by in
    if by' > toInteger (maxBound :: Int) then
      panic "wordSignedShiftRight" ["Shift amount too large", show by]
    else
      pure $! mkBv w (shiftR (signedValue w ival) (fromInteger by'))

  wordRotateRight _sym (BV 0 i) _ = pure (BV 0 i)
  wordRotateRight _sym (BV w i) (BV _ by) =
      pure . mkBv w $! (i `shiftR` b) .|. (i `shiftL` (fromInteger w - b))
    where b = fromInteger (by `mod` w)

  wordRotateLeft _sym (BV 0 i) _ = pure (BV 0 i)
  wordRotateLeft _sym (BV w i) (BV _ by) =
      pure . mkBv w $! (i `shiftL` b) .|. (i `shiftR` (fromInteger w - b))
    where b = fromInteger (by `mod` w)

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

  intToZn _ 0 _ = evalPanic "intToZn" ["0 modulus not allowed"]
  intToZn _ m x = pure $! x `mod` m

  -- NB: requires we maintain the invariant that
  --     Z_n is in reduced form
  znToInt _ _m x = pure x
  znEq _ _m x y = pure $! x == y

  -- NB: under the precondition that `m` is prime,
  -- the only values for which no inverse exists are
  -- congruent to 0 modulo m.
  znRecip sym m x =
    case Integer.integerRecipMod x m of
      Just r  -> integerLit sym r
      Nothing -> raiseError sym DivideByZero

  znPlus  _ = liftBinIntMod (+)
  znMinus _ = liftBinIntMod (-)
  znMult  _ = liftBinIntMod (*)
  znNegate _ 0 _ = evalPanic "znNegate" ["0 modulus not allowed"]
  znNegate _ m x = pure $! (negate x) `mod` m

  ------------------------------------------------------------------------
  -- Floating Point
  fpLit _sym e p rat     = pure (FP.fpLit e p rat)

  fpNaN _sym e p         = pure (FP.BF e p FP.bfNaN)
  fpPosInf _sym e p      = pure (FP.BF e p FP.bfPosInf)

  fpAsLit _ f            = Just f
  fpExactLit _sym bf     = pure bf
  fpEq _sym x y          = pure (FP.bfValue x == FP.bfValue y)
  fpLogicalEq _sym x y   = pure (FP.bfCompare (FP.bfValue x) (FP.bfValue y) == EQ)
  fpLessThan _sym x y    = pure (FP.bfValue x <  FP.bfValue y)
  fpGreaterThan _sym x y = pure (FP.bfValue x >  FP.bfValue y)
  fpPlus  = fpBinArith FP.bfAdd
  fpMinus = fpBinArith FP.bfSub
  fpMult  = fpBinArith FP.bfMul
  fpDiv   = fpBinArith FP.bfDiv
  fpNeg _ x = pure $! x { FP.bfValue = FP.bfNeg (FP.bfValue x) }

  fpAbs _ x = pure $! x { FP.bfValue = FP.bfAbs (FP.bfValue x) }
  fpSqrt sym r x =
    do r' <- fpRoundMode sym r
       let opts = FP.fpOpts (FP.bfExpWidth x) (FP.bfPrecWidth x) r'
       pure $! x{ FP.bfValue = FP.fpCheckStatus (FP.bfSqrt opts (FP.bfValue x)) }

  fpFMA sym r x y z =
    do r' <- fpRoundMode sym r
       let opts = FP.fpOpts (FP.bfExpWidth x) (FP.bfPrecWidth x) r'
       pure $! x { FP.bfValue = FP.fpCheckStatus (FP.bfFMA opts (FP.bfValue x) (FP.bfValue y) (FP.bfValue z)) }

  fpIsZero _ x = pure (FP.bfIsZero (FP.bfValue x))
  fpIsNeg _ x  = pure (FP.bfIsNeg (FP.bfValue x))
  fpIsNaN _ x  = pure (FP.bfIsNaN (FP.bfValue x))
  fpIsInf _ x  = pure (FP.bfIsInf (FP.bfValue x))
  fpIsNorm _ x =
    let opts = FP.fpOpts (FP.bfExpWidth x) (FP.bfPrecWidth x) FP.NearEven
     in pure (FP.bfIsNormal opts (FP.bfValue x))
  fpIsSubnorm _ x =
    let opts = FP.fpOpts (FP.bfExpWidth x) (FP.bfPrecWidth x) FP.NearEven
     in pure (FP.bfIsSubnormal opts (FP.bfValue x))

  fpFromBits _sym e p bv = pure (FP.floatFromBits e p (bvVal bv))
  fpToBits _sym (FP.BF e p v) = pure (mkBv (e+p) (FP.floatToBits e p v))

  fpFromInteger sym e p r x =
    do r' <- fpRoundMode sym r
       pure FP.BF { FP.bfExpWidth = e
                  , FP.bfPrecWidth = p
                  , FP.bfValue = FP.fpCheckStatus $
                                 FP.bfRoundInt r' (FP.bfFromInteger x)
                  }
  fpToInteger = fpCvtToInteger

  fpFromRational sym e p r x =
    do mode <- fpRoundMode sym r
       pure (FP.floatFromRational e p mode (sNum x % sDenom x))

  fpToRational sym fp =
      case FP.floatToRational "fpToRational" fp of
        Left err -> raiseError sym err
        Right r  -> pure $ SRational { sNum = numerator r, sDenom = denominator r }

{-# INLINE liftBinIntMod #-}
liftBinIntMod :: Monad m =>
  (Integer -> Integer -> Integer) -> Integer -> Integer -> Integer -> m Integer
liftBinIntMod op m x y
  | m == 0    = evalPanic "znArithmetic" ["0 modulus not allowed"]
  | otherwise = pure $ (op x y) `mod` m



{-# INLINE fpBinArith #-}
fpBinArith ::
  (FP.BFOpts -> FP.BigFloat -> FP.BigFloat -> (FP.BigFloat, FP.Status)) ->
  Concrete ->
  SWord Concrete  {- ^ Rouding mode -} ->
  SFloat Concrete ->
  SFloat Concrete ->
  SEval Concrete (SFloat Concrete)
fpBinArith fun = \sym r x y ->
  do opts <- FP.fpOpts (FP.bfExpWidth x) (FP.bfPrecWidth x)
                                                  <$> fpRoundMode sym r
     pure $! x { FP.bfValue = FP.fpCheckStatus
                                (fun opts (FP.bfValue x) (FP.bfValue y)) }

fpCvtToInteger ::
  Concrete ->
  String ->
  SWord Concrete {- ^ Rounding mode -} ->
  SFloat Concrete ->
  SEval Concrete (SInteger Concrete)
fpCvtToInteger sym fun rnd flt =
  do mode <- fpRoundMode sym rnd
     case FP.floatToInteger fun mode flt of
       Right i -> pure i
       Left err -> raiseError sym err

fpRoundMode :: Concrete -> SWord Concrete -> SEval Concrete FP.RoundMode
fpRoundMode sym w =
  case FP.fpRound (bvVal w) of
    Left err -> raiseError sym err
    Right a  -> pure a
