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
{-# LANGUAGE TypeApplications #-}
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
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import           Data.Bits
import           Data.Word
import           Numeric (showIntAtBase)
import qualified LibBF as FP
import qualified GHC.Integer.GMP.Internals as Integer
import           System.Random (random, randomR, split)
import           System.Random.TF.Gen (TFGen, seedTFGen)

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

randomSize :: Word8 -> Word8 -> TFGen -> (Word8, TFGen)
randomSize k n g
  | p == 1 = (n, g')
  | otherwise = randomSize k (n + 1) g'
  where (p, g') = randomR (1, k) g

instance Backend Concrete where
  type SBit Concrete = Bool
  type SWord Concrete = BV
  type SInteger Concrete = Integer
  type SFloat Concrete = FP.BF
  type SEval Concrete = Eval
  type SGen Concrete = ReaderT Word8 (StateT TFGen Eval)

  raiseError _ err =
    do stk <- getCallStack
       io (X.throwIO (EvalErrorEx stk err))

  assertSideCondition _ True _ = return ()
  assertSideCondition sym False err = raiseError sym err

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
  sSpark _ = evalSpark
  sModifyCallStack _ f m = modifyCallStack f m
  sGetCallStack _ = getCallStack

  sGenLift _sym m = lift (lift m)
  sRunGen _sym sz seed m =
    do let mask64 = 0xFFFFFFFFFFFFFFFF
           unpack s = fromInteger (s .&. mask64) : unpack (s `shiftR` 64)
           [a, b, c, d] = take 4 (unpack (bvVal seed))
           g0 = seedTFGen (a,b,c,d)
       fst <$> runStateT (runReaderT m (fromInteger (bvVal sz))) g0

  sGenGetSize _sym = reader (mkBv 8 . toInteger)
  sGenWithSize _sym sz m = local (\_ -> fromInteger (bvVal sz)) m

  sGenerateBit _sym = state random
  sUnboundedWord _sym w = mkBv w <$> state (randomR (0, 2^w - 1))
  sBoundedWord _sym (BV w b1,BV _ b2) = mkBv w <$> state (randomR (lo, hi))
    where
    lo = min b1 b2
    hi = max b1 b2

  sBoundedSignedWord _sym (BV w x1,BV _ x2) = mkBv w <$> state (randomR (lo, hi))
    where
    b1 = signedValue w x1
    b2 = signedValue w x2

    lo = min b1 b2
    hi = max b1 b2

  sBoundedInteger _sym (x1,x2) = state (randomR (lo, hi))
    where
    lo = min x1 x2
    hi = max x1 x2

  sUnboundedInteger _sym =
    do sz <- ask
       n  <- if sz < 100 then pure sz else state (randomSize 8 100)
       state (randomR (- 256^n, 256^n ))

  sBoundedBelowInteger _sym lo =
    do sz <- ask
       n  <- if sz < 100 then pure sz else state (randomSize 8 100)
       x  <- state (randomR (0, 256^n))
       pure (lo + x)

  sBoundedAboveInteger _sym hi =
    do sz <- ask
       n  <- if sz < 100 then pure sz else state (randomSize 8 100)
       x  <- state (randomR (0, 256^n))
       pure (hi - x)

  sSuchThat sym m p =
    do x <- m
       b <- lift (lift (p x))
       if b then pure x else sSuchThat sym m p

  sGenStream sym m =
    do sz <- ask
       (x, fill) <- sGenLift sym (blackhole "sGenStream")
       g0 <- state split
       let mkElem  = runStateT (runReaderT m sz)
       let mkMap = IndexSeqMap @Concrete \i ->
                       if i <= 0 then
                         mkElem g0
                       else
                         do x' <- x
                            (_,g) <- lookupSeqMap @Concrete x' (i-1)
                            mkElem g
       sGenLift sym (fill (memoMap sym mkMap))
       pure (IndexSeqMap \i -> x >>= \x' -> fst <$> lookupSeqMap @Concrete x' i)


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

  intToZn _ 0 _ = evalPanic "intToZn" ["0 modulus not allowed"]
  intToZn _ m x = pure $! x `mod` m

  -- NB: requires we maintain the invariant that
  --     Z_n is in reduced form
  znToInt _ _m x = pure x
  znEq _ _m x y = pure $! x == y

  -- NB: under the precondition that `m` is prime,
  -- the only values for which no inverse exists are
  -- congruent to 0 modulo m.
  znRecip sym m x
    | r == 0    = raiseError sym DivideByZero
    | otherwise = pure r
   where
     r = Integer.recipModInteger x m

  znPlus  _ = liftBinIntMod (+)
  znMinus _ = liftBinIntMod (-)
  znMult  _ = liftBinIntMod (*)
  znNegate _ 0 _ = evalPanic "znNegate" ["0 modulus not allowed"]
  znNegate _ m x = pure $! (negate x) `mod` m

  ------------------------------------------------------------------------
  -- Floating Point
  fpLit _sym e p rat     = pure (FP.fpLit e p rat)
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
  fpNeg _ x = pure x { FP.bfValue = FP.bfNeg (FP.bfValue x) }
  fpFromInteger sym e p r x =
    do opts <- FP.fpOpts e p <$> fpRoundMode sym r
       pure FP.BF { FP.bfExpWidth = e
                  , FP.bfPrecWidth = p
                  , FP.bfValue = FP.fpCheckStatus $
                                 FP.bfRoundInt opts (FP.bfFromInteger x)
                  }
  fpToInteger = fpCvtToInteger


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
     pure x { FP.bfValue = FP.fpCheckStatus
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
