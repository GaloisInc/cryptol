{-# Language BlockArguments, OverloadedStrings #-}
{-# Language BangPatterns #-}
module Cryptol.Backend.FloatHelpers where

import Data.Ratio(numerator,denominator)
import Data.Int(Int64)
import Data.Bits(testBit,setBit,shiftL,shiftR,(.&.),(.|.))
import LibBF

import Cryptol.Utils.PP
import Cryptol.Utils.Panic(panic)
import Cryptol.Backend.Monad( EvalError(..) )


data BF = BF
  { bfExpWidth  :: Integer
  , bfPrecWidth :: Integer
  , bfValue     :: BigFloat
  }


-- | Make LibBF options for the given precision and rounding mode.
fpOpts :: Integer -> Integer -> RoundMode -> BFOpts
fpOpts e p r =
  case ok of
    Just opts -> opts
    Nothing   -> panic "floatOpts" [ "Invalid Float size"
                                   , "exponent: " ++ show e
                                   , "precision: " ++ show p
                                   ]
  where
  ok = do eb <- rng expBits expBitsMin expBitsMax e
          pb <- rng precBits precBitsMin precBitsMax p
          pure (eb <> pb <> allowSubnormal <> rnd r)

  rng f a b x = if toInteger a <= x && x <= toInteger b
                  then Just (f (fromInteger x))
                  else Nothing



-- | Mapping from the rounding modes defined in the `Float.cry` to
-- the rounding modes of `LibBF`.
fpRound :: Integer -> Either EvalError RoundMode
fpRound n =
  case n of
    0 -> Right NearEven
    1 -> Right NearAway
    2 -> Right ToPosInf
    3 -> Right ToNegInf
    4 -> Right ToZero
    _ -> Left (BadRoundingMode n)

-- | Check that we didn't get an unexpected status.
fpCheckStatus :: (BigFloat,Status) -> BigFloat
fpCheckStatus (r,s) =
  case s of
    MemError  -> panic "checkStatus" [ "libBF: Memory error" ]
    _         -> r


-- | Pretty print a float
fpPP :: PPOpts -> BF -> Doc
fpPP opts bf =
  case bfSign num of
    Nothing -> "fpNaN"
    Just s
      | bfIsFinite num -> text hacStr
      | otherwise ->
        case s of
          Pos -> "fpPosInf"
          Neg -> "fpNegInf"
  where
  num = bfValue bf
  precW = bfPrecWidth bf

  base  = useFPBase opts

  withExp :: PPFloatExp -> ShowFmt -> ShowFmt
  withExp e f = case e of
                  AutoExponent -> f
                  ForceExponent -> f <> forceExp

  str = bfToString base fmt num
  fmt = addPrefix <> showRnd NearEven <>
        case useFPFormat opts of
          FloatFree e -> withExp e $ showFreeMin
                                   $ Just $ fromInteger precW
          FloatFixed n e -> withExp e $ showFixed $ fromIntegral n
          FloatFrac n    -> showFrac $ fromIntegral n

  -- non-base 10 literals are not overloaded so we add an explicit
  -- .0 if one is not present. 
  hacStr
    | base == 10 || elem '.' str = str
    | otherwise = case break (== 'p') str of
                    (xs,ys) -> xs ++ ".0" ++ ys


-- | Make a literal
fpLit ::
  Integer     {- ^ Exponent width -} ->
  Integer     {- ^ Precision width -} ->
  Rational ->
  BF
fpLit e p rat = floatFromRational e p NearEven rat

-- | Make a floating point number from a rational, using the given rounding mode
floatFromRational :: Integer -> Integer -> RoundMode -> Rational -> BF
floatFromRational e p r rat =
  BF { bfExpWidth = e
     , bfPrecWidth = p
     , bfValue = fpCheckStatus
                 if den == 1 then bfRoundFloat opts num
                             else bfDiv opts num (bfFromInteger den)
     }
  where
  opts  = fpOpts e p r

  num   = bfFromInteger (numerator rat)
  den   = denominator rat


-- | Convert a floating point number to a rational, if possible.
floatToRational :: String -> BF -> Either EvalError Rational
floatToRational fun bf =
  case bfToRep (bfValue bf) of
    BFNaN -> Left (BadValue fun)
    BFRep s num ->
      case num of
        Inf  -> Left (BadValue fun)
        Zero -> Right 0
        Num i ev -> Right case s of
                            Pos -> ab
                            Neg -> negate ab
          where ab = fromInteger i * (2 ^^ ev)


-- | Convert a floating point number to an integer, if possible.
floatToInteger :: String -> RoundMode -> BF -> Either EvalError Integer
floatToInteger fun r fp =
  do rat <- floatToRational fun fp
     pure case r of
            NearEven -> round rat
            NearAway -> if rat > 0 then ceiling rat else floor rat
            ToPosInf -> ceiling rat
            ToNegInf -> floor rat
            ToZero   -> truncate rat
            _        -> panic "fpCvtToInteger"
                              ["Unexpected rounding mode", show r]




floatFromBits :: 
  Integer {- ^ Exponent width -} ->
  Integer {- ^ Precision widht -} ->
  Integer {- ^ Raw bits -} ->
  BF
floatFromBits e p bv = BF { bfValue = floatFromBits' e p bv
                          , bfExpWidth = e, bfPrecWidth = p }



-- | Make a float using "raw" bits.
floatFromBits' ::
  Integer {- ^ Exponent width -} ->
  Integer {- ^ Precision widht -} ->
  Integer {- ^ Raw bits -} ->
  BigFloat

floatFromBits' e p bits
  | expoBiased == 0 && mant == 0 =            -- zero
    if isNeg then bfNegZero else bfPosZero

  | expoBiased == eMask && mant ==  0 =       -- infinity
    if isNeg then bfNegInf else bfPosInf

  | expoBiased == eMask = bfNaN               -- NaN

  | expoBiased == 0 =                         -- Subnormal
    case bfMul2Exp opts (bfFromInteger mant) (expoVal + 1) of
      (num,Ok) -> if isNeg then bfNeg num else num
      (_,s)    -> panic "floatFromBits" [ "Unexpected status: " ++ show s ]

  | otherwise =                               -- Normal
    case bfMul2Exp opts (bfFromInteger mantVal) expoVal of
      (num,Ok) -> if isNeg then bfNeg num else num
      (_,s)    -> panic "floatFromBits" [ "Unexpected status: " ++ show s ]

  where
  opts       = expBits e' <> precBits (p' + 1) <> allowSubnormal

  e'         = fromInteger e                               :: Int
  p'         = fromInteger p - 1                           :: Int
  eMask      = (1 `shiftL` e') - 1                         :: Int64
  pMask      = (1 `shiftL` p') - 1                         :: Integer

  isNeg      = testBit bits (e' + p')

  mant       = pMask .&. bits                              :: Integer
  mantVal    = mant `setBit` p'                            :: Integer
  -- accounts for the implicit 1 bit

  expoBiased = eMask .&. fromInteger (bits `shiftR` p')    :: Int64
  bias       = eMask `shiftR` 1                            :: Int64
  expoVal    = expoBiased - bias - fromIntegral p'         :: Int64


-- | Turn a float into raw bits.
-- @NaN@ is represented as a positive "quiet" @NaN@
-- (most significant bit in the significand is set, the rest of it is 0)
floatToBits :: Integer -> Integer -> BigFloat -> Integer
floatToBits e p bf =  (isNeg      `shiftL` (e' + p'))
                  .|. (expBiased  `shiftL` p')
                  .|. (mant       `shiftL` 0)
  where
  e' = fromInteger e     :: Int
  p' = fromInteger p - 1 :: Int

  eMask = (1 `shiftL` e') - 1   :: Integer
  pMask = (1 `shiftL` p') - 1   :: Integer

  (isNeg, expBiased, mant) =
    case bfToRep bf of
      BFNaN       -> (0,  eMask, 1 `shiftL` (p' - 1))
      BFRep s num -> (sign, be, ma)
        where
        sign = case s of
                Neg -> 1
                Pos -> 0

        (be,ma) =
          case num of
            Zero     -> (0,0)
            Num i ev
              | ex <= 0   -> (0, i `shiftL` (p' - m -1 + fromInteger ex))
              | otherwise -> (ex, (i `shiftL` (p' - m)) .&. pMask)
              where
              m    = msb 0 i - 1
              bias = eMask `shiftR` 1
              ex   = toInteger ev + bias + toInteger m

            Inf -> (eMask,0)

  msb !n j = if j == 0 then n else msb (n+1) (j `shiftR` 1)
