{-# Language BlockArguments #-}
module Cryptol.Eval.Concrete.FloatHelpers where

import Data.Ratio
import LibBF

import Cryptol.Utils.PP
import Cryptol.Utils.Panic(panic)
import Cryptol.Eval.Backend
import Cryptol.Eval.Monad( EvalError(..)
                         , PPOpts(..), PPFloatFormat(..), PPFloatExp(..)
                         )


data BF = BF
  { bfExpWidth  :: Integer
  , bfPrecWidth :: Integer
  , bfValue     :: BigFloat
  }


-- | Make LibBF options for the given precision and rounding mode.
fpOpts ::
  Backend sym =>
  sym           {- ^ backend -} ->
  Integer       {- ^ expoinent bits -} ->
  Integer       {- ^ precision bits -} ->
  Integer       {- ^ rounding mode, as defined in `Float.cry` -} ->
  SEval sym BFOpts
fpOpts sym e p r =
  case ok of
    Just opts -> case fpRound r of
                   Just m  -> pure (rnd m <> opts)
                   Nothing -> raiseError sym (BadRoundingMode r)
    Nothing   -> panic "floatOpts" [ "Invalid Float size"
                                   , "exponent: " ++ show e
                                   , "precision: " ++ show p
                                   ]
  where
  ok =
    do eb <- rng expBits expBitsMin expBitsMax e
       pb <- rng precBits precBitsMin precBitsMax p
       pure (eb <> pb <> allowSubnormal)

  rng f a b x = if toInteger a <= x && x <= toInteger b
                  then Just (f (fromInteger x))
                  else Nothing

-- | Mapping from the rounding modes defined in the `Float.cry` to
-- the rounding modes of `LibBF`.
fpRound :: Integer -> Maybe RoundMode
fpRound n =
  case n of
    0 -> Just NearEven
    1 -> Just NearAway
    2 -> Just ToPosInf
    3 -> Just ToNegInf
    4 -> Just ToZero
    _ -> Nothing


-- | Check that we didn't get an unexpected status.
fpCheckStatus :: Backend sym => sym -> (BigFloat,Status) -> SEval sym BigFloat
fpCheckStatus _sym (r,s) =
  case s of
    MemError  -> panic "checkStatus" [ "libBF: Memory error" ]
    _         -> pure r


-- | Pretty print a float
fpPP :: PPOpts -> BF -> Doc
fpPP opts bf = text $ bfToString base fmt num
  where
  num = bfValue bf
  precW = bfPrecWidth bf

  base  = useFPBase opts

  withExp :: PPFloatExp -> ShowFmt -> ShowFmt
  withExp e f = case e of
                  AutoExponent -> f
                  ForceExponent -> f <> forceExp

  fmt = addPrefix <> showRnd NearEven <>
        case useFPFormat opts of
          FloatFree e -> withExp e $ showFreeMin
                                   $ Just $ fromInteger precW
          FloatFixed n e -> withExp e $ showFixed $ fromIntegral n
          FloatFrac n    -> showFrac $ fromIntegral n



-- | Make a literal
fpLit ::
  Backend sym =>
  sym ->
  Integer     {- ^ Exponent width -} ->
  Integer     {- ^ Precision width -} ->
  Rational ->
  SEval sym BF
fpLit sym e p r =
  do opts <- fpOpts sym e p 0 -- round to nearest even
     let num = bfFromInteger (numerator r)
         res
           | denominator r == 1 = bfRoundFloat opts num
           | otherwise          = bfDiv opts num (bfFromInteger (denominator r))
     v <- fpCheckStatus sym res
     pure BF { bfExpWidth = e, bfPrecWidth = p, bfValue = v }


fpToI :: RoundMode -> BigFloat -> Maybe Integer
fpToI r flt =
  case bfToRep flt of
    BFNaN -> Nothing
    BFRep s num ->
      case num of
        Zero -> pure 0
        Inf  -> Nothing
        Num i ev ->
          pure
          case r of
            NearEven -> round $ addSign rat
            NearAway -> addSign $ ceiling rat
            ToPosInf -> ceiling $ addSign rat
            ToNegInf -> floor $ addSign rat
            ToZero   -> truncate rat
            _        -> panic "fpCvtToInteger"
                              ["Unexpected rounding mode", show r]
          where
          rat = fromInteger i * 2 ^^ ev :: Rational
          addSign :: Num a => a -> a
          addSign = case s of
                      Pos -> id
                      Neg -> negate




