module Cryptol.Eval.Concrete.FloatHelpers where

import LibBF

import Cryptol.Utils.Panic(panic)
import Cryptol.Eval.Backend
import Cryptol.Eval.Monad(EvalError(..))



floatOpts ::
  Backend sym =>
  sym           {- ^ backend -} ->
  Integer       {- ^ expoinent bits -} ->
  Integer       {- ^ precision bits -} ->
  Integer       {- ^ rounding mode, as defined in `Float.cry` -} ->
  SEval sym BFOpts
floatOpts sym e p r =
  case ok of
    Just opts -> case floatRound r of
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
       pure (eb <> pb)

  rng f a b x = if toInteger a <= x && x <= toInteger b
                  then Just (f (fromInteger x))
                  else Nothing

floatRound :: Integer -> Maybe RoundMode
floatRound n =
  case n of
    0 -> Just NearEven
    1 -> Just NearAway
    2 -> Just ToPosInf
    3 -> Just ToNegInf
    4 -> Just ToZero
    _ -> Nothing


checkStatus :: Backend sym => sym -> (BigFloat,Status) -> SEval sym BigFloat
checkStatus _sym (r,s) =
  case s of
    MemError  -> panic "checkStatus" [ "libBF: Memory error" ]
    -- InvalidOp -> panic "checkStatus" [ "libBF: Invalid op" ]
    _ -> pure r

