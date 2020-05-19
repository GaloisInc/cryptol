module Cryptol.Eval.Concrete.FloatHelpers where

import Cryptol.Eval.Backend
import Cryptol.Eval.Monad(EvalError(..))

import LibBF


floatOpts ::
  Backend sym =>
  sym           {- ^ backend -} ->
  Integer       {- ^ expoinent bits -} ->
  Integer       {- ^ precision bits -} ->
  Integer       {- ^ rounding mode, as defined in `Float.cry` -} ->
  SEval sym BFOpts
floatOpts sym e p r =
  case ok of
    Just opts -> pure opts
    Nothing   -> raiseError sym (BadFPParams e p r)
  where
  ok =
    do eb <- rng expBits expBitsMin expBitsMax e
       pb <- rng precBits precBitsMin precBitsMax p
       rn <- floatRound r
       pure (eb <> pb <> rnd rn)

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




