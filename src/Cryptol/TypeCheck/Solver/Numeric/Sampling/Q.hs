{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Cryptol.TypeCheck.Solver.Numeric.Sampling.Q where

import Control.Monad (guard)
import GHC.Real

newtype Q = Q Rational
  deriving (Eq, Ord, Fractional)

toQ :: Real a => a -> Q
toQ = Q . toRational

denom :: Q -> Integer
denom (Q r) = denominator r

numer :: Q -> Integer
numer (Q r) = numerator r


instance Show Q where
  show (Q r)
    | denominator r == 1 = show (numerator r)
    | otherwise =
      concat
        ["(", show (numerator r), "/", show (denominator r), ")"]

instance Num Q where
  Q r1 + Q r2 = Q (r1 + r2)
  Q r1 * Q r2 = Q (r1 * r2)
  abs (Q r) = Q (abs r)
  signum (Q r) = Q (signum r)
  fromInteger = Q . fromInteger
  negate (Q r) = Q (negate r)

fromQ :: Integral a => Q -> Maybe a
fromQ (Q r) = do
  guard $ denominator r == 1
  pure . fromInteger . numerator $ r
