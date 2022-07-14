module Cryptol.TypeCheck.Solver.Numeric.Sampling.Q where

import GHC.Real
import Control.Monad (guard)

type Q = Rational

fromQ :: Integral a => Q -> Maybe a
fromQ q = do
  guard $ denominator q == 0
  pure . fromInteger . numerator $ q
