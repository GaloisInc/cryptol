{-# LANGUAGE Safe #-}
-- | Useful information about various types.
module Cryptol.Utils.Types where

-- | Exponent and precision of 32-bit IEEE-754 floating point.
float32ExpPrec :: (Integer, Integer)
float32ExpPrec = (8, 24)

-- | Exponent and precision of 64-bit IEEE-754 floating point.
float64ExpPrec :: (Integer, Integer)
float64ExpPrec = (11, 53)
