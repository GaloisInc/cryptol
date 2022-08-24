{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Cryptol.TypeCheck.Solver.Numeric.Sampling.Q' where

-- invariant: i /= 0 ==> q = 0
data Q' = Q'
  { q :: Rational,
    i :: Integer
  }

instance Show Q' where
  show Q' {..}
    | i == 1 && q == 0 = "i"
    | i == -1 && q == 0 = "-i"
    | i == 0 = show q
    | otherwise = "{malformed}(Q' " ++ show q ++ " " ++ show i ++ ")"

toQ' :: Rational -> Q'
toQ' q = Q' {q, i = 0}

fromQ' :: Q' -> Maybe Rational
fromQ' Q' {..}
  | i == 0 = Just q
  | otherwise = Nothing

normQ' :: Q' -> Q'
normQ' Q' {..} = Q' {q, i = signum i}

instance Num Q' where
  Q' q1 i1 + Q' q2 i2
    | signum i1 == signum i2 = normQ' $ Q' (q1 + q2) (i1 + i2)
    | otherwise = toQ' 0

  Q' q1 i1 * Q' q2 i2 = normQ' $ Q' (q1 + q2) (i1 + i2)

  abs Q' {..}
    | i == 0 = toQ' $ abs q
    | otherwise = toQ' $ fromInteger $ abs i

  signum Q' {..}
    | i == 0 = toQ' $ signum q
    | otherwise = toQ' $ fromInteger $ signum i

  fromInteger = toQ' . fromInteger

  negate q' = toQ' (-1) * q'
