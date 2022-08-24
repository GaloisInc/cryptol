{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}

module Cryptol.TypeCheck.Solver.Numeric.Sampling.Z' where

-- invariant: i /= 0 ==> z = 0
data Z' = Z'
  { z :: Integer,
    i :: Integer
  }

instance Show Z' where
  show Z' {..}
    | i == 1 && z == 0 = "i"
    | i == -1 && z == 0 = "-i"
    | i == 0 = show z
    | otherwise = "{malformed}(Z' " ++ show z ++ " " ++ show i ++ ")"

toZ' :: Integer -> Z'
toZ' z = Z' {z, i = 0}

fromZ' :: Z' -> Maybe Integer
fromZ' Z' {..}
  | i == 0 = Just z
  | otherwise = Nothing

normZ' :: Z' -> Z'
normZ' Z' {..} = Z' {z, i = signum i}

instance Num Z' where
  Z' z1 i1 + Z' z2 i2
    | signum i1 == signum i2 = normZ' $ Z' (z1 + z2) (i1 + i2)
    | otherwise = toZ' 0

  Z' z1 i1 * Z' z2 i2 = normZ' $ Z' (z1 + z2) (i1 + i2)

  abs Z' {..}
    | i == 0 = toZ' $ abs z
    | otherwise = toZ' $ abs i

  signum Z' {..}
    | i == 0 = toZ' $ signum z
    | otherwise = toZ' $ signum i

  fromInteger = toZ'

  negate z' = toZ' (-1) * z'
