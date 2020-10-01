{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
module Cryptol.F2 where

import Data.Bits
import Cryptol.TypeCheck.Solver.InfNat (widthInteger)

pmult :: Int -> Integer -> Integer -> Integer
pmult w x y = go (w-1) 0
  where
    go !i !z
      | i >= 0    = go (i-1) (if testBit x i then (z `shiftL` 1) `xor` y else (z `shiftL` 1))
      | otherwise = z

pdiv :: Int -> Integer -> Integer -> Integer
pdiv w x m = go (w-1) 0 0
  where
    degree :: Int
    degree = fromInteger (widthInteger m - 1)

    reduce :: Integer -> Integer
    reduce u = if testBit u degree then u `xor` m else u
    {-# INLINE reduce #-}

    go !i !z !r
      | i >= 0    = go (i-1) z' r'
      | otherwise = r
     where
      zred = reduce z
      z'   = if testBit x  i      then (zred `shiftL` 1) .|. 1 else zred `shiftL` 1
      r'   = if testBit z' degree then (r    `shiftL` 1) .|. 1 else r    `shiftL` 1


pmod :: Int -> Integer -> Integer -> Integer
pmod w x m = mask .&. go 0 0 (reduce 1)
  where
    degree :: Int
    degree = fromInteger (widthInteger m - 1)

    reduce :: Integer -> Integer
    reduce u = if testBit u degree then u `xor` m else u
    {-# INLINE reduce #-}

    mask = bit degree - 1

    go !i !z !p
      | i < w     = go (i+1) (if testBit x i then z `xor` p else z) (reduce (p `shiftL` 1))
      | otherwise = z
