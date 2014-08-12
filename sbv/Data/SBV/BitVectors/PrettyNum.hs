-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.BitVectors.PrettyNum
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Number representations in hex/bin
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Data.SBV.BitVectors.PrettyNum (
        PrettyNum(..), readBin, shex, shexI, sbin, sbinI
      , showCFloat, showCDouble, showHFloat, showHDouble
      , showSMTFloat, showSMTDouble, smtRoundingMode
      ) where

import Data.Char  (ord)
import Data.Int   (Int8, Int16, Int32, Int64)
import Data.List  (isPrefixOf)
import Data.Maybe (fromJust)
import Data.Ratio (numerator, denominator)
import Data.Word  (Word8, Word16, Word32, Word64)
import Numeric    (showIntAtBase, showHex, readInt)

import Data.SBV.BitVectors.Data

-- | PrettyNum class captures printing of numbers in hex and binary formats; also supporting negative numbers.
--
-- Minimal complete definition: 'hexS' and 'binS'
class PrettyNum a where
  -- | Show a number in hexadecimal (starting with @0x@ and type.)
  hexS :: a -> String
  -- | Show a number in binary (starting with @0b@ and type.)
  binS :: a -> String
  -- | Show a number in hex, without prefix, or types.
  hex :: a -> String
  -- | Show a number in bin, without prefix, or types.
  bin :: a -> String

-- Why not default methods? Because defaults need "Integral a" but Bool is not..
instance PrettyNum Bool where
  {hexS = show; binS = show; hex = show; bin = show}
instance PrettyNum Word8 where
  {hexS = shex True True (False,8) ; binS = sbin True True (False,8) ; hex = shex False False (False,8) ; bin = sbin False False (False,8) ;}
instance PrettyNum Int8 where
  {hexS = shex True True (True,8)  ; binS = sbin True True (True,8)  ; hex = shex False False (True,8)  ; bin = sbin False False (True,8)  ;}
instance PrettyNum Word16 where
  {hexS = shex True True (False,16); binS = sbin True True (False,16); hex = shex False False (False,16); bin = sbin False False (False,16);}
instance PrettyNum Int16  where
  {hexS = shex True True (True,16);  binS = sbin True True (True,16) ; hex = shex False False (True,16);  bin = sbin False False (True,16) ;}
instance PrettyNum Word32 where
  {hexS = shex True True (False,32); binS = sbin True True (False,32); hex = shex False False (False,32); bin = sbin False False (False,32);}
instance PrettyNum Int32  where
  {hexS = shex True True (True,32);  binS = sbin True True (True,32) ; hex = shex False False (True,32);  bin = sbin False False (True,32) ;}
instance PrettyNum Word64 where
  {hexS = shex True True (False,64); binS = sbin True True (False,64); hex = shex False False (False,64); bin = sbin False False (False,64);}
instance PrettyNum Int64  where
  {hexS = shex True True (True,64);  binS = sbin True True (True,64) ; hex = shex False False (True,64);  bin = sbin False False (True,64) ;}
instance PrettyNum Integer where
  {hexS = shexI True True; binS = sbinI True True; hex = shexI False False; bin = sbinI False False;}

instance PrettyNum CW where
  hexS cw | cwIsBit cw         = hexS (cwToBool cw)
          | isReal cw          = let CWAlgReal w = cwVal cw in show w
          | not (isBounded cw) = let CWInteger w = cwVal cw in shexI True True w
          | isUninterpreted cw = show cw
          | True               = let CWInteger w = cwVal cw in shex  True True (hasSign cw, intSizeOf cw) w

  binS cw | cwIsBit cw         = binS (cwToBool cw)
          | isReal cw          = let CWAlgReal w = cwVal cw in show w
          | not (isBounded cw) = let CWInteger w = cwVal cw in sbinI True True w
          | isUninterpreted cw = show cw
          | True               = let CWInteger w = cwVal cw in sbin  True True (hasSign cw, intSizeOf cw) w

  hex cw | cwIsBit cw         = hexS (cwToBool cw)
         | isReal cw          = let CWAlgReal w = cwVal cw in show w
         | not (isBounded cw) = let CWInteger w = cwVal cw in shexI False False w
         | isUninterpreted cw = show cw
         | True               = let CWInteger w = cwVal cw in shex  False False (hasSign cw, intSizeOf cw) w

  bin cw | cwIsBit cw         = binS (cwToBool cw)
         | isReal cw          = let CWAlgReal w = cwVal cw in show w
         | not (isBounded cw) = let CWInteger w = cwVal cw in sbinI False False w
         | isUninterpreted cw = show cw
         | True               = let CWInteger w = cwVal cw in sbin  False False (hasSign cw, intSizeOf cw) w

instance (SymWord a, PrettyNum a) => PrettyNum (SBV a) where
  hexS s = maybe (show s) (hexS :: a -> String) $ unliteral s
  binS s = maybe (show s) (binS :: a -> String) $ unliteral s
  hex  s = maybe (show s) (hex  :: a -> String) $ unliteral s
  bin  s = maybe (show s) (bin  :: a -> String) $ unliteral s

-- | Show as a hexadecimal value. First bool controls whether type info is printed
-- while the second boolean controls wether 0x prefix is printed. The tuple is
-- the signedness and the bit-length of the input. The length of the string
-- will /not/ depend on the value, but rather the bit-length.
shex :: (Show a, Integral a) => Bool -> Bool -> (Bool, Int) -> a -> String
shex shType shPre (signed, size) a
 | a < 0
 = "-" ++ pre ++ pad l (s16 (abs (fromIntegral a :: Integer)))  ++ t
 | True
 = pre ++ pad l (s16 a) ++ t
 where t | shType = " :: " ++ (if signed then "Int" else "Word") ++ show size
         | True   = ""
       pre | shPre = "0x"
           | True  = ""
       l = (size + 3) `div` 4

-- | Show as a hexadecimal value, integer version. Almost the same as shex above
-- except we don't have a bit-length so the length of the string will depend
-- on the actual value.
shexI :: Bool -> Bool -> Integer -> String
shexI shType shPre a
 | a < 0
 = "-" ++ pre ++ s16 (abs a)  ++ t
 | True
 = pre ++ s16 a ++ t
 where t | shType = " :: Integer"
         | True   = ""
       pre | shPre = "0x"
           | True  = ""

-- | Similar to 'shex'; except in binary.
sbin :: (Show a, Integral a) => Bool -> Bool -> (Bool, Int) -> a -> String
sbin shType shPre (signed,size) a
 | a < 0
 = "-" ++ pre ++ pad size (s2 (abs (fromIntegral a :: Integer)))  ++ t
 | True
 = pre ++ pad size (s2 a) ++ t
 where t | shType = " :: " ++ (if signed then "Int" else "Word") ++ show size
         | True   = ""
       pre | shPre = "0b"
           | True  = ""

-- | Similar to 'shexI'; except in binary.
sbinI :: Bool -> Bool -> Integer -> String
sbinI shType shPre a
 | a < 0
 = "-" ++ pre ++ s2 (abs a) ++ t
 | True
 =  pre ++ s2 a ++ t
 where t | shType = " :: Integer"
         | True   = ""
       pre | shPre = "0b"
           | True  = ""

-- | Pad a string to a given length. If the string is longer, then we don't drop anything.
pad :: Int -> String -> String
pad l s = replicate (l - length s) '0' ++ s

-- | Binary printer
s2 :: (Show a, Integral a) => a -> String
s2  v = showIntAtBase 2 dig v "" where dig = fromJust . flip lookup [(0, '0'), (1, '1')]

-- | Hex printer
s16 :: (Show a, Integral a) => a -> String
s16 v = showHex v ""

-- | A more convenient interface for reading binary numbers, also supports negative numbers
readBin :: Num a => String -> a
readBin ('-':s) = -(readBin s)
readBin s = case readInt 2 isDigit cvt s' of
              [(a, "")] -> a
              _         -> error $ "SBV.readBin: Cannot read a binary number from: " ++ show s
  where cvt c = ord c - ord '0'
        isDigit = (`elem` "01")
        s' | "0b" `isPrefixOf` s = drop 2 s
           | True                = s

-- | A version of show for floats that generates correct C literals for nan/infinite. NB. Requires "math.h" to be included.
showCFloat :: Float -> String
showCFloat f
   | isNaN f             = "((float) NAN)"
   | isInfinite f, f < 0 = "((float) (-INFINITY))"
   | isInfinite f        = "((float) INFINITY)"
   | True                = show f ++ "F"

-- | A version of show for doubles that generates correct C literals for nan/infinite. NB. Requires "math.h" to be included.
showCDouble :: Double -> String
showCDouble f
   | isNaN f             = "((double) NAN)"
   | isInfinite f, f < 0 = "((double) (-INFINITY))"
   | isInfinite f        = "((double) INFINITY)"
   | True                = show f

-- | A version of show for floats that generates correct Haskell literals for nan/infinite
showHFloat :: Float -> String
showHFloat f
   | isNaN f             = "((0/0) :: Float)"
   | isInfinite f, f < 0 = "((-1/0) :: Float)"
   | isInfinite f        = "((1/0) :: Float)"
   | True                = show f

-- | A version of show for doubles that generates correct Haskell literals for nan/infinite
showHDouble :: Double -> String
showHDouble d
   | isNaN d             = "((0/0) :: Double)"
   | isInfinite d, d < 0 = "((-1/0) :: Double)"
   | isInfinite d        = "((1/0) :: Double)"
   | True                = show d

-- | A version of show for floats that generates correct SMTLib literals using the rounding mode
showSMTFloat :: RoundingMode -> Float -> String
showSMTFloat rm f
   | isNaN f             = as "NaN"
   | isInfinite f, f < 0 = as "minusInfinity"
   | isInfinite f        = as "plusInfinity"
   | isNegativeZero f    = "(- ((_ asFloat 8 24) " ++ smtRoundingMode rm ++ " (/ 0 1)))"
   | True                = "((_ asFloat 8 24) " ++ smtRoundingMode rm ++ " " ++ toSMTLibRational (toRational f) ++ ")"
   where as s = "(as " ++ s ++ " (_ FP 8 24))"

-- | A version of show for doubles that generates correct SMTLib literals using the rounding mode
showSMTDouble :: RoundingMode -> Double -> String
showSMTDouble rm d
   | isNaN d             = as "NaN"
   | isInfinite d, d < 0 = as "minusInfinity"
   | isInfinite d        = as "plusInfinity"
   | isNegativeZero d    = "(- ((_ asFloat 11 53) " ++ smtRoundingMode rm ++ " (/ 0 1)))"
   | True                = "((_ asFloat 11 53) " ++ smtRoundingMode rm ++ " " ++ toSMTLibRational (toRational d) ++ ")"
   where as s = "(as " ++ s ++ " (_ FP 11 53))"

-- | Show a rational in SMTLib format
toSMTLibRational :: Rational -> String
toSMTLibRational r
   | n < 0
   = "(- (/ "  ++ show (abs n) ++ " " ++ show d ++ "))"
   | True
   = "(/ " ++ show n ++ " " ++ show d ++ ")"
  where n = numerator r
        d = denominator r

-- | Convert a rounding mode to the format SMT-Lib2 understands.
smtRoundingMode :: RoundingMode -> String
smtRoundingMode RoundNearestTiesToEven = "roundNearestTiesToEven"
smtRoundingMode RoundNearestTiesToAway = "roundNearestTiesToAway"
smtRoundingMode RoundTowardPositive    = "roundTowardPositive"
smtRoundingMode RoundTowardNegative    = "roundTowardNegative"
smtRoundingMode RoundTowardZero        = "roundTowardZero"
