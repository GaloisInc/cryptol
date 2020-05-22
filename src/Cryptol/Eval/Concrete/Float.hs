{-# Language BlockArguments #-}
{-# Language OverloadedStrings #-}
{-# Language BangPatterns #-}
-- | Concrete evaluations for floating point primitives.
module Cryptol.Eval.Concrete.Float where

import Data.Map(Map)
import Data.Bits(testBit,setBit,shiftL,shiftR,(.&.),(.|.))
import Data.Int(Int64)
import qualified Data.Map as Map
import LibBF

import Cryptol.Utils.Ident(PrimIdent, floatPrim)
import Cryptol.Utils.Panic(panic)
import Cryptol.Eval.Value
import Cryptol.Eval.Generic
import Cryptol.Eval.Concrete.Value


floatPrims :: Concrete -> Map PrimIdent Value
floatPrims sym = Map.fromList [ (floatPrim i,v) | (i,v) <- nonInfixTable ]
  where
  (~>) = (,)
  nonInfixTable =
    [ "fpNaN"       ~> ilam \_ -> ilam \_ -> VFloat bfNaN
    , "fpPosInf"    ~> ilam \_ -> ilam \_ -> VFloat bfPosInf
    , "fpFromBits"  ~> ilam \e -> ilam \p -> wlam sym \bv ->
                       pure $ VFloat $ floatFromBits e p $ bvVal bv
    , "fpToBits"    ~> ilam \e -> ilam \p -> flam \x ->
                       pure $ word sym (e + p) (floatToBits e p x)
    , "=.="         ~> ilam \_ -> ilam \_ -> flam \x -> pure $ flam \y ->
                       pure $ VBit $ bitLit sym (bfCompare x y == EQ)

      -- From Backend class
    , "fpAdd"      ~> fpBinArithV sym fpPlus
    , "fpSub"      ~> fpBinArithV sym fpMinus
    , "fpMul"      ~> fpBinArithV sym fpMult
    , "fpDiv"      ~> fpBinArithV sym fpDiv
    ]


-- | Make a float using "raw" bits.
floatFromBits ::
  Integer {- ^ Exponent width -} ->
  Integer {- ^ Precision widht -} ->
  Integer {- ^ Raw bits -} ->
  BigFloat

floatFromBits e p bits
  | expoBiased == 0 && mant == 0 =            -- zero
    if isNeg then bfNegZero else bfPosZero

  | expoBiased == eMask && mant ==  0 =       -- infinity
    if isNeg then bfNegInf else bfPosInf

  | expoBiased == eMask = bfNaN               -- NaN

  | otherwise =                               -- A "normal" float
     case bfMul2Exp infPrec (bfFromInteger mantVal) expoVal of
       (num,Ok) -> if isNeg then bfNeg num else num
       (_,s) -> panic "floatFromBits" [ "Unexpected status: " ++ show s ]

  where
  e'         = fromInteger e                               :: Int
  p'         = fromInteger p - 1                           :: Int
  eMask      = (1 `shiftL` e') - 1                         :: Int64
  pMask      = (1 `shiftL` p') - 1                         :: Integer

  isNeg      = testBit bits (e' + p')

  mant       = pMask .&. bits                              :: Integer
  mantVal    = if expoBiased == 0
                 then mant
                 else mant `setBit` p'                     :: Integer
  -- accounts for the implicit 1 bit

  expoBiased = eMask .&. fromInteger (bits `shiftR` p')    :: Int64
  bias       = eMask `shiftR` 1                            :: Int64
  expoVal    = expoBiased - bias - fromIntegral p'         :: Int64


-- | Turn a float into raw bits.
-- @NaN@ is represented as a positive "quiet" @NaN@
-- (most significant bit in the significand is set, the rest of it is 0)
floatToBits :: Integer -> Integer -> BigFloat -> Integer
floatToBits e p bf =  (isNeg      `shiftL` (e' + p'))
                  .|. (expBiased  `shiftL` p')
                  .|. (mant       `shiftL` 0)
  where
  e' = fromInteger e     :: Int
  p' = fromInteger p - 1 :: Int

  eMask = (1 `shiftL` e') - 1   :: Integer
  pMask = (1 `shiftL` p') - 1   :: Integer

  (isNeg, expBiased, mant) =
    case bfToRep bf of
      BFNaN       -> (0,  eMask, 1 `shiftL` (p' - 1))
      BFRep s num -> (sign, be, ma)
        where
        sign = case s of
                Neg -> 1
                Pos -> 0

        (be,ma) =
          case num of
            Zero     -> (0,0)
            Num i ev ->
              let m    = msb 0 i - 1
                  bias = eMask `shiftR` 1
              in ( toInteger ev + toInteger m + bias
                 , (i `shiftL` (p' - m)) .&. pMask
                 )
            Inf     -> (eMask,0)

  msb !n j = if j == 0 then n else msb (n+1) (j `shiftR` 1)

