{-# Language BlockArguments #-}
{-# Language OverloadedStrings #-}
-- | Concrete evaluations for floating point primitives.
module Cryptol.Eval.Concrete.Float where

import Data.Map(Map)
import Data.Bits(testBit,setBit,shiftL,shiftR,(.&.))
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
    [ "fpNaN"     ~> ilam \_ -> ilam \_ -> VFloat bfNaN
    , "fpPosInf"  ~> ilam \_ -> ilam \_ -> VFloat bfPosInf
    , "fpNeg"     ~> ilam \_ -> ilam \_ -> flam \x -> pure $ VFloat $ bfNeg x
    , "fpFromBits" ~> ilam \e -> ilam \p -> wlam sym \bv ->
                        pure $ VFloat $ floatFromBits e p $ bvVal bv

      -- From Backend class
    , "fpAdd"     ~> fpBinArithV sym fpPlus
    , "fpSub"     ~> fpBinArithV sym fpMinus
    , "fpMul"     ~> fpBinArithV sym fpMult
    , "fpDiv"     ~> fpBinArithV sym fpDiv
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






