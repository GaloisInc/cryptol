{-# Language BlockArguments #-}
{-# Language MultiWayIf #-}
{-# Language OverloadedStrings #-}
-- | Concrete evaluations for floating point primitives.
module Cryptol.Eval.Concrete.Float where

import Data.Map(Map)
import Data.Bits(testBit,setBit,shiftL,shiftR,(.&.))
import Data.Int(Int64)
import qualified Data.Map as Map
import LibBF

import Cryptol.Utils.Ident(Ident, floatPrimIdent)
import Cryptol.Eval.Value
import Cryptol.Eval.Concrete.FloatHelpers
import Cryptol.Eval.Concrete.Value

floatPrims :: Concrete -> Map Ident Value
floatPrims sym = Map.fromList [ (floatPrimIdent i,v) | (i,v) <- table ]
  where
  (~>) = (,)
  table =
    [ "fpNaN"     ~> ilam \_ -> ilam \_ -> VFloat bfNaN
    , "fpPosInf"  ~> ilam \_ -> ilam \_ -> VFloat bfPosInf
    , "fpNeg"     ~> ilam \_ -> ilam \_ -> flam \x -> pure $ VFloat $ bfNeg x
    , "fpFromBits" ~> fpFromBits sym

    , "fpAdd"     ~> binArith sym bfAdd
    , "fpSub"     ~> binArith sym bfSub
    , "fpMul"     ~> binArith sym bfMul
    , "fpDiv"     ~> binArith sym bfDiv
    ]

binArith ::
  Concrete ->
  (BFOpts -> BigFloat -> BigFloat -> (BigFloat, Status)) ->
  Value
binArith sym fun =
  ilam \e ->
  ilam \p ->
  wlam sym \r ->
  pure $ flam \x ->
  pure $ flam \y ->
  do opts <- floatOpts sym e p (bvVal r)
     VFloat <$> checkStatus sym (fun opts x y)

fpFromBits :: Concrete -> Value
fpFromBits sym =
  ilam \e ->
  ilam \p ->
  wlam sym \bv ->
  do opts <- floatOpts sym e p 0
     let bits       = bvVal bv
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


     VFloat <$>
       if -- zero
          | expoBiased == 0 && mant == 0 ->
            pure $ if isNeg then bfNegZero else bfPosZero

          -- infinity
          | expoBiased == eMask && mant ==  0 ->
            pure $ if isNeg then bfNegInf else bfPosInf

          -- NaN
          | expoBiased == eMask ->
            pure $ bfNaN

          -- A "normal" float
          | otherwise ->
            do num <- checkStatus sym
                        (bfMul2Exp opts (bfFromInteger mantVal) expoVal)

               pure (if isNeg then bfNeg num else num)


