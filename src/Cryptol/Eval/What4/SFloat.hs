{-# Language DataKinds #-}
{-# Language FlexibleContexts #-}
{-# Language GADTs #-}
{-# Language TypeApplications #-}
{-# Language TypeOperators #-}
-- | Working with floats of dynamic sizes.
-- This should probably be moved to What4 one day.
module Cryptol.Eval.What4.SFloat where

import Control.Exception

import Data.Parameterized.Some
import Data.Parameterized.NatRepr

import What4.BaseTypes
import What4.Interface

-- | Symbolic floating point numbers.
data SFloat sym where
  SFloat :: SymExpr sym (BaseFloatType fpp) -> SFloat sym



--------------------------------------------------------------------------------

-- | This exception is thrown if the operations try to create a
-- floating point value we do not support
data UnsupportedFloat =
  UnsupportedFloat { fpWho :: String, exponentBits, precisionBits :: Integer }
  deriving Show

-- | Throw 'UnsupportedFloat' exception
unsupported ::
  String  {- ^ Label -} ->
  Integer {- ^ Exponent -} ->
  Integer {- ^ Precision -} ->
  IO a
unsupported l e p =
  throwIO UnsupportedFloat { fpWho         = l
                           , exponentBits  = e
                           , precisionBits = p }

instance Exception UnsupportedFloat


-- | Construct the 'FloatPrecisionRepr' with the given parameters.
fpRepr ::
  Integer {- ^ exponent -} ->
  Integer {- ^ precision -} ->
  Maybe (Some FloatPrecisionRepr)
fpRepr iE iP =
  do Some e    <- someNat iE
     LeqProof  <- testLeq (knownNat @2) e
     Some p    <- someNat iP
     LeqProof  <- testLeq (knownNat @2) p
     pure (Some (FloatingPointPrecisionRepr e p))

-- | Not a number
fpNaN ::
  IsExprBuilder sym =>
  sym ->
  Integer {- exponent -} ->
  Integer {- precision -} ->
  IO (SFloat sym)
fpNaN sym e p
  | Just (Some fpp) <- fpRepr e p = SFloat <$> floatNaN sym fpp
  | otherwise = unsupported "fpNaN" e p


-- | Positive infinity
fpPosInf ::
  IsExprBuilder sym =>
  sym ->
  Integer {- exponent -} ->
  Integer {- precision -} ->
  IO (SFloat sym)
fpPosInf sym e p
  | Just (Some fpp) <- fpRepr e p = SFloat <$> floatPInf sym fpp
  | otherwise = unsupported "fpPosInf" e p

fpFromRational ::
  IsExprBuilder sym =>
  sym ->
  Integer {- exponent -} ->
  Integer {- precision -} ->
  Rational ->
  IO (SFloat sym)
fpFromRational sym e p r
  | Just (Some fpp) <- fpRepr e p = SFloat <$> floatLit sym fpp r
  | otherwise = unsupported "fpFromRational" e p


