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

data SFloat sym where
  SFloat ::
    (IsExpr (SymExpr sym)) =>
    SymExpr sym (BaseFloatType fpp) ->
    SFloat sym

data UnsupportedFloat =
  UnsupportedFloat { exponentBits, precisionBits :: Integer }
  deriving Show

instance Exception UnsupportedFloat


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

fpNaN ::
  IsExprBuilder sym =>
  sym ->
  Integer {- exponent -} ->
  Integer {- precision -} ->
  IO (SFloat sym)
fpNaN sym e p
  | Just (Some fpp) <- fpRepr e p = SFloat <$> floatNaN sym fpp
  | otherwise = throwIO UnsupportedFloat { exponentBits = e
                                         , precisionBits = p
                                         }

