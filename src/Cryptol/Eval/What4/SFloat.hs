{-# Language DataKinds #-}
{-# Language FlexibleContexts #-}
{-# Language GADTs #-}
{-# Language RankNTypes #-}
{-# Language TypeApplications #-}
{-# Language TypeOperators #-}
-- | Working with floats of dynamic sizes.
-- This should probably be moved to What4 one day.
module Cryptol.Eval.What4.SFloat
  ( -- * Interface
    SFloat(..)
  , fpReprOf

    -- * Constants
  , fpFresh
  , fpNaN
  , fpPosInf
  , fpFromRational

    -- * Relations
  , SFloatRel
  , fpEqIEEE
  , fpLtIEEE
  , fpGtIEEE

    -- * Arithmetic
  , SFloatBinArith
  , fpNeg
  , fpAdd
  , fpSub
  , fpMul
  , fpDiv

  -- * Exceptions
  , UnsupportedFloat(..)
  , FPTypeError(..)
  ) where

import Control.Exception

import Data.Parameterized.Some
import Data.Parameterized.NatRepr

import What4.BaseTypes
import What4.Interface

-- | Symbolic floating point numbers.
data SFloat sym where
  SFloat :: IsExpr (SymExpr sym) => SymFloat sym fpp -> SFloat sym



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

-- | This exceptoin is throws if the types don't match.
data FPTypeError =
  FPTypeError { fpExpected :: Some FloatPrecisionRepr
              , fpActual   :: Some FloatPrecisionRepr
              }
    deriving Show

instance Exception FPTypeError

fpTypeError :: FloatPrecisionRepr t1 -> FloatPrecisionRepr t2 -> IO a
fpTypeError expect actual =
  throwIO FPTypeError { fpExpected = Some expect
                      , fpActual   = Some actual
                      }


--------------------------------------------------------------------------------
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

fpReprOf ::
  IsExpr (SymExpr sym) => sym -> SymFloat sym fpp -> FloatPrecisionRepr fpp
fpReprOf _ e =
  case exprType e of
    BaseFloatRepr r -> r


fpFresh ::
  IsSymExprBuilder sym =>
  sym ->
  Integer ->
  Integer ->
  IO (SFloat sym)
fpFresh sym e p
  | Just (Some fpp) <- fpRepr e p =
    SFloat <$> freshConstant sym emptySymbol (BaseFloatRepr fpp)
  | otherwise = unsupported "fpFresh" e p

-- | Not a number
fpNaN ::
  IsExprBuilder sym =>
  sym ->
  Integer {- ^ exponent -} ->
  Integer {- ^ precision -} ->
  IO (SFloat sym)
fpNaN sym e p
  | Just (Some fpp) <- fpRepr e p = SFloat <$> floatNaN sym fpp
  | otherwise = unsupported "fpNaN" e p


-- | Positive infinity
fpPosInf ::
  IsExprBuilder sym =>
  sym ->
  Integer {- ^ exponent -} ->
  Integer {- ^ precision -} ->
  IO (SFloat sym)
fpPosInf sym e p
  | Just (Some fpp) <- fpRepr e p = SFloat <$> floatPInf sym fpp
  | otherwise = unsupported "fpPosInf" e p

fpFromRational ::
  IsExprBuilder sym =>
  sym ->
  Integer {- ^ exponent -} ->
  Integer {- ^ precision -} ->
  Rational ->
  IO (SFloat sym)
fpFromRational sym e p r
  | Just (Some fpp) <- fpRepr e p = SFloat <$> floatLit sym fpp r
  | otherwise = unsupported "fpFromRational" e p

fpNeg :: IsExprBuilder sym => sym -> SFloat sym -> IO (SFloat sym)
fpNeg sym (SFloat fl) = SFloat <$> floatNeg sym fl


fpRel ::
  IsExprBuilder sym =>
  (forall t.
    sym ->
    SymFloat sym t ->
    SymFloat sym t ->
    IO (Pred sym)
  ) ->
  sym -> SFloat sym -> SFloat sym -> IO (Pred sym)
fpRel fun sym (SFloat x) (SFloat y) =
  let t1 = sym `fpReprOf` x
      t2 = sym `fpReprOf` y
  in
  case testEquality t1 t2 of
    Just Refl -> fun sym x y
    _         -> fpTypeError t1 t2

fpBinArith ::
  IsExprBuilder sym =>
  (forall t.
      sym ->
      RoundingMode ->
      SymFloat sym t ->
      SymFloat sym t ->
      IO (SymFloat sym t)
  ) ->
  sym -> RoundingMode -> SFloat sym -> SFloat sym -> IO (SFloat sym)
fpBinArith fun sym r (SFloat x) (SFloat y) =
  let t1 = sym `fpReprOf` x
      t2 = sym `fpReprOf` y
  in
  case testEquality t1 t2 of
    Just Refl -> SFloat <$> fun sym r x y
    _         -> fpTypeError t1 t2

type SFloatBinArith sym =
  sym -> RoundingMode -> SFloat sym -> SFloat sym -> IO (SFloat sym)

fpAdd :: IsExprBuilder sym => SFloatBinArith sym
fpAdd = fpBinArith floatAdd

fpSub :: IsExprBuilder sym => SFloatBinArith sym
fpSub = fpBinArith floatSub

fpMul :: IsExprBuilder sym => SFloatBinArith sym
fpMul = fpBinArith floatMul

fpDiv :: IsExprBuilder sym => SFloatBinArith sym
fpDiv = fpBinArith floatDiv


type SFloatRel sym =
  sym -> SFloat sym -> SFloat sym -> IO (Pred sym)

fpEqIEEE :: IsExprBuilder sym => SFloatRel sym
fpEqIEEE = fpRel floatFpEq

fpLtIEEE :: IsExprBuilder sym => SFloatRel sym
fpLtIEEE = fpRel floatLt

fpGtIEEE :: IsExprBuilder sym => SFloatRel sym
fpGtIEEE = fpRel floatGt




