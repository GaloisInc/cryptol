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
  , fpSize
  , fpRepr

    -- * Constants
  , fpFresh
  , fpNaN
  , fpPosInf
  , fpFromRationalLit

    -- * Interchange formats
  , fpFromBinary
  , fpToBinary

    -- * Relations
  , SFloatRel
  , fpEq
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

    -- * Conversions
  , fpRound
  , fpToReal
  , fpFromReal
  , fpFromRational
  , fpToRational
  , fpFromInteger

    -- * Queries
  , fpIsInf, fpIsNaN

  -- * Exceptions
  , UnsupportedFloat(..)
  , FPTypeError(..)
  ) where

import Control.Exception

import Data.Parameterized.Some
import Data.Parameterized.NatRepr

import What4.BaseTypes
import What4.Panic(panic)
import What4.SWord
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
  Integer {- ^ Exponent width -} ->
  Integer {- ^ Precision width -} ->
  IO a
unsupported l e p =
  throwIO UnsupportedFloat { fpWho         = l
                           , exponentBits  = e
                           , precisionBits = p }

instance Exception UnsupportedFloat

-- | This exceptoin is throws if the types don't match.
data FPTypeError =
  FPTypeError { fpExpected :: Some BaseTypeRepr
              , fpActual   :: Some BaseTypeRepr
              }
    deriving Show

instance Exception FPTypeError

fpTypeMismatch :: BaseTypeRepr t1 -> BaseTypeRepr t2 -> IO a
fpTypeMismatch expect actual =
  throwIO FPTypeError { fpExpected = Some expect
                      , fpActual   = Some actual
                      }
fpTypeError :: FloatPrecisionRepr t1 -> FloatPrecisionRepr t2 -> IO a
fpTypeError t1 t2 =
  fpTypeMismatch (BaseFloatRepr t1) (BaseFloatRepr t2)


--------------------------------------------------------------------------------
-- | Construct the 'FloatPrecisionRepr' with the given parameters.
fpRepr ::
  Integer {- ^ Exponent width -} ->
  Integer {- ^ Precision width -} ->
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

fpSize :: SFloat sym -> (Integer,Integer)
fpSize (SFloat f) =
  case exprType f of
    BaseFloatRepr (FloatingPointPrecisionRepr e p) -> (intValue e, intValue p)


--------------------------------------------------------------------------------
-- Constants

-- | A fresh variable of the given type.
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
  Integer {- ^ Exponent width -} ->
  Integer {- ^ Precision width -} ->
  IO (SFloat sym)
fpNaN sym e p
  | Just (Some fpp) <- fpRepr e p = SFloat <$> floatNaN sym fpp
  | otherwise = unsupported "fpNaN" e p


-- | Positive infinity
fpPosInf ::
  IsExprBuilder sym =>
  sym ->
  Integer {- ^ Exponent width -} ->
  Integer {- ^ Precision width -} ->
  IO (SFloat sym)
fpPosInf sym e p
  | Just (Some fpp) <- fpRepr e p = SFloat <$> floatPInf sym fpp
  | otherwise = unsupported "fpPosInf" e p

-- | A floating point number corresponding to the given rations.
fpFromRationalLit ::
  IsExprBuilder sym =>
  sym ->
  Integer {- ^ Exponent width -} ->
  Integer {- ^ Precision width -} ->
  Rational ->
  IO (SFloat sym)
fpFromRationalLit sym e p r
  | Just (Some fpp) <- fpRepr e p = SFloat <$> floatLit sym fpp r
  | otherwise = unsupported "fpFromRational" e p


-- | Make a floating point number with the given bit representation.
fpFromBinary ::
  IsExprBuilder sym =>
  sym ->
  Integer {- ^ Exponent width -} ->
  Integer {- ^ Precision width -} ->
  SWord sym ->
  IO (SFloat sym)
fpFromBinary sym e p swe
  | DBV sw <- swe
  , Just (Some fpp) <- fpRepr e p
  , FloatingPointPrecisionRepr ew pw <- fpp
  , let expectW = addNat ew pw
  , actual@(BaseBVRepr actualW)  <- exprType sw =
    case testEquality expectW actualW of
      Just Refl -> SFloat <$> floatFromBinary sym fpp sw
      Nothing -- we want to report type correct type errors! :-)
        | Just LeqProof <- testLeq (knownNat @1) expectW ->
                fpTypeMismatch (BaseBVRepr expectW) actual
        | otherwise -> panic "fpFromBits" [ "1 >= 2" ]
  | otherwise = unsupported "fpFromBits" e p

fpToBinary :: IsExprBuilder sym => sym -> SFloat sym -> IO (SWord sym)
fpToBinary sym (SFloat f)
  | FloatingPointPrecisionRepr e p <- fpReprOf sym f
  , Just LeqProof <- testLeq (knownNat @1) (addNat e p)
    = DBV <$> floatToBinary sym f
  | otherwise = panic "fpToBinary" [ "we messed up the types" ]


--------------------------------------------------------------------------------
-- Arithmetic

fpNeg :: IsExprBuilder sym => sym -> SFloat sym -> IO (SFloat sym)
fpNeg sym (SFloat fl) = SFloat <$> floatNeg sym fl

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




--------------------------------------------------------------------------------

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




type SFloatRel sym =
  sym -> SFloat sym -> SFloat sym -> IO (Pred sym)

fpEq :: IsExprBuilder sym => SFloatRel sym
fpEq = fpRel floatEq

fpEqIEEE :: IsExprBuilder sym => SFloatRel sym
fpEqIEEE = fpRel floatFpEq

fpLtIEEE :: IsExprBuilder sym => SFloatRel sym
fpLtIEEE = fpRel floatLt

fpGtIEEE :: IsExprBuilder sym => SFloatRel sym
fpGtIEEE = fpRel floatGt


--------------------------------------------------------------------------------
fpRound ::
  IsExprBuilder sym => sym -> RoundingMode -> SFloat sym -> IO (SFloat sym)
fpRound sym r (SFloat x) = SFloat <$> floatRound sym r x

-- | This is undefined on "special" values (NaN,infinity)
fpToReal :: IsExprBuilder sym => sym -> SFloat sym -> IO (SymReal sym)
fpToReal sym (SFloat x) = floatToReal sym x

fpFromReal ::
  IsExprBuilder sym =>
  sym -> Integer -> Integer -> RoundingMode -> SymReal sym -> IO (SFloat sym)
fpFromReal sym e p r x
  | Just (Some repr) <- fpRepr e p = SFloat <$> realToFloat sym repr r x
  | otherwise = unsupported "fpFromReal" e p


fpFromInteger ::
  IsExprBuilder sym =>
  sym -> Integer -> Integer -> RoundingMode -> SymInteger sym -> IO (SFloat sym)
fpFromInteger sym e p r x = fpFromReal sym e p r =<< integerToReal sym x


fpFromRational ::
  IsExprBuilder sym =>
  sym -> Integer -> Integer -> RoundingMode ->
  SymInteger sym -> SymInteger sym -> IO (SFloat sym)
fpFromRational sym e p r x y =
  do num <- integerToReal sym x
     den <- integerToReal sym y
     res <- realDiv sym num den
     fpFromReal sym e p r res

{- | Returns a predicate and two integers, @x@ and @y@.
If the the predicate holds, then @x / y@ is a rational representing
the floating point number. Assumes the FP number is not one of the
special ones that has no real representation. -}
fpToRational ::
  IsSymExprBuilder sym =>
  sym ->
  SFloat sym ->
  IO (Pred sym, SymInteger sym, SymInteger sym)
fpToRational sym fp =
  do r    <- fpToReal sym fp
     x    <- freshConstant sym emptySymbol BaseIntegerRepr
     y    <- freshConstant sym emptySymbol BaseIntegerRepr
     num  <- integerToReal sym x
     den  <- integerToReal sym y
     res  <- realDiv sym num den
     same <- realEq sym r res
     pure (same, x, y)



--------------------------------------------------------------------------------
fpIsInf :: IsExprBuilder sym => sym -> SFloat sym -> IO (Pred sym)
fpIsInf sym (SFloat x) = floatIsInf sym x

fpIsNaN :: IsExprBuilder sym => sym -> SFloat sym -> IO (Pred sym)
fpIsNaN sym (SFloat x) = floatIsNaN sym x



