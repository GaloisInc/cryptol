-- |
-- Module      :  Cryptol.Backend.SBV
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
module Cryptol.Backend.SBV
  ( SBV(..), SBVEval(..), SBVResult(..)
  , literalSWord
  , freshSBool_
  , freshBV_
  , freshSInteger_
  , freshSFloat_
  , addDefEqn
  , ashr
  , lshr
  , shl
  , evalPanic
  , svFromInteger
  , svToInteger
  ) where

import qualified Control.Exception as X
import           Control.Concurrent.MVar
import           Control.Monad.IO.Class (MonadIO(..))
import           Data.Bits (bit, complement, shiftL)
import           Data.List (foldl')
import           Data.Ratio ((%), numerator, denominator)
import           LibBF (BigFloat, BFOpts, RoundMode, Status)
import qualified LibBF as BF

import qualified GHC.Num.Compat as Integer

import Data.SBV.Dynamic as SBV
import qualified Data.SBV.Float as SBV
import qualified Data.SBV.Internals as SBV

import Cryptol.Backend
import Cryptol.Backend.Concrete ( integerToChar )
import Cryptol.Backend.FloatHelpers (BF(..), fpCheckStatus, fpOpts)
import Cryptol.Backend.Monad
  ( Eval(..), blackhole, delayFill, evalSpark
  , EvalError(..), EvalErrorEx(..), Unsupported(..)
  , modifyCallStack, getCallStack, maybeReady
  )

import Cryptol.Utils.Panic (panic)

data SBV =
  SBV
  { sbvStateVar     :: MVar (SBV.State)
  , sbvDefRelations :: MVar SVal
  }

-- Utility operations -------------------------------------------------------------

fromBitsLE :: [SBit SBV] -> SWord SBV
fromBitsLE bs = foldl' f (literalSWord 0 0) bs
  where f w b = svJoin (svToWord1 b) w

packSBV :: [SBit SBV] -> SWord SBV
packSBV bs = fromBitsLE (reverse bs)

unpackSBV :: SWord SBV -> [SBit SBV]
unpackSBV x = [ svTestBit x i | i <- reverse [0 .. intSizeOf x - 1] ]

literalSWord :: Int -> Integer -> SWord SBV
literalSWord w i = svInteger (KBounded False w) i

svMkSymVar_ :: Maybe Quantifier -> Kind -> Maybe String -> SBV.State -> IO SVal
#if MIN_VERSION_sbv(8,8,0)
svMkSymVar_ = svMkSymVar . SBV.NonQueryVar
#else
svMkSymVar_ = svMkSymVar
#endif

freshBV_ :: SBV -> Int -> IO (SWord SBV)
freshBV_ (SBV stateVar _) w =
  withMVar stateVar (svMkSymVar_ Nothing (KBounded False w) Nothing)

freshSBool_ :: SBV -> IO (SBit SBV)
freshSBool_ (SBV stateVar _) =
  withMVar stateVar (svMkSymVar_ Nothing KBool Nothing)

freshSInteger_ :: SBV -> IO (SInteger SBV)
freshSInteger_ (SBV stateVar _) =
  withMVar stateVar (svMkSymVar_ Nothing KUnbounded Nothing)

freshSFloat_ :: SBV -> Integer -> Integer -> IO (SFloat SBV)
freshSFloat_ (SBV stateVar _) e p =
  withMVar stateVar (svMkSymVar_ Nothing (KFP e' p') Nothing)
    where
      (e', p') = fpExpAndPrec e p


-- SBV Evaluation monad -------------------------------------------------------

data SBVResult a
  = SBVError !EvalErrorEx
  | SBVResult !SVal !a -- safety predicate and result

instance Functor SBVResult where
  fmap _ (SBVError err) = SBVError err
  fmap f (SBVResult p x) = SBVResult p (f x)

instance Applicative SBVResult where
  pure = SBVResult svTrue
  SBVError err <*> _ = SBVError err
  _ <*> SBVError err = SBVError err
  SBVResult p1 f <*> SBVResult p2 x = SBVResult (svAnd p1 p2) (f x)

instance Monad SBVResult where
  return = pure
  SBVError err >>= _ = SBVError err
  SBVResult px x >>= m =
    case m x of
      SBVError err   -> SBVError err
      SBVResult pm z -> SBVResult (svAnd px pm) z

newtype SBVEval a = SBVEval{ sbvEval :: Eval (SBVResult a) }
  deriving (Functor)

instance Applicative SBVEval where
  pure = SBVEval . pure . pure
  f <*> x = SBVEval $
    do f' <- sbvEval f
       x' <- sbvEval x
       pure (f' <*> x')

instance Monad SBVEval where
  return = pure
  x >>= f = SBVEval $
    sbvEval x >>= \case
      SBVError err -> pure (SBVError err)
      SBVResult px x' ->
        sbvEval (f x') >>= \case
          SBVError err -> pure (SBVError err)
          SBVResult pz z -> pure (SBVResult (svAnd px pz) z)

instance MonadIO SBVEval where
  liftIO m = SBVEval $ fmap pure (liftIO m)


addDefEqn :: SBV -> SVal -> IO ()
addDefEqn (SBV _ relsVar) b = modifyMVar_ relsVar (pure . svAnd b)

-- Symbolic Big-endian Words -------------------------------------------------------

instance Backend SBV where
  type SBit SBV = SVal
  type SWord SBV = SVal
  type SInteger SBV = SVal
  type SFloat SBV = SVal
  type SEval SBV = SBVEval

  raiseError _ err = SBVEval $
    do stk <- getCallStack
       pure (SBVError (EvalErrorEx stk err))

  assertSideCondition sym cond err
    | Just False <- svAsBool cond = raiseError sym err
    | otherwise = SBVEval (pure (SBVResult cond ()))

  isReady _ (SBVEval m) = SBVEval $
    maybeReady m >>= \case
      Just x  -> pure (Just <$> x)
      Nothing -> pure (pure Nothing)

  sDelayFill _ m retry msg = SBVEval $
    do m' <- delayFill (sbvEval m) (sbvEval <$> retry) msg
       pure (pure (SBVEval m'))

  sSpark _ m = SBVEval $
    do m' <- evalSpark (sbvEval m)
       pure (pure (SBVEval m'))

  sDeclareHole _ msg = SBVEval $
    do (hole, fill) <- blackhole msg
       pure (pure (SBVEval hole, \m -> SBVEval (fmap pure $ fill (sbvEval m))))

  sModifyCallStack _ f (SBVEval m) = SBVEval $
    modifyCallStack f m

  sGetCallStack _ = SBVEval (pure <$> getCallStack)

  mergeEval _sym f c mx my = SBVEval $
    do rx <- sbvEval mx
       ry <- sbvEval my
       case (rx, ry) of
         (SBVError err, SBVError _) ->
           pure $ SBVError err -- arbitrarily choose left error to report
         (SBVError _, SBVResult p y) ->
           pure $ SBVResult (svAnd (svNot c) p) y
         (SBVResult p x, SBVError _) ->
           pure $ SBVResult (svAnd c p) x
         (SBVResult px x, SBVResult py y) ->
           do zr <- sbvEval (f c x y)
              case zr of
                SBVError err -> pure $ SBVError err
                SBVResult pz z ->
                  pure $ SBVResult (svAnd (svIte c px py) pz) z

  wordLen' _ v = toInteger (intSizeOf v)
  {-# INLINE wordLen' #-}
  wordAsChar _ v = integerToChar <$> svAsInteger v

  iteBit _ b x y = pure $! svSymbolicMerge KBool True b x y
  iteWord _ b x y = pure $! svSymbolicMerge (kindOf x) True b x y
  iteInteger _ b x y = pure $! svSymbolicMerge KUnbounded True b x y

  bitAsLit _ b = svAsBool b
  wordAsLit _ w =
    case svAsInteger w of
      Just x -> Just (toInteger (intSizeOf w), x)
      Nothing -> Nothing
  integerAsLit _ v = svAsInteger v

  bitLit _ b     = svBool b
  wordLit _ n x  = pure $! literalSWord (fromInteger n) x
  integerLit _ x = pure $! svInteger KUnbounded x

  bitEq  _ x y = pure $! svEqual x y
  bitOr  _ x y = pure $! svOr x y
  bitAnd _ x y = pure $! svAnd x y
  bitXor _ x y = pure $! svXOr x y
  bitComplement _ x = pure $! svNot x

  wordBit _ x idx = pure $! svTestBit x (intSizeOf x - 1 - fromInteger idx)

  wordUpdate _ x idx b = pure $! svSymbolicMerge (kindOf x) False b wtrue wfalse
    where
     i' = intSizeOf x - 1 - fromInteger idx
     wtrue  = x `svOr`  svInteger (kindOf x) (bit i' :: Integer)
     wfalse = x `svAnd` svInteger (kindOf x) (complement (bit i' :: Integer))

  packWord _ bs  = pure $! packSBV bs
  unpackWord _ x = pure $! unpackSBV x

  wordEq _ x y = pure $! svEqual x y
  wordLessThan _ x y = pure $! svLessThan x y
  wordGreaterThan _ x y = pure $! svGreaterThan x y

  wordSignedLessThan _ x y = pure $! svLessThan sx sy
    where sx = svSign x
          sy = svSign y

  joinWord _ x y = pure $! svJoin x y

  splitWord _ _leftW rightW w = pure
    ( svExtract (intSizeOf w - 1) (fromInteger rightW) w
    , svExtract (fromInteger rightW - 1) 0 w
    )

  extractWord _ len start w =
    pure $! svExtract (fromInteger start + fromInteger len - 1) (fromInteger start) w

  wordAnd _ a b = pure $! svAnd a b
  wordOr  _ a b = pure $! svOr a b
  wordXor _ a b = pure $! svXOr a b
  wordComplement _ a = pure $! svNot a

  wordPlus  _ a b = pure $! svPlus a b
  wordMinus _ a b = pure $! svMinus a b
  wordMult  _ a b = pure $! svTimes a b
  wordNegate _ a  = pure $! svUNeg a

  wordShiftLeft _ a b   = pure $! shl a b
  wordShiftRight _ a b  = pure $! lshr a b
  wordRotateLeft _ a b  = pure $! SBV.svRotateLeft a b
  wordRotateRight _ a b = pure $! SBV.svRotateRight a b
  wordSignedShiftRight _ a b = pure $! ashr a b

  wordDiv sym a b =
    do let z = literalSWord (intSizeOf b) 0
       assertSideCondition sym (svNot (svEqual b z)) DivideByZero
       pure $! svQuot a b

  wordMod sym a b =
    do let z = literalSWord (intSizeOf b) 0
       assertSideCondition sym (svNot (svEqual b z)) DivideByZero
       pure $! svRem a b

  wordSignedDiv sym a b =
    do let z = literalSWord (intSizeOf b) 0
       assertSideCondition sym (svNot (svEqual b z)) DivideByZero
       pure $! signedQuot a b

  wordSignedMod sym a b =
    do let z = literalSWord (intSizeOf b) 0
       assertSideCondition sym (svNot (svEqual b z)) DivideByZero
       pure $! signedRem a b

  wordLg2 _ a = sLg2 a

  wordToInt _ x = pure $! svToInteger x
  wordToSignedInt _ x = pure $! svToInteger (svSign x)
  wordFromInt _ w i = pure $! svFromInteger w i

  intEq _ a b = pure $! svEqual a b
  intLessThan _ a b = pure $! svLessThan a b
  intGreaterThan _ a b = pure $! svGreaterThan a b

  intPlus  _ a b = pure $! svPlus a b
  intMinus _ a b = pure $! svMinus a b
  intMult  _ a b = pure $! svTimes a b
  intNegate _ a  = pure $! SBV.svUNeg a

  intDiv sym a b =
    do let z = svInteger KUnbounded 0
       assertSideCondition sym (svNot (svEqual b z)) DivideByZero
       let p = svLessThan z b
       pure $! svSymbolicMerge KUnbounded True p (svQuot a b) (svQuot (svUNeg a) (svUNeg b))
  intMod sym a b =
    do let z = svInteger KUnbounded 0
       assertSideCondition sym (svNot (svEqual b z)) DivideByZero
       let p = svLessThan z b
       pure $! svSymbolicMerge KUnbounded True p (svRem a b) (svUNeg (svRem (svUNeg a) (svUNeg b)))

  -- NB, we don't do reduction here
  intToZn _ _m a = pure a

  znToInt _ 0 _ = evalPanic "znToInt" ["0 modulus not allowed"]
  znToInt _ m a =
    do let m' = svInteger KUnbounded m
       pure $! svRem a m'

  znEq _ 0 _ _ = evalPanic "znEq" ["0 modulus not allowed"]
  znEq sym m a b = svDivisible sym m (SBV.svMinus a b)

  znPlus  sym m a b = sModAdd sym m a b
  znMinus sym m a b = sModSub sym m a b
  znMult  sym m a b = sModMult sym m a b
  znNegate sym m a  = sModNegate sym m a
  znRecip = sModRecip

  fpAsLit _                 = fmap fpToBF . svAsFP
  iteFloat _ b x y          = pure $! svSymbolicMerge (kindOf x) True b x y
  fpNaN _ e p               = pure $! svFPNaN e p
  fpPosInf _ e p            = pure $! svFPInf False e p
  fpExactLit _ bf           = pure $! svFloatingPoint (fpFromBF bf)
  fpLit _ e p r             = pure $! svFPFromRationalLit e p r
  fpLogicalEq _ a b         = pure $! svStrongEqual a b
  fpEq _ a b                = pure $! svEqual a b
  fpLessThan _ a b          = pure $! svLessThan a b
  fpGreaterThan _ a b       = pure $! svGreaterThan a b
  fpPlus sym r a b          = do m <- fpRoundingMode sym r
                                 pure $! svFPPlus m a b
  fpMinus sym r a b         = do m <- fpRoundingMode sym r
                                 pure $! svFPSub m a b
  fpMult sym r a b          = do m <- fpRoundingMode sym r
                                 pure $! svFPMul m a b
  fpDiv sym r a b           = do m <- fpRoundingMode sym r
                                 pure $! svFPDiv m a b
  fpAbs _ a                 = pure $! svFPAbs a
  fpSqrt sym r a            = do m <- fpRoundingMode sym r
                                 pure $! svFPSqrt m a
  fpFMA sym r a b c         = do m <- fpRoundingMode sym r
                                 pure $! svFPFMA m a b c
  fpNeg _ a                 = pure $! svFPNeg a
  fpFromInteger sym e p r a = do m <- fpRoundingMode sym r
                                 pure $! svFPFromInteger e p m a
  fpToInteger               = fpCvtToInteger
  fpIsZero _ a              = pure $! svFPIsZero a
  fpIsInf _ a               = pure $! svFPIsInfinite a
  fpIsNeg _ a               = pure $! svFPIsNegative a
  fpIsNaN _ a               = pure $! svFPIsNaN a
  fpIsNorm _ a              = pure $! svFPIsNormal a
  fpIsSubnorm _ a           = pure $! svFPIsSubnormal a
  fpToBits sym a            = fpCvtToBits sym a
  fpFromBits _ e p a        = pure $! svFPFromBits e p a
  fpToRational sym a        = fpCvtToRational sym a
  fpFromRational sym e p r a = do m <- fpRoundingMode sym r
                                  pure $! svFPFromRational e p m a


svToInteger :: SWord SBV -> SInteger SBV
svToInteger w =
  case svAsInteger w of
    Nothing -> svFromIntegral KUnbounded w
    Just x  -> svInteger KUnbounded x

svFromInteger :: Integer -> SInteger SBV -> SWord SBV
svFromInteger 0 _ = literalSWord 0 0
svFromInteger n i =
  case svAsInteger i of
    Nothing -> svFromIntegral (KBounded False (fromInteger n)) i
    Just x  -> literalSWord (fromInteger n) x

-- Errors ----------------------------------------------------------------------

evalPanic :: String -> [String] -> a
evalPanic cxt = panic ("[SBV] " ++ cxt)


sModAdd :: SBV -> Integer -> SInteger SBV -> SInteger SBV -> SEval SBV (SInteger SBV)
sModAdd _ 0 _ _ = evalPanic "sModAdd" ["0 modulus not allowed"]
sModAdd sym modulus x y =
  case (SBV.svAsInteger x, SBV.svAsInteger y) of
    (Just i, Just j) -> integerLit sym ((i + j) `mod` modulus)
    _                -> pure $ SBV.svPlus x y

sModSub :: SBV -> Integer -> SInteger SBV -> SInteger SBV -> SEval SBV (SInteger SBV)
sModSub _ 0 _ _ = evalPanic "sModSub" ["0 modulus not allowed"]
sModSub sym modulus x y =
  case (SBV.svAsInteger x, SBV.svAsInteger y) of
    (Just i, Just j) -> integerLit sym ((i - j) `mod` modulus)
    _                -> pure $ SBV.svMinus x y

sModNegate :: SBV -> Integer -> SInteger SBV -> SEval SBV (SInteger SBV)
sModNegate _ 0 _ = evalPanic "sModNegate" ["0 modulus not allowed"]
sModNegate sym modulus x =
  case SBV.svAsInteger x of
    Just i -> integerLit sym ((negate i) `mod` modulus)
    _      -> pure $ SBV.svUNeg x

sModMult :: SBV -> Integer -> SInteger SBV -> SInteger SBV -> SEval SBV (SInteger SBV)
sModMult _ 0 _ _ = evalPanic "sModMult" ["0 modulus not allowed"]
sModMult sym modulus x y =
  case (SBV.svAsInteger x, SBV.svAsInteger y) of
    (Just i, Just j) -> integerLit sym ((i * j) `mod` modulus)
    _                -> pure $ SBV.svTimes x y

-- Create a fresh constant and assert that it is the
-- multiplicitive inverse of x; return the constant.
-- Such an inverse must exist under the precondition
-- that the modulus is prime and the input is nonzero.
sModRecip ::
  SBV ->
  Integer {- ^ modulus: must be prime -} ->
  SInteger SBV ->
  SEval SBV (SInteger SBV)
sModRecip _sym 0 _ = panic "sModRecip" ["0 modulus not allowed"]
sModRecip sym m x
  -- If the input is concrete, evaluate the answer
  | Just xi <- svAsInteger x
  = case Integer.integerRecipMod xi m of
      Just r  -> integerLit sym r
      Nothing -> raiseError sym DivideByZero

  -- If the input is symbolic, create a new symbolic constant
  -- and assert that it is the desired multiplicitive inverse.
  -- Such an inverse will exist under the precondition that
  -- the modulus is prime, and as long as the input is nonzero.
  | otherwise
  = do divZero <- svDivisible sym m x
       assertSideCondition sym (svNot divZero) DivideByZero

       z <- liftIO (freshSInteger_ sym)
       let xz = svTimes x z
       rel <- znEq sym m xz (svInteger KUnbounded 1)
       let range = svAnd (svLessThan (svInteger KUnbounded 0) z)
                         (svLessThan z (svInteger KUnbounded m))
       liftIO (addDefEqn sym (svAnd range (svOr divZero rel)))

       return z

-- | Ceiling (log_2 x)
sLg2 :: SWord SBV -> SEval SBV (SWord SBV)
sLg2 x = pure $ go 0
  where
    lit n = literalSWord (SBV.intSizeOf x) n
    go i | i < SBV.intSizeOf x = SBV.svIte (SBV.svLessEq x (lit (2^i))) (lit (toInteger i)) (go (i + 1))
         | otherwise           = lit (toInteger i)

svDivisible :: SBV -> Integer -> SInteger SBV -> SEval SBV (SBit SBV)
svDivisible sym m x =
  do m' <- integerLit sym m
     z  <- integerLit sym 0
     pure $ SBV.svEqual (SBV.svRem x m') z

signedQuot :: SWord SBV -> SWord SBV -> SWord SBV
signedQuot x y = SBV.svUnsign (SBV.svQuot (SBV.svSign x) (SBV.svSign y))

signedRem :: SWord SBV -> SWord SBV -> SWord SBV
signedRem x y = SBV.svUnsign (SBV.svRem (SBV.svSign x) (SBV.svSign y))

ashr :: SVal -> SVal -> SVal
ashr x idx =
  case SBV.svAsInteger idx of
    Just i  -> SBV.svUnsign (SBV.svShr (SBV.svSign x) (fromInteger i))
    Nothing -> SBV.svUnsign (SBV.svShiftRight (SBV.svSign x) idx)

lshr :: SVal -> SVal -> SVal
lshr x idx =
  case SBV.svAsInteger idx of
    Just i -> SBV.svShr x (fromInteger i)
    Nothing -> SBV.svShiftRight x idx

shl :: SVal -> SVal -> SVal
shl x idx =
  case SBV.svAsInteger idx of
    Just i  -> SBV.svShl x (fromInteger i)
    Nothing -> SBV.svShiftLeft x idx

-- Floats ----------------------------------------------------------------------
--
-- Note the following naming conventions used in the functions below:
--
-- * fpCvt*: A floating-point operation that lives in the SEval monad (e.g.,
--   because it needs to add assumptions or assert side conditions).
--
-- * sv*: A pure function that is intended to mimic the API in
--   Data.SBV.Dynamic. (In principle, all of these functions could be
--   upstreamed to SBV.)

-- | Convert the exponent and significand (precision) sizes from 'Integer's to
-- 'Int's. While 'Integer'-to-'Int' conversions are not safe in general,
-- Cryptol's floating-point functionality maintains the invariant that the
-- exponent and significand sizes will not exceed the maximum size of an 'Int'.
fpExpAndPrec :: Integer -> Integer -> (Int, Int)
fpExpAndPrec e p = (fromInteger @Int e, fromInteger @Int p)

-- | Convert an 'SBV.FP' to a Cryptol 'BF'.
fpToBF :: SBV.FP -> BF
fpToBF fp =
  BF { bfExpWidth = toInteger @Int (SBV.fpExponentSize fp)
     , bfPrecWidth = toInteger @Int (SBV.fpSignificandSize fp)
     , bfValue = SBV.fpValue fp
     }

-- | Convert a Cryptol 'BF' to an 'SBV.FP'.
fpFromBF :: BF -> SBV.FP
fpFromBF bf =
  SBV.FP { SBV.fpExponentSize = e'
         , SBV.fpSignificandSize = p'
         , SBV.fpValue = bfValue bf
         }
  where
    (e', p') = fpExpAndPrec (bfExpWidth bf) (bfPrecWidth bf)

-- | Convert a Cryptol rounding mode value (represented as a 3-bit word) to an
-- 'SBV.RoundingMode'. Precondition: the Cryptol rounding mode value must be
-- concrete.
fpRoundingMode ::
  SBV -> SWord SBV -> SEval SBV SBV.RoundingMode
fpRoundingMode sym v =
  case wordAsLit sym v of
    Just (_w,i) ->
      case i of
        0 -> pure SBV.RoundNearestTiesToEven
        1 -> pure SBV.RoundNearestTiesToAway
        2 -> pure SBV.RoundTowardPositive
        3 -> pure SBV.RoundTowardNegative
        4 -> pure SBV.RoundTowardZero
        x -> raiseError sym (BadRoundingMode x)
    _ -> liftIO $ X.throwIO $ UnsupportedSymbolicOp "rounding mode"

-- | Convert an 'SBV.RoundingMode' to a @libBF@ 'RoundMode'.
roundingModeToRoundMode :: SBV.RoundingMode -> RoundMode
roundingModeToRoundMode r =
  case r of
    SBV.RoundNearestTiesToEven -> BF.NearEven
    SBV.RoundNearestTiesToAway -> BF.NearAway
    SBV.RoundTowardPositive -> BF.ToPosInf
    SBV.RoundTowardNegative -> BF.ToNegInf
    SBV.RoundTowardZero -> BF.ToZero

-- | Convert a float to a bitvector of the same size.
fpCvtToBits :: SBV -> SFloat SBV -> SEval SBV (SWord SBV)
fpCvtToBits sym x@(SBV.SVal kindFrom@(KFP e p) _)
  | Just x' <- svAsFP x
  = pure $ svInteger kindTo $ fpLiftOpts BF.bfToBits x'
  | otherwise
  = do -- SMT-LIB intentionally doesn't include a float-to-bits operation, as
       -- there is ambiguity about what bit pattern to use for NaN. Cryptol, on
       -- the other hand, picks a single convention for NaNs, which we use
       -- here.
       --
       -- First, we create a fresh bitvector...
       n <- liftIO $ freshBV_ sym w
       pure $ SBV.SVal kindTo $ Right $ SBV.cache $ result n
  where
    w = e + p
    kindTo = KBounded False w

    result n st = do
      n' <- SBV.svToSV st n
      -- ...then we assert that if we convert the fresh bitvector to a float,
      -- then that float will be equal to the input float...
      ysw <- SBV.newExpr st kindFrom $ SBV.SBVApp (SBV.IEEEFP (SBV.FP_Reinterpret kindTo kindFrom)) [n']
      SBV.internalConstraint st False [] $ x `svStrongEqual` SBV.SVal kindFrom (Right (SBV.cache (\_ -> pure ysw)))
      -- ...as noted above, however, we need a special case for NaNs. Here, we
      -- encode Cryptol's NaN bit pattern (see the comments for fpToBits in
      -- lib/Float.cry) as an SBV word.
      let qnan = svInteger kindTo $ shiftL (2 ^ (e + 1) - 1) (p - 2)
      SBV.svToSV st $ svIte (svFPIsNaN x) qnan n
fpCvtToBits _ (SBV.SVal kindFrom _) =
  evalPanic "fpCvtToBits" ["non-float type: " ++ show kindFrom]

-- | Convert a float to an integer using the supplied rounding mode. While
-- SMT-LIB does have an @fp.roundToIntegral@ operation, it returns a float
-- rather than an integer. As such, we rountrip through real numbers instead.
--
-- Precondition: the input float is finite and not a NaN.
fpCvtToInteger :: SBV -> String -> SWord SBV -> SFloat SBV -> SEval SBV (SInteger SBV)
fpCvtToInteger sym fun r x = do
  let grd = svNot (svOr (svFPIsInfinite x) (svFPIsNaN x))
  assertSideCondition sym grd (BadValue fun)
  rnd <- fpRoundingMode sym r
  let y = svFPToReal x
  case rnd of
    SBV.RoundNearestTiesToEven -> fpRealRoundEven sym y
    SBV.RoundNearestTiesToAway -> fpRealRoundAway sym y
    SBV.RoundTowardPositive -> pure $ svRealCeil y
    SBV.RoundTowardNegative -> pure $ svRealFloor y
    SBV.RoundTowardZero -> pure $ svRealTrunc y

-- | Round a real number to the nearest integer, ties to even.
fpRealRoundEven :: SBV -> SBV.SVal -> SEval SBV (SInteger SBV)
fpRealRoundEven sym x
  | Just x' <- svAsAlgRational x
  = pure $ svInteger KUnbounded $ round x'
  | otherwise
  = do -- It's not very straightforward to define the semantics of this
       -- operation in terms of SMT-LIB's to_int operation (which rounds
       -- towards negative infinity). As such, we mimic the approach that
       -- what4's encoding of realRoundEven uses.
       --
       -- First, create a fresh integer `nm`.
       nm <- liftIO $ freshSInteger_ sym
       -- Let `r` be the real number obtained from converting `nm` to a real.
       let r = svFromIntegral KReal nm
       -- Assert that `x` is in the interval [r, r+1].
       liftIO $ addDefEqn sym $
         svAnd (svLessEq r x) (svLessEq x (svPlus r (svReal 1)))
       let diff = svMinus x r
       let half = svReal (1 % 2)
       let nmPlusOne = svPlus nm (svInteger KUnbounded 1)
       let nmEven = svEqual (svRem nm (svInteger KUnbounded 2))
                            (svInteger KUnbounded 0)
       -- Finally, return either `nm` or `nm + 1` depending on how large `x`'s
       -- fractional component is and whether `nm` is even or not.
       pure $
         svIte (svLessThan diff half) nm $
           svIte (svGreaterThan diff half) nmPlusOne $
             svIte nmEven nm nmPlusOne

-- | Round a real number to the nearest integer, ties away from zero.
fpRealRoundAway :: SBV -> SBV.SVal -> SEval SBV (SInteger SBV)
fpRealRoundAway sym x
  | Just x' <- svAsAlgRational x
  = pure $ svInteger KUnbounded $ roundAway x'
  | otherwise
  = do -- It's not very straightforward to define the semantics of this
       -- operation in terms of SMT-LIB's to_int operation (which rounds
       -- towards negative infinity). As such, we mimic the approach that
       -- what4's encoding of realRoundEven uses.
       --
       -- First, create a fresh integer `nm`.
       nm <- liftIO $ freshSInteger_ sym
       -- Let `r` be the real number obtained from converting `nm` to a real.
       let r = svFromIntegral KReal nm
       -- Split into two cases depending on if x is non-negative.
       let zero = svReal 0
       let one = svReal 1
       let two = svReal 2
       -- 2*x
       let twoX = svTimes two x
       -- 2*r
       let twoR = svTimes two r
       -- 2*x - 1
       let twoXMinus1 = svMinus twoX one
       -- 2*x + 1
       let twoXPlus1 = svPlus twoX one
       -- (2*x - 1 <  2*r) && (2*r <= 2*x + 1)
       let posExpr = svAnd (svLessThan twoXMinus1 twoR) (svLessEq twoR twoXPlus1)
       -- (2*x - 1 <= 2*r) && (2*r <  2*x + 1)
       let negExpr = svAnd (svLessEq twoXMinus1 twoR) (svLessThan twoR twoXPlus1)
       liftIO $ addDefEqn sym $
         svOr (svLessThan x zero) posExpr
       liftIO $ addDefEqn sym $
         svOr (svGreaterEq x zero) negExpr
       pure nm
  where
    roundAway :: Rational -> Integer
    roundAway r = truncate (r + signum r * 0.5)

-- | Convert a float to a rational. SMT-LIB doesn't have an operation quite
-- like this, so we create one ourselves by round-tripping through real
-- numbers.
--
-- Precondition: the input float is finite and not a NaN.
fpCvtToRational :: SBV -> SFloat SBV -> SEval SBV (SRational SBV)
fpCvtToRational sym fp = do
  let grd = svNot (svOr (svFPIsInfinite fp) (svFPIsNaN fp))
  assertSideCondition sym grd (BadValue "fpToRational")
  -- Convert the input float to a real number `r`. Also create two fresh
  -- integers `x` and `y` and assume that `r = x/y`.
  let r = svFPToReal fp
  x <- liftIO $ freshSInteger_ sym
  y <- liftIO $ freshSInteger_ sym
  -- In order for `x/y` to be well-defined, `y` cannot be zero.
  liftIO $ addDefEqn sym $ SBV.svLessEq (SBV.svInteger KUnbounded 1) y
  let num = svFromIntegral KReal x
  let den = svFromIntegral KReal y
  let res = svDivide num den
  let same = svEqual r res
  liftIO $ addDefEqn sym $ SBV.svOr (svNot grd) same
  -- Finally, return the rational number `x/y`.
  pure $ SRational x y

-- Various utility functions for lifting BigFloat operations to SBV.FP
-- operations.

fpLift ::
  (BigFloat -> r) ->
  SBV.FP -> r
fpLift f (SBV.FP _ _ a) = f a

fpLiftOpts ::
  (BFOpts -> BigFloat -> r) ->
  SBV.FP -> r
fpLiftOpts f (SBV.FP eb sb a) = f (fpOpts eb' sb' BF.NearEven) a
  where
    eb' = toInteger @Int eb
    sb' = toInteger @Int sb

fpArith1 ::
  (BigFloat -> BigFloat) ->
  SBV.FP -> SBV.FP
fpArith1 f (SBV.FP eb sb a) = SBV.FP eb sb $ f a

fpArithRM1 ::
  (BFOpts -> BigFloat -> (BigFloat, Status)) ->
  SBV.RoundingMode -> SBV.FP -> SBV.FP
fpArithRM1 f r (SBV.FP eb sb a) =
    SBV.FP eb sb $ fpCheckStatus $ f (fpOpts eb' sb' r') a
  where
    r'  = roundingModeToRoundMode r
    eb' = toInteger @Int eb
    sb' = toInteger @Int sb

fpArithRM2 ::
  (BFOpts -> BigFloat -> BigFloat -> (BigFloat, Status)) ->
  SBV.RoundingMode -> SBV.FP -> SBV.FP -> SBV.FP
fpArithRM2 f r (SBV.FP eb sb a) (SBV.FP _ _ b) =
    SBV.FP eb sb $ fpCheckStatus $ f (fpOpts eb' sb' r') a b
  where
    r'  = roundingModeToRoundMode r
    eb' = toInteger @Int eb
    sb' = toInteger @Int sb

fpArithRM3 ::
  (BFOpts -> BigFloat -> BigFloat -> BigFloat -> (BigFloat, Status)) ->
  SBV.RoundingMode -> SBV.FP -> SBV.FP -> SBV.FP -> SBV.FP
fpArithRM3 f r (SBV.FP eb sb a) (SBV.FP _ _ b) (SBV.FP _ _ c) =
    SBV.FP eb sb $ fpCheckStatus $ f (fpOpts eb' sb' r') a b c
  where
    r'  = roundingModeToRoundMode r
    eb' = toInteger @Int eb
    sb' = toInteger @Int sb

-- | Convert from a concrete 'SBV.RoundingMode'.
svRoundingMode :: SBV.RoundingMode -> SVal
svRoundingMode r = SBV.unSBV $ SBV.literal r

-- | Extract an 'SBV.FP' from a concrete value.
svAsFP :: SFloat SBV -> Maybe SBV.FP
svAsFP (SBV.SVal _ (Left (CV _ (CFP fp)))) = Just fp
svAsFP _ = Nothing

-- | Extract a 'Rational' from a concrete value. (Note that not all concrete
-- algebraic real values correspond to 'Rational' values.)
svAsAlgRational :: SVal -> Maybe Rational
svAsAlgRational (SBV.SVal _ (Left (CV _ (CAlgReal (SBV.AlgRational True r))))) = Just r
svAsAlgRational _ = Nothing

-- | Create a NaN float value of the given exponent and significand sizes.
svFPNaN :: Integer -> Integer -> SFloat SBV
svFPNaN e p = SBV.SVal kind $ Left $ SBV.CV kind $ CFP $ SBV.fpNaN e' p'
  where
    (e', p') = fpExpAndPrec e p
    kind = KFP e' p'

-- | Create an infinite float value of the given exponent and significand
-- sizes. If the 'Bool' argument is 'True', then use negative infinity;
-- otherwise, use positive infinity.
svFPInf :: Bool -> Integer -> Integer -> SFloat SBV
svFPInf sign e p = SBV.SVal kind $ Left $ SBV.CV kind $ CFP $ SBV.fpInf sign e' p'
  where
    (e', p') = fpExpAndPrec e p
    kind = KFP e' p'

-- | Create a float value from a concrete 'Rational' value. This uses the
-- 'SBV.RoundNearestTiesToEven' rounding mode, which is consistent with how
-- "Cryptol.Backend.What4" does it.
svFPFromRationalLit :: Integer -> Integer -> Rational -> SFloat SBV
svFPFromRationalLit e p r = SBV.SVal kind $ Left $ SBV.CV kind $ CFP $ SBV.fpFromRational e' p' r
  where
    (e', p') = fpExpAndPrec e p
    kind = KFP e' p'

-- | Compute the greatest integer which is not greater than the input (i.e.,
-- the floor).
svRealFloor :: SBV.SVal -> SInteger SBV
svRealFloor x
  | Just x' <- svAsAlgRational x
  = svInteger kindTo $ floor x'
  | otherwise
  = SBV.SVal kindTo $ Right $ SBV.cache result
  where
    kindFrom = KReal
    kindTo = KUnbounded

    result st = do
      x' <- SBV.svToSV st x
      -- Note that KindCast uses @to_int@ under the hood, which rounds the same
      -- way as @floor@ does.
      SBV.newExpr st kindTo $ SBV.SBVApp (SBV.KindCast kindFrom kindTo) [x']

-- | Compute the least integer which is not less than the input (i.e., the
-- ceiling).
svRealCeil :: SBV.SVal -> SInteger SBV
-- Note that `ceiling x = -(floor (-x))`
svRealCeil = SBV.svUNeg . svRealFloor . SBV.svUNeg

-- | Truncate the input, i.e., return the integer nearest the input which is
-- between zero and the input.
svRealTrunc :: SBV.SVal -> SInteger SBV
svRealTrunc x =
  -- Note that `trunc x = if x < 0 then ceiling x else floor x`
  let isNeg = svLessThan x (svReal 0) in
  svIte isNeg (svRealCeil x) (svRealFloor x)

-- Various utility functions for lifting BigFloat operations to SFloat
-- operations.

svPred ::
  (BigFloat -> Bool) ->
  SBV.FPOp ->
  SFloat SBV -> SBit SBV
svPred concreteOp symbolicOp x
  | Just x' <- svAsFP x
  = svBool $ fpLift concreteOp x'
  | otherwise
  = SBV.SVal KBool $ Right $ SBV.cache result
  where
    result st = do
      x' <- SBV.svToSV st x
      SBV.newExpr st KBool $ SBV.SBVApp (SBV.IEEEFP symbolicOp) [x']

svPredOpts ::
  (BFOpts -> BigFloat -> Bool) ->
  SBV.FPOp ->
  SFloat SBV -> SBit SBV
svPredOpts concreteOp symbolicOp x
  | Just x' <- svAsFP x
  = svBool $ fpLiftOpts concreteOp x'
  | otherwise
  = SBV.SVal KBool $ Right $ SBV.cache result
  where
    result st = do
      x' <- SBV.svToSV st x
      SBV.newExpr st KBool $ SBV.SBVApp (SBV.IEEEFP symbolicOp) [x']

svArith1 ::
  (BigFloat -> BigFloat) ->
  SBV.FPOp ->
  SFloat SBV -> SFloat SBV
svArith1 concreteOp symbolicOp x
  | Just x' <- svAsFP x
  = svFloatingPoint $ fpArith1 concreteOp x'
  | otherwise
  = SBV.SVal kind $ Right $ SBV.cache result
  where
    kind = kindOf x
    result st = do
      x' <- SBV.svToSV st x
      SBV.newExpr st kind $ SBV.SBVApp (SBV.IEEEFP symbolicOp) [x']

svArithRM1 ::
  (BFOpts -> BigFloat -> (BigFloat, Status)) ->
  SBV.FPOp ->
  SBV.RoundingMode -> SFloat SBV -> SFloat SBV
svArithRM1 concreteOp symbolicOp r x
  | Just x' <- svAsFP x
  = svFloatingPoint $ fpArithRM1 concreteOp r x'
  | otherwise
  = SBV.SVal kind $ Right $ SBV.cache result
  where
    kind = kindOf x
    result st = do
      r' <- SBV.svToSV st (svRoundingMode r)
      x' <- SBV.svToSV st x
      SBV.newExpr st kind $ SBV.SBVApp (SBV.IEEEFP symbolicOp) [r', x']

svArithRM2 ::
  (BFOpts -> BigFloat -> BigFloat -> (BigFloat, Status)) ->
  SBV.FPOp ->
  SBV.RoundingMode -> SFloat SBV -> SFloat SBV -> SFloat SBV
svArithRM2 concreteOp symbolicOp r x y
  | Just x' <- svAsFP x, Just y' <- svAsFP y
  = svFloatingPoint $ fpArithRM2 concreteOp r x' y'
  | otherwise
  = SBV.SVal kind $ Right $ SBV.cache result
  where
    kind = kindOf x
    result st = do
      r' <- SBV.svToSV st (svRoundingMode r)
      x' <- SBV.svToSV st x
      y' <- SBV.svToSV st y
      SBV.newExpr st kind $ SBV.SBVApp (SBV.IEEEFP symbolicOp) [r', x', y']

svArithRM3 ::
  (BFOpts -> BigFloat -> BigFloat -> BigFloat -> (BigFloat, Status)) ->
  SBV.FPOp ->
  SBV.RoundingMode -> SFloat SBV -> SFloat SBV -> SFloat SBV -> SFloat SBV
svArithRM3 concreteOp symbolicOp r x y z
  | Just x' <- svAsFP x, Just y' <- svAsFP y, Just z' <- svAsFP z
  = svFloatingPoint $ fpArithRM3 concreteOp r x' y' z'
  | otherwise
  = SBV.SVal kind $ Right $ SBV.cache result
  where
    kind = kindOf x
    result st = do
      r' <- SBV.svToSV st (svRoundingMode r)
      x' <- SBV.svToSV st x
      y' <- SBV.svToSV st y
      z' <- SBV.svToSV st z
      SBV.newExpr st kind $ SBV.SBVApp (SBV.IEEEFP symbolicOp) [r', x', y', z']

-- | Floating-point addition.
svFPPlus :: SBV.RoundingMode -> SFloat SBV -> SFloat SBV -> SFloat SBV
svFPPlus = svArithRM2 BF.bfAdd SBV.FP_Add

-- | Floating-point subtraction.
svFPSub :: SBV.RoundingMode -> SFloat SBV -> SFloat SBV -> SFloat SBV
svFPSub = svArithRM2 BF.bfSub SBV.FP_Sub

-- | Floating-point multiplication.
svFPMul :: SBV.RoundingMode -> SFloat SBV -> SFloat SBV -> SFloat SBV
svFPMul = svArithRM2 BF.bfMul SBV.FP_Mul

-- | Floating-point division.
svFPDiv :: SBV.RoundingMode -> SFloat SBV -> SFloat SBV -> SFloat SBV
svFPDiv = svArithRM2 BF.bfDiv SBV.FP_Div

-- | Floating-point absolute value.
svFPAbs :: SFloat SBV -> SFloat SBV
svFPAbs = svArith1 BF.bfAbs SBV.FP_Abs

-- | Floating-point square root.
svFPSqrt :: SBV.RoundingMode -> SFloat SBV -> SFloat SBV
svFPSqrt = svArithRM1 BF.bfSqrt SBV.FP_Sqrt

-- | Floating-point fused-multiply-add (FMA).
svFPFMA :: SBV.RoundingMode -> SFloat SBV -> SFloat SBV -> SFloat SBV -> SFloat SBV
svFPFMA = svArithRM3 BF.bfFMA SBV.FP_FMA

-- | Floating-point negation.
svFPNeg :: SFloat SBV -> SFloat SBV
svFPNeg = svArith1 BF.bfNeg SBV.FP_Neg

-- | Convert an integer to a float, subject to the given rounding mode.
svFPFromInteger :: Integer -> Integer -> SBV.RoundingMode -> SInteger SBV -> SFloat SBV
svFPFromInteger e p r x
  | Just x' <- svAsInteger x
  = svFloatingPoint $ SBV.FP e' p' $ fpCheckStatus $ BF.bfRoundFloat (fpOpts e p rm) (BF.bfFromInteger x')
  | otherwise
  = SBV.SVal kindTo $ Right $ SBV.cache result
  where
    (e', p') = fpExpAndPrec e p
    rm = roundingModeToRoundMode r
    sr = svRoundingMode r
    kindFrom = KUnbounded
    kindTo = KFP e' p'

    result st = do
      sr' <- SBV.svToSV st sr
      x' <- SBV.svToSV st x
      SBV.newExpr st kindTo $ SBV.SBVApp (SBV.IEEEFP (SBV.FP_Cast kindFrom kindTo sr')) [x']

-- | Convert a real number to a float, subject to the given rounding mode.
svFPFromReal :: Integer -> Integer -> SBV.RoundingMode -> SBV.SVal -> SFloat SBV
svFPFromReal e p r x
  | Just x' <- svAsAlgRational x
  = let numBF = BF.bfFromInteger $ numerator x' in
    let denBF = BF.bfFromInteger $ denominator x' in
    svFloatingPoint $ SBV.FP e' p' $ fpCheckStatus $ BF.bfDiv (fpOpts e p rm) numBF denBF
  | otherwise
  = SBV.SVal kindTo $ Right $ SBV.cache result
  where
    (e', p') = fpExpAndPrec e p
    rm = roundingModeToRoundMode r
    sr = svRoundingMode r
    kindFrom = KReal
    kindTo = KFP e' p'

    result st = do
      sr' <- SBV.svToSV st sr
      x' <- SBV.svToSV st x
      SBV.newExpr st kindTo $ SBV.SBVApp (SBV.IEEEFP (SBV.FP_Cast kindFrom kindTo sr')) [x']

-- | Convert a float to a real number.
--
-- Precondition: the float must be finite and not a NaN.
svFPToReal :: SFloat SBV -> SBV.SVal
svFPToReal x@(SBV.SVal kindFrom _)
  | Just x' <- svAsFP x
  = svReal $ toRational x'
  | otherwise
  = SBV.SVal kindTo $ Right $ SBV.cache result
  where
    -- The choice of rounding mode here is arbitrary. Ultimately, SBV does not
    -- make use of this rounding mode anyway, as converting a float to a real
    -- number does not require rounding.
    sr = svRoundingMode SBV.RoundNearestTiesToEven
    kindTo = KReal

    result st = do
      sr' <- SBV.svToSV st sr
      x' <- SBV.svToSV st x
      SBV.newExpr st kindTo $ SBV.SBVApp (SBV.IEEEFP (SBV.FP_Cast kindFrom kindTo sr')) [x']

-- | Check if a float is zero.
svFPIsZero :: SFloat SBV -> SBit SBV
svFPIsZero = svPred BF.bfIsZero SBV.FP_IsZero

-- | Check if a float is infinite.
svFPIsInfinite :: SFloat SBV -> SBit SBV
svFPIsInfinite = svPred BF.bfIsInf SBV.FP_IsInfinite

-- | Check if a float is negative.
svFPIsNegative :: SFloat SBV -> SBit SBV
svFPIsNegative = svPred BF.bfIsNeg SBV.FP_IsNegative

-- | Check if a float is NaN.
svFPIsNaN :: SFloat SBV -> SBit SBV
svFPIsNaN = svPred BF.bfIsNaN SBV.FP_IsNaN

-- | Check if a float is normal.
svFPIsNormal :: SFloat SBV -> SBit SBV
svFPIsNormal = svPredOpts BF.bfIsNormal SBV.FP_IsNormal

-- | Check if a float is subnormal.
svFPIsSubnormal :: SFloat SBV -> SBit SBV
svFPIsSubnormal = svPredOpts BF.bfIsSubnormal SBV.FP_IsSubnormal

-- | Convert a bitvector to a float of the same size.
svFPFromBits :: Integer -> Integer -> SWord SBV -> SFloat SBV
svFPFromBits e p x
  | Just x' <- svAsInteger x
  = svFloatingPoint $ SBV.FP e' p' $ BF.bfFromBits (fpOpts e p BF.NearEven) x'
  | otherwise
  = SBV.SVal kindTo $ Right $ SBV.cache result
  where
    (e', p') = fpExpAndPrec e p
    kindFrom = KBounded False (e' + p')
    kindTo = KFP e' p'

    result st = do
      x' <- SBV.svToSV st x
      SBV.newExpr st kindTo $ SBV.SBVApp (SBV.IEEEFP (SBV.FP_Reinterpret kindFrom kindTo)) [x']

-- | Convert a 'Rational' to a float, subject to the given rounding mode.
-- SMT-LIB doesn't have an operation quite like this, so we create one
-- ourselves by round-tripping through real numbers.
svFPFromRational :: Integer -> Integer -> SBV.RoundingMode -> SRational SBV -> SFloat SBV
svFPFromRational e p r x =
  let num = svFromIntegral KReal (sNum x) in
  let den = svFromIntegral KReal (sDenom x) in
  let res = svDivide num den in
  svFPFromReal e p r res
