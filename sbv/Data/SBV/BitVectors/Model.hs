-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.BitVectors.Model
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Instance declarations for our symbolic world
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -fno-warn-orphans   #-}
{-# LANGUAGE CPP                    #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE BangPatterns           #-}
{-# LANGUAGE PatternGuards          #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE Rank2Types             #-}

module Data.SBV.BitVectors.Model (
    Mergeable(..), EqSymbolic(..), OrdSymbolic(..), SDivisible(..), Uninterpreted(..), SIntegral
  , ite, iteLazy, sBranch, sbvTestBit, sbvPopCount, setBitTo, sbvShiftLeft, sbvShiftRight, sbvSignedShiftArithRight
  , sbvRotateLeft, sbvRotateRight, mkUninterpreted
  , allEqual, allDifferent, inRange, sElem, oneIf, blastBE, blastLE, fullAdder, fullMultiplier
  , lsb, msb, genVar, genVar_, forall, forall_, exists, exists_
  , constrain, pConstrain, sBool, sBools, sWord8, sWord8s, sWord16, sWord16s, sWord32
  , sWord32s, sWord64, sWord64s, sInt8, sInt8s, sInt16, sInt16s, sInt32, sInt32s, sInt64
  , sInt64s, sInteger, sIntegers, sReal, sReals, toSReal, sFloat, sFloats, sDouble, sDoubles, slet
  , fusedMA
  , liftQRem, liftDMod
  )
  where

import Control.Monad   (when, liftM)

import Data.Array      (Array, Ix, listArray, elems, bounds, rangeSize)
import Data.Bits       (Bits(..))
import Data.Int        (Int8, Int16, Int32, Int64)
import Data.List       (genericLength, genericIndex, unzip4, unzip5, unzip6, unzip7, intercalate)
import Data.Maybe      (fromMaybe)
import Data.Word       (Word8, Word16, Word32, Word64)

import Test.QuickCheck                           (Testable(..), Arbitrary(..))
import qualified Test.QuickCheck         as QC   (whenFail)
import qualified Test.QuickCheck.Monadic as QC   (monadicIO, run)
import System.Random

import Data.SBV.BitVectors.AlgReals
import Data.SBV.BitVectors.Data
import Data.SBV.Utils.Boolean

-- The following two imports are only needed because of the doctest expressions we have. Sigh..
-- It might be a good idea to reorg some of the content to avoid this.
import Data.SBV.Provers.Prover (isSBranchFeasibleInState, isVacuous, prove)
import Data.SBV.SMT.SMT (ThmResult)

-- | Newer versions of GHC (Starting with 7.8 I think), distinguishes between FiniteBits and Bits classes.
-- We should really use FiniteBitSize for SBV which would make things better. In the interim, just work
-- around pesky warnings..
ghcBitSize :: Bits a => a -> Int
#if __GLASGOW_HASKELL__ >= 708
ghcBitSize x = maybe (error "SBV.ghcBitSize: Unexpected non-finite usage!") id (bitSizeMaybe x)
#else
ghcBitSize = bitSize
#endif

noUnint  :: String -> a
noUnint x = error $ "Unexpected operation called on uninterpreted value: " ++ show x

noUnint2 :: String -> String -> a
noUnint2 x y = error $ "Unexpected binary operation called on uninterpreted values: " ++ show (x, y)

liftSym1 :: (State -> Kind -> SW -> IO SW) -> (AlgReal -> AlgReal) -> (Integer -> Integer) -> (Float -> Float) -> (Double -> Double) -> SBV b -> SBV b
liftSym1 _   opCR opCI opCF opCD   (SBV k (Left a)) = SBV k $ Left  $ mapCW opCR opCI opCF opCD noUnint a
liftSym1 opS _    _    _    _    a@(SBV k _)        = SBV k $ Right $ cache c
   where c st = do swa <- sbvToSW st a
                   opS st k swa

liftSW2 :: (State -> Kind -> SW -> SW -> IO SW) -> Kind -> SBV a -> SBV b -> Cached SW
liftSW2 opS k a b = cache c
  where c st = do sw1 <- sbvToSW st a
                  sw2 <- sbvToSW st b
                  opS st k sw1 sw2

liftSym2 :: (State -> Kind -> SW -> SW -> IO SW) -> (CW -> CW -> Bool) -> (AlgReal -> AlgReal -> AlgReal) -> (Integer -> Integer -> Integer) -> (Float -> Float -> Float) -> (Double -> Double -> Double) -> SBV b -> SBV b -> SBV b
liftSym2 _   okCW opCR opCI opCF opCD   (SBV k (Left a)) (SBV _ (Left b)) | okCW a b = SBV k $ Left  $ mapCW2 opCR opCI opCF opCD noUnint2 a b
liftSym2 opS _    _    _    _    _    a@(SBV k _)        b                           = SBV k $ Right $ liftSW2 opS k a b

liftSym2B :: (State -> Kind -> SW -> SW -> IO SW) -> (CW -> CW -> Bool) -> (AlgReal -> AlgReal -> Bool) -> (Integer -> Integer -> Bool) -> (Float -> Float -> Bool) -> (Double -> Double -> Bool) -> SBV b -> SBV b -> SBool
liftSym2B _   okCW opCR opCI opCF opCD (SBV _ (Left a)) (SBV _ (Left b)) | okCW a b = literal (liftCW2 opCR opCI opCF opCD noUnint2 a b)
liftSym2B opS _    _    _    _    _    a                b                           = SBV KBool $ Right $ liftSW2 opS KBool a b

liftSym1Bool :: (State -> Kind -> SW -> IO SW) -> (Bool -> Bool) -> SBool -> SBool
liftSym1Bool _   opC (SBV _ (Left a)) = literal $ opC $ cwToBool a
liftSym1Bool opS _   a                = SBV KBool $ Right $ cache c
  where c st = do sw <- sbvToSW st a
                  opS st KBool sw

liftSym2Bool :: (State -> Kind -> SW -> SW -> IO SW) -> (Bool -> Bool -> Bool) -> SBool -> SBool -> SBool
liftSym2Bool _   opC (SBV _ (Left a)) (SBV _ (Left b)) = literal (cwToBool a `opC` cwToBool b)
liftSym2Bool opS _   a                b                = SBV KBool $ Right $ cache c
  where c st = do sw1 <- sbvToSW st a
                  sw2 <- sbvToSW st b
                  opS st KBool sw1 sw2

mkSymOpSC :: (SW -> SW -> Maybe SW) -> Op -> State -> Kind -> SW -> SW -> IO SW
mkSymOpSC shortCut op st k a b = maybe (newExpr st k (SBVApp op [a, b])) return (shortCut a b)

mkSymOp :: Op -> State -> Kind -> SW -> SW -> IO SW
mkSymOp = mkSymOpSC (const (const Nothing))

mkSymOp1SC :: (SW -> Maybe SW) -> Op -> State -> Kind -> SW -> IO SW
mkSymOp1SC shortCut op st k a = maybe (newExpr st k (SBVApp op [a])) return (shortCut a)

mkSymOp1 :: Op -> State -> Kind -> SW -> IO SW
mkSymOp1 = mkSymOp1SC (const Nothing)

-- Symbolic-Word class instances

-- | Generate a finite symbolic bitvector, named
genVar :: (Random a, SymWord a) => Maybe Quantifier -> Kind -> String -> Symbolic (SBV a)
genVar q k = mkSymSBV q k . Just

-- | Generate a finite symbolic bitvector, unnamed
genVar_ :: (Random a, SymWord a) => Maybe Quantifier -> Kind -> Symbolic (SBV a)
genVar_ q k = mkSymSBV q k Nothing

-- | Generate a finite constant bitvector
genLiteral :: Integral a => Kind -> a -> SBV b
genLiteral k = SBV k . Left . mkConstCW k

-- | Convert a constant to an integral value
genFromCW :: Integral a => CW -> a
genFromCW (CW _ (CWInteger x)) = fromInteger x
genFromCW c                    = error $ "genFromCW: Unsupported non-integral value: " ++ show c

-- | Generically make a symbolic var
genMkSymVar :: (Random a, SymWord a) => Kind -> Maybe Quantifier -> Maybe String -> Symbolic (SBV a)
genMkSymVar k mbq Nothing  = genVar_ mbq k
genMkSymVar k mbq (Just s) = genVar  mbq k s

instance SymWord Bool where
  mkSymWord  = genMkSymVar KBool
  literal x  = genLiteral  KBool (if x then (1::Integer) else 0)
  fromCW     = cwToBool
  mbMaxBound = Just maxBound
  mbMinBound = Just minBound

instance SymWord Word8 where
  mkSymWord  = genMkSymVar (KBounded False 8)
  literal    = genLiteral  (KBounded False 8)
  fromCW     = genFromCW
  mbMaxBound = Just maxBound
  mbMinBound = Just minBound

instance SymWord Int8 where
  mkSymWord  = genMkSymVar (KBounded True 8)
  literal    = genLiteral  (KBounded True 8)
  fromCW     = genFromCW
  mbMaxBound = Just maxBound
  mbMinBound = Just minBound

instance SymWord Word16 where
  mkSymWord  = genMkSymVar (KBounded False 16)
  literal    = genLiteral  (KBounded False 16)
  fromCW     = genFromCW
  mbMaxBound = Just maxBound
  mbMinBound = Just minBound

instance SymWord Int16 where
  mkSymWord  = genMkSymVar (KBounded True 16)
  literal    = genLiteral  (KBounded True 16)
  fromCW     = genFromCW
  mbMaxBound = Just maxBound
  mbMinBound = Just minBound

instance SymWord Word32 where
  mkSymWord  = genMkSymVar (KBounded False 32)
  literal    = genLiteral  (KBounded False 32)
  fromCW     = genFromCW
  mbMaxBound = Just maxBound
  mbMinBound = Just minBound

instance SymWord Int32 where
  mkSymWord  = genMkSymVar (KBounded True 32)
  literal    = genLiteral  (KBounded True 32)
  fromCW     = genFromCW
  mbMaxBound = Just maxBound
  mbMinBound = Just minBound

instance SymWord Word64 where
  mkSymWord  = genMkSymVar (KBounded False 64)
  literal    = genLiteral  (KBounded False 64)
  fromCW     = genFromCW
  mbMaxBound = Just maxBound
  mbMinBound = Just minBound

instance SymWord Int64 where
  mkSymWord  = genMkSymVar (KBounded True 64)
  literal    = genLiteral  (KBounded True 64)
  fromCW     = genFromCW
  mbMaxBound = Just maxBound
  mbMinBound = Just minBound

instance SymWord Integer where
  mkSymWord  = genMkSymVar KUnbounded
  literal    = SBV KUnbounded . Left . mkConstCW KUnbounded
  fromCW     = genFromCW
  mbMaxBound = Nothing
  mbMinBound = Nothing

instance SymWord AlgReal where
  mkSymWord  = genMkSymVar KReal
  literal    = SBV KReal . Left . CW KReal . CWAlgReal
  fromCW (CW _ (CWAlgReal a)) = a
  fromCW c                    = error $ "SymWord.AlgReal: Unexpected non-real value: " ++ show c
  -- AlgReal needs its own definition of isConcretely
  -- to make sure we avoid using unimplementable Haskell functions
  isConcretely (SBV KReal (Left (CW KReal (CWAlgReal v)))) p
     | isExactRational v = p v
  isConcretely _ _       = False
  mbMaxBound = Nothing
  mbMinBound = Nothing

instance SymWord Float where
  mkSymWord  = genMkSymVar KFloat
  literal    = SBV KFloat . Left . CW KFloat . CWFloat
  fromCW (CW _ (CWFloat a)) = a
  fromCW c                  = error $ "SymWord.Float: Unexpected non-float value: " ++ show c
  -- For Float, we conservatively return 'False' for isConcretely. The reason is that
  -- this function is used for optimizations when only one of the argument is concrete,
  -- and in the presence of NaN's it would be incorrect to do any optimization
  isConcretely _ _ = False
  mbMaxBound = Nothing
  mbMinBound = Nothing

instance SymWord Double where
  mkSymWord  = genMkSymVar KDouble
  literal    = SBV KDouble . Left . CW KDouble . CWDouble
  fromCW (CW _ (CWDouble a)) = a
  fromCW c                   = error $ "SymWord.Double: Unexpected non-double value: " ++ show c
  -- For Double, we conservatively return 'False' for isConcretely. The reason is that
  -- this function is used for optimizations when only one of the argument is concrete,
  -- and in the presence of NaN's it would be incorrect to do any optimization
  isConcretely _ _ = False
  mbMaxBound = Nothing
  mbMinBound = Nothing

------------------------------------------------------------------------------------
-- * Smart constructors for creating symbolic values. These are not strictly
-- necessary, as they are mere aliases for 'symbolic' and 'symbolics', but 
-- they nonetheless make programming easier.
------------------------------------------------------------------------------------
-- | Declare an 'SBool'
sBool :: String -> Symbolic SBool
sBool = symbolic

-- | Declare a list of 'SBool's
sBools :: [String] -> Symbolic [SBool]
sBools = symbolics

-- | Declare an 'SWord8'
sWord8 :: String -> Symbolic SWord8
sWord8 = symbolic

-- | Declare a list of 'SWord8's
sWord8s :: [String] -> Symbolic [SWord8]
sWord8s = symbolics

-- | Declare an 'SWord16'
sWord16 :: String -> Symbolic SWord16
sWord16 = symbolic

-- | Declare a list of 'SWord16's
sWord16s :: [String] -> Symbolic [SWord16]
sWord16s = symbolics

-- | Declare an 'SWord32'
sWord32 :: String -> Symbolic SWord32
sWord32 = symbolic

-- | Declare a list of 'SWord32's
sWord32s :: [String] -> Symbolic [SWord32]
sWord32s = symbolics

-- | Declare an 'SWord64'
sWord64 :: String -> Symbolic SWord64
sWord64 = symbolic

-- | Declare a list of 'SWord64's
sWord64s :: [String] -> Symbolic [SWord64]
sWord64s = symbolics

-- | Declare an 'SInt8'
sInt8 :: String -> Symbolic SInt8
sInt8 = symbolic

-- | Declare a list of 'SInt8's
sInt8s :: [String] -> Symbolic [SInt8]
sInt8s = symbolics

-- | Declare an 'SInt16'
sInt16 :: String -> Symbolic SInt16
sInt16 = symbolic

-- | Declare a list of 'SInt16's
sInt16s :: [String] -> Symbolic [SInt16]
sInt16s = symbolics

-- | Declare an 'SInt32'
sInt32 :: String -> Symbolic SInt32
sInt32 = symbolic

-- | Declare a list of 'SInt32's
sInt32s :: [String] -> Symbolic [SInt32]
sInt32s = symbolics

-- | Declare an 'SInt64'
sInt64 :: String -> Symbolic SInt64
sInt64 = symbolic

-- | Declare a list of 'SInt64's
sInt64s :: [String] -> Symbolic [SInt64]
sInt64s = symbolics

-- | Declare an 'SInteger'
sInteger:: String -> Symbolic SInteger
sInteger = symbolic

-- | Declare a list of 'SInteger's
sIntegers :: [String] -> Symbolic [SInteger]
sIntegers = symbolics

-- | Declare an 'SReal'
sReal:: String -> Symbolic SReal
sReal = symbolic

-- | Declare a list of 'SReal's
sReals :: [String] -> Symbolic [SReal]
sReals = symbolics

-- | Declare an 'SFloat'
sFloat :: String -> Symbolic SFloat
sFloat = symbolic

-- | Declare a list of 'SFloat's
sFloats :: [String] -> Symbolic [SFloat]
sFloats = symbolics

-- | Declare an 'SDouble'
sDouble :: String -> Symbolic SDouble
sDouble = symbolic

-- | Declare a list of 'SDouble's
sDoubles :: [String] -> Symbolic [SDouble]
sDoubles = symbolics

-- | Promote an SInteger to an SReal
toSReal :: SInteger -> SReal
toSReal x
  | Just i <- unliteral x = literal $ fromInteger i
  | True                  = SBV KReal (Right (cache y))
  where y st = do xsw <- sbvToSW st x
                  newExpr st KReal (SBVApp (Extract 0 0) [xsw]) -- special encoding!

-- | Symbolic Equality. Note that we can't use Haskell's 'Eq' class since Haskell insists on returning Bool
-- Comparing symbolic values will necessarily return a symbolic value.
--
-- Minimal complete definition: '.=='
infix 4 .==, ./=
class EqSymbolic a where
  (.==), (./=) :: a -> a -> SBool
  -- minimal complete definition: .==
  x ./= y = bnot (x .== y)

-- | Symbolic Comparisons. Similar to 'Eq', we cannot implement Haskell's 'Ord' class
-- since there is no way to return an 'Ordering' value from a symbolic comparison.
-- Furthermore, 'OrdSymbolic' requires 'Mergeable' to implement if-then-else, for the
-- benefit of implementing symbolic versions of 'max' and 'min' functions.
--
-- Minimal complete definition: '.<'
infix 4 .<, .<=, .>, .>=
class (Mergeable a, EqSymbolic a) => OrdSymbolic a where
  (.<), (.<=), (.>), (.>=) :: a -> a -> SBool
  smin, smax :: a -> a -> a
  -- minimal complete definition: .<
  a .<= b    = a .< b ||| a .== b
  a .>  b    = b .<  a
  a .>= b    = b .<= a
  a `smin` b = ite (a .<= b) a b
  a `smax` b = ite (a .<= b) b a

{- We can't have a generic instance of the form:

instance Eq a => EqSymbolic a where
  x .== y = if x == y then true else false

even if we're willing to allow Flexible/undecidable instances..
This is because if we allow this it would imply EqSymbolic (SBV a);
since (SBV a) has to be Eq as it must be a Num. But this wouldn't be
the right choice obviously; as the Eq instance is bogus for SBV
for natural reasons..
-}

instance EqSymbolic (SBV a) where
  (.==) = liftSym2B (mkSymOpSC (eqOpt trueSW)  Equal)    rationalCheck (==) (==) (==) (==)
  (./=) = liftSym2B (mkSymOpSC (eqOpt falseSW) NotEqual) rationalCheck (/=) (/=) (/=) (/=)

-- | eqOpt says the references are to the same SW, thus we can optimize. Note that
-- we explicitly disallow KFloat/KDouble here. Why? Because it's *NOT* true that
-- NaN == NaN, NaN >= NaN, and so-forth. So, we have to make sure we don't optimize
-- floats and doubles, in case the argument turns out to be NaN.
eqOpt :: SW -> SW -> SW -> Maybe SW
eqOpt w x y = case kindOf x of
                KFloat  -> Nothing
                KDouble -> Nothing
                _       -> if x == y then Just w else Nothing

instance SymWord a => OrdSymbolic (SBV a) where
  x .< y
    | Just mb <- mbMaxBound, x `isConcretely` (== mb) = false
    | Just mb <- mbMinBound, y `isConcretely` (== mb) = false
    | True                                            = liftSym2B (mkSymOpSC (eqOpt falseSW) LessThan)    rationalCheck (<)  (<)  (<) (<) x y
  x .<= y
    | Just mb <- mbMinBound, x `isConcretely` (== mb) = true
    | Just mb <- mbMaxBound, y `isConcretely` (== mb) = true
    | True                                            = liftSym2B (mkSymOpSC (eqOpt trueSW) LessEq)       rationalCheck (<=) (<=) (<=) (<=) x y
  x .> y
    | Just mb <- mbMinBound, x `isConcretely` (== mb) = false
    | Just mb <- mbMaxBound, y `isConcretely` (== mb) = false
    | True                                            = liftSym2B (mkSymOpSC (eqOpt falseSW) GreaterThan) rationalCheck (>)  (>)  (>) (>) x y
  x .>= y
    | Just mb <- mbMaxBound, x `isConcretely` (== mb) = true
    | Just mb <- mbMinBound, y `isConcretely` (== mb) = true
    | True                                            = liftSym2B (mkSymOpSC (eqOpt trueSW) GreaterEq)    rationalCheck (>=) (>=) (>=) (>=) x y

-- Bool
instance EqSymbolic Bool where
  x .== y = if x == y then true else false

-- Lists
instance EqSymbolic a => EqSymbolic [a] where
  []     .== []     = true
  (x:xs) .== (y:ys) = x .== y &&& xs .== ys
  _      .== _      = false

instance OrdSymbolic a => OrdSymbolic [a] where
  []     .< []     = false
  []     .< _      = true
  _      .< []     = false
  (x:xs) .< (y:ys) = x .< y ||| (x .== y &&& xs .< ys)

-- Maybe
instance EqSymbolic a => EqSymbolic (Maybe a) where
  Nothing .== Nothing = true
  Just a  .== Just b  = a .== b
  _       .== _       = false

instance (OrdSymbolic a) => OrdSymbolic (Maybe a) where
  Nothing .<  Nothing = false
  Nothing .<  _       = true
  Just _  .<  Nothing = false
  Just a  .<  Just b  = a .< b

-- Either
instance (EqSymbolic a, EqSymbolic b) => EqSymbolic (Either a b) where
  Left a  .== Left b  = a .== b
  Right a .== Right b = a .== b
  _       .== _       = false

instance (OrdSymbolic a, OrdSymbolic b) => OrdSymbolic (Either a b) where
  Left a  .< Left b  = a .< b
  Left _  .< Right _ = true
  Right _ .< Left _  = false
  Right a .< Right b = a .< b

-- 2-Tuple
instance (EqSymbolic a, EqSymbolic b) => EqSymbolic (a, b) where
  (a0, b0) .== (a1, b1) = a0 .== a1 &&& b0 .== b1

instance (OrdSymbolic a, OrdSymbolic b) => OrdSymbolic (a, b) where
  (a0, b0) .< (a1, b1) = a0 .< a1 ||| (a0 .== a1 &&& b0 .< b1)

-- 3-Tuple
instance (EqSymbolic a, EqSymbolic b, EqSymbolic c) => EqSymbolic (a, b, c) where
  (a0, b0, c0) .== (a1, b1, c1) = (a0, b0) .== (a1, b1) &&& c0 .== c1

instance (OrdSymbolic a, OrdSymbolic b, OrdSymbolic c) => OrdSymbolic (a, b, c) where
  (a0, b0, c0) .< (a1, b1, c1) = (a0, b0) .< (a1, b1) ||| ((a0, b0) .== (a1, b1) &&& c0 .< c1)

-- 4-Tuple
instance (EqSymbolic a, EqSymbolic b, EqSymbolic c, EqSymbolic d) => EqSymbolic (a, b, c, d) where
  (a0, b0, c0, d0) .== (a1, b1, c1, d1) = (a0, b0, c0) .== (a1, b1, c1) &&& d0 .== d1

instance (OrdSymbolic a, OrdSymbolic b, OrdSymbolic c, OrdSymbolic d) => OrdSymbolic (a, b, c, d) where
  (a0, b0, c0, d0) .< (a1, b1, c1, d1) = (a0, b0, c0) .< (a1, b1, c1) ||| ((a0, b0, c0) .== (a1, b1, c1) &&& d0 .< d1)

-- 5-Tuple
instance (EqSymbolic a, EqSymbolic b, EqSymbolic c, EqSymbolic d, EqSymbolic e) => EqSymbolic (a, b, c, d, e) where
  (a0, b0, c0, d0, e0) .== (a1, b1, c1, d1, e1) = (a0, b0, c0, d0) .== (a1, b1, c1, d1) &&& e0 .== e1

instance (OrdSymbolic a, OrdSymbolic b, OrdSymbolic c, OrdSymbolic d, OrdSymbolic e) => OrdSymbolic (a, b, c, d, e) where
  (a0, b0, c0, d0, e0) .< (a1, b1, c1, d1, e1) = (a0, b0, c0, d0) .< (a1, b1, c1, d1) ||| ((a0, b0, c0, d0) .== (a1, b1, c1, d1) &&& e0 .< e1)

-- 6-Tuple
instance (EqSymbolic a, EqSymbolic b, EqSymbolic c, EqSymbolic d, EqSymbolic e, EqSymbolic f) => EqSymbolic (a, b, c, d, e, f) where
  (a0, b0, c0, d0, e0, f0) .== (a1, b1, c1, d1, e1, f1) = (a0, b0, c0, d0, e0) .== (a1, b1, c1, d1, e1) &&& f0 .== f1

instance (OrdSymbolic a, OrdSymbolic b, OrdSymbolic c, OrdSymbolic d, OrdSymbolic e, OrdSymbolic f) => OrdSymbolic (a, b, c, d, e, f) where
  (a0, b0, c0, d0, e0, f0) .< (a1, b1, c1, d1, e1, f1) =    (a0, b0, c0, d0, e0) .<  (a1, b1, c1, d1, e1)
                                                       ||| ((a0, b0, c0, d0, e0) .== (a1, b1, c1, d1, e1) &&& f0 .< f1)

-- 7-Tuple
instance (EqSymbolic a, EqSymbolic b, EqSymbolic c, EqSymbolic d, EqSymbolic e, EqSymbolic f, EqSymbolic g) => EqSymbolic (a, b, c, d, e, f, g) where
  (a0, b0, c0, d0, e0, f0, g0) .== (a1, b1, c1, d1, e1, f1, g1) = (a0, b0, c0, d0, e0, f0) .== (a1, b1, c1, d1, e1, f1) &&& g0 .== g1

instance (OrdSymbolic a, OrdSymbolic b, OrdSymbolic c, OrdSymbolic d, OrdSymbolic e, OrdSymbolic f, OrdSymbolic g) => OrdSymbolic (a, b, c, d, e, f, g) where
  (a0, b0, c0, d0, e0, f0, g0) .< (a1, b1, c1, d1, e1, f1, g1) =    (a0, b0, c0, d0, e0, f0) .<  (a1, b1, c1, d1, e1, f1)
                                                               ||| ((a0, b0, c0, d0, e0, f0) .== (a1, b1, c1, d1, e1, f1) &&& g0 .< g1)

-- | Symbolic Numbers. This is a simple class that simply incorporates all number like
-- base types together, simplifying writing polymorphic type-signatures that work for all
-- symbolic numbers, such as 'SWord8', 'SInt8' etc. For instance, we can write a generic
-- list-minimum function as follows:
--
-- @
--    mm :: SIntegral a => [SBV a] -> SBV a
--    mm = foldr1 (\a b -> ite (a .<= b) a b)
-- @
--
-- It is similar to the standard 'Integral' class, except ranging over symbolic instances.
class (SymWord a, Num a, Bits a) => SIntegral a

-- 'SIntegral' Instances, including all possible variants except 'Bool', since booleans
-- are not numbers.
instance SIntegral Word8
instance SIntegral Word16
instance SIntegral Word32
instance SIntegral Word64
instance SIntegral Int8
instance SIntegral Int16
instance SIntegral Int32
instance SIntegral Int64
instance SIntegral Integer

-- Boolean combinators
instance Boolean SBool where
  true  = literal True
  false = literal False
  bnot  b | b `isConcretely` (== False) = true
          | b `isConcretely` (== True)  = false
          | True                        = liftSym1Bool (mkSymOp1SC opt Not) not b
          where opt x
                 | x == falseSW = Just trueSW
                 | x == trueSW  = Just falseSW
                 | True         = Nothing
  a &&& b | a `isConcretely` (== False) || b `isConcretely` (== False) = false
          | a `isConcretely` (== True)                                 = b
          | b `isConcretely` (== True)                                 = a
          | True                                                       = liftSym2Bool (mkSymOpSC opt And) (&&) a b
          where opt x y
                 | x == falseSW || y == falseSW = Just falseSW
                 | x == trueSW                  = Just y
                 | y == trueSW                  = Just x
                 | True                         = Nothing
  a ||| b | a `isConcretely` (== True)  || b `isConcretely` (== True) = true
          | a `isConcretely` (== False)                               = b
          | b `isConcretely` (== False)                               = a
          | True                                                      = liftSym2Bool (mkSymOpSC opt Or)  (||) a b
          where opt x y
                 | x == trueSW || y == trueSW = Just trueSW
                 | x == falseSW               = Just y
                 | y == falseSW               = Just x
                 | True                       = Nothing
  a <+> b | a `isConcretely` (== False) = b
          | b `isConcretely` (== False) = a
          | a `isConcretely` (== True)  = bnot b
          | b `isConcretely` (== True)  = bnot a
          | True                        = liftSym2Bool (mkSymOpSC opt XOr) (<+>) a b
          where opt x y
                 | x == y       = Just falseSW
                 | x == falseSW = Just y
                 | y == falseSW = Just x
                 | True         = Nothing

-- | Returns (symbolic) true if all the elements of the given list are different.
allDifferent :: EqSymbolic a => [a] -> SBool
allDifferent (x:xs@(_:_)) = bAll (x ./=) xs &&& allDifferent xs
allDifferent _            = true

-- | Returns (symbolic) true if all the elements of the given list are the same.
allEqual :: EqSymbolic a => [a] -> SBool
allEqual (x:xs@(_:_))     = bAll (x .==) xs
allEqual _                = true

-- | Returns (symbolic) true if the argument is in range
inRange :: OrdSymbolic a => a -> (a, a) -> SBool
inRange x (y, z) = x .>= y &&& x .<= z

-- | Symbolic membership test
sElem :: EqSymbolic a => a -> [a] -> SBool
sElem x xs = bAny (.== x) xs

-- | Returns 1 if the boolean is true, otherwise 0.
oneIf :: ({-Num a,-} SymWord a) => SBool -> SBV a
oneIf t = ite t 1 0

-- | Predicate for optimizing word operations like (+) and (*).
isConcreteZero :: SBV a -> Bool
isConcreteZero (SBV _ (Left (CW _ (CWInteger n)))) = n == 0
isConcreteZero (SBV KReal (Left (CW KReal (CWAlgReal v)))) = isExactRational v && v == 0
isConcreteZero _ = False

-- | Predicate for optimizing word operations like (+) and (*).
isConcreteOne :: SBV a -> Bool
isConcreteOne (SBV _ (Left (CW _ (CWInteger 1)))) = True
isConcreteOne (SBV KReal (Left (CW KReal (CWAlgReal v)))) = isExactRational v && v == 1
isConcreteOne _ = False

-- | Predicate for optimizing bitwise operations.
isConcreteOnes :: SBV a -> Bool
isConcreteOnes (SBV _ (Left (CW (KBounded b w) (CWInteger n)))) =
    n == (if b then -1 else bit w - 1)
isConcreteOnes (SBV _ (Left (CW KUnbounded (CWInteger n)))) = n == -1
isConcreteOnes _ = False

-- Num instance for symbolic words.
instance (Ord a, {-Num a,-} SymWord a) => Num (SBV a) where
--BH  fromInteger = literal . fromIntegral
  fromInteger n = error $ "fromInteger " ++ show n ++ " :: SBV a"
  x + y
    | isConcreteZero x = y
    | isConcreteZero y = x
    | True             = liftSym2 (mkSymOp Plus)  rationalCheck (+) (+) (+) (+) x y
  x * y
    | isConcreteZero x = x
    | isConcreteZero y = y
    | isConcreteOne x  = y
    | isConcreteOne y  = x
    | True             = liftSym2 (mkSymOp Times) rationalCheck (*) (*) (*) (*) x y
  x - y
    | isConcreteZero y = x
    | True             = liftSym2 (mkSymOp Minus) rationalCheck (-) (-) (-) (-) x y
  abs a
    | hasSign a = ite (a .< 0) (-a) a
    | True      = a
  signum a
    | hasSign a = ite (a .< 0) (-1) (ite (a .== 0) 0 1)
    | True      = oneIf (a ./= 0)
  negate x
    | isConcreteZero x = x
    | True             = sbvFromInteger (kindOf x) 0 - x

instance (SymWord a, Fractional a) => Fractional (SBV a) where
  fromRational = literal . fromRational
  x / y        = liftSym2 (mkSymOp Quot) rationalCheck (/) die (/) (/) x y
   where -- should never happen
         die = error "impossible: integer valued data found in Fractional instance"

-- | Define Floating instance on SBV's; only for base types that are already floating; i.e., SFloat and SDouble
-- Note that most of the fields are "undefined" for symbolic values, we add methods as they are supported by SMTLib.
-- Currently, the only symbolicly available function in this class is sqrt.
instance (SymWord a, Fractional a, Floating a) => Floating (SBV a) where
    pi      = literal pi
    exp     = lift1FNS "exp"     exp
    log     = lift1FNS "log"     log
    sqrt    = lift1F   sqrt      smtLibSquareRoot
    sin     = lift1FNS "sin"     sin
    cos     = lift1FNS "cos"     cos
    tan     = lift1FNS "tan"     tan
    asin    = lift1FNS "asin"    asin
    acos    = lift1FNS "acos"    acos
    atan    = lift1FNS "atan"    atan
    sinh    = lift1FNS "sinh"    sinh
    cosh    = lift1FNS "cosh"    cosh
    tanh    = lift1FNS "tanh"    tanh
    asinh   = lift1FNS "asinh"   asinh
    acosh   = lift1FNS "acosh"   acosh
    atanh   = lift1FNS "atanh"   atanh
    (**)    = lift2FNS "**"      (**)
    logBase = lift2FNS "logBase" logBase

-- | Fused-multiply add. @fusedMA a b c = a * b + c@, for double and floating point values.
-- Note that a 'fusedMA' call will *never* be concrete, even if all the arguments are constants; since
-- we cannot guarantee the precision requirements, which is the whole reason why 'fusedMA' exists in the
-- first place. (NB. 'fusedMA' only rounds once, even though it does two operations, and hence the extra
-- precision.)
fusedMA :: (SymWord a, Floating a) => SBV a -> SBV a -> SBV a -> SBV a
fusedMA a b c = SBV k $ Right $ cache r
  where k = kindOf a
        r st = do swa <- sbvToSW st a
                  swb <- sbvToSW st b
                  swc <- sbvToSW st c
                  newExpr st k (SBVApp smtLibFusedMA [swa, swb, swc])

-- | Lift a float/double unary function, using a corresponding function in SMT-lib. We piggy-back on the uninterpreted
-- function mechanism here, as it essentially is the same as introducing this as a new function.
lift1F :: (SymWord a, Floating a) => (a -> a) -> Op -> SBV a -> SBV a
lift1F f smtOp sv
  | Just v <- unliteral sv = literal $ f v
  | True                   = SBV k $ Right $ cache c
  where k = kindOf sv
        c st = do swa <- sbvToSW st sv
                  newExpr st k (SBVApp smtOp [swa])

-- | Lift a float/double unary function, only over constants
lift1FNS :: (SymWord a, Floating a) => String -> (a -> a) -> SBV a -> SBV a
lift1FNS nm f sv
  | Just v <- unliteral sv = literal $ f v
  | True                   = error $ "SBV." ++ nm ++ ": not supported for symbolic values of type " ++ show (kindOf sv)

-- | Lift a float/double binary function, only over constants
lift2FNS :: (SymWord a, Floating a) => String -> (a -> a -> a) -> SBV a -> SBV a -> SBV a
lift2FNS nm f sv1 sv2
  | Just v1 <- unliteral sv1
  , Just v2 <- unliteral sv2 = literal $ f v1 v2
  | True                     = error $ "SBV." ++ nm ++ ": not supported for symbolic values of type " ++ show (kindOf sv1)

-- Most operations on concrete rationals require a compatibility check
rationalCheck :: CW -> CW -> Bool
rationalCheck a b = case (cwVal a, cwVal b) of
                     (CWAlgReal x, CWAlgReal y) -> isExactRational x && isExactRational y
                     _                          -> True

-- same as above, for SBV's
rationalSBVCheck :: SBV a -> SBV a -> Bool
rationalSBVCheck (SBV KReal (Left a)) (SBV KReal (Left b)) = rationalCheck a b
rationalSBVCheck _                    _                    = True

-- Some operations will never be used on Reals, but we need fillers:
noReal :: String -> AlgReal -> AlgReal -> AlgReal
noReal o a b = error $ "SBV.AlgReal." ++ o ++ ": Unexpected arguments: " ++ show (a, b)

noFloat :: String -> Float -> Float -> Float
noFloat o a b = error $ "SBV.Float." ++ o ++ ": Unexpected arguments: " ++ show (a, b)

noDouble :: String -> Double -> Double -> Double
noDouble o a b = error $ "SBV.Double." ++ o ++ ": Unexpected arguments: " ++ show (a, b)

noRealUnary :: String -> AlgReal -> AlgReal
noRealUnary o a = error $ "SBV.AlgReal." ++ o ++ ": Unexpected argument: " ++ show a

noFloatUnary :: String -> Float -> Float
noFloatUnary o a = error $ "SBV.Float." ++ o ++ ": Unexpected argument: " ++ show a

noDoubleUnary :: String -> Double -> Double
noDoubleUnary o a = error $ "SBV.Double." ++ o ++ ": Unexpected argument: " ++ show a

-- NB. In the optimizations below, use of -1 is valid as
-- -1 has all bits set to True for both signed and unsigned values
instance ({-Num a,-} Bits a, SymWord a) => Bits (SBV a) where
  x .&. y
    | isConcreteZero x = x
    | isConcreteOnes x = y
    | isConcreteZero y = y
    | isConcreteOnes y = x
    | True             = liftSym2 (mkSymOp  And) (const (const True)) (noReal ".&.") (.&.) (noFloat ".&.") (noDouble ".&.") x y
  x .|. y
    | isConcreteZero x = y
    | isConcreteOnes x = x
    | isConcreteZero y = x
    | isConcreteOnes y = y
    | True             = liftSym2 (mkSymOp  Or)  (const (const True)) (noReal ".|.") (.|.) (noFloat ".|.") (noDouble ".|.") x y
  x `xor` y
    | isConcreteZero x = y
    | isConcreteZero y = x
    | True             = liftSym2 (mkSymOp  XOr) (const (const True)) (noReal "xor") xor (noFloat "xor") (noDouble "xor") x y
  complement = liftSym1 (mkSymOp1 Not) (noRealUnary "complement") complement (noFloatUnary "complement") (noDoubleUnary "complement")
  bitSize  x = case kindOf x of KBounded _ w -> w
#if __GLASGOW_HASKELL__ >= 708
  bitSizeMaybe x = Just $ case kindOf x of KBounded _ w -> w
#endif
  isSigned x = case kindOf x of KBounded s _ -> s
  bit i      = 1 `shiftL` i
  setBit x i = x .|. sbvFromInteger (kindOf x) (bit i)
  shiftL x y
    | y < 0       = shiftR x (-y)
    | y == 0      = x
    | True        = liftSym1 (mkSymOp1 (Shl y)) (noRealUnary "shiftL") (`shiftL` y) (noFloatUnary "shiftL") (noDoubleUnary "shiftL") x
  shiftR x y
    | y < 0       = shiftL x (-y)
    | y == 0      = x
    | True        = liftSym1 (mkSymOp1 (Shr y)) (noRealUnary "shiftR") (`shiftR` y) (noFloatUnary "shiftR") (noDoubleUnary "shiftR") x
  rotateL x y
    | y < 0       = rotateR x (-y)
    | y == 0      = x
    | isBounded x = let sz = ghcBitSize x in liftSym1 (mkSymOp1 (Rol (y `mod` sz))) (noRealUnary "rotateL") (rot True sz y) (noFloatUnary "rotateL") (noDoubleUnary "rotateL") x
    | True        = shiftL x y   -- for unbounded Integers, rotateL is the same as shiftL in Haskell
  rotateR x y
    | y < 0       = rotateL x (-y)
    | y == 0      = x
    | isBounded x = let sz = ghcBitSize x in liftSym1 (mkSymOp1 (Ror (y `mod` sz))) (noRealUnary "rotateR") (rot False sz y) (noFloatUnary "rotateR") (noDoubleUnary "rotateR") x
    | True        = shiftR x y   -- for unbounded integers, rotateR is the same as shiftR in Haskell
  -- NB. testBit is *not* implementable on non-concrete symbolic words
  x `testBit` i
    | SBV _ (Left (CW _ (CWInteger n))) <- x = testBit n i
    | True                 = error $ "SBV.testBit: Called on symbolic value: " ++ show x ++ ". Use sbvTestBit instead."
  -- NB. popCount is *not* implementable on non-concrete symbolic words
  popCount x
    | SBV _ (Left (CW (KBounded _ w) (CWInteger n))) <- x = popCount (n .&. (bit w - 1))
    | True                = error $ "SBV.popCount: Called on symbolic value: " ++ show x ++ ". Use sbvPopCount instead."

-- Since the underlying representation is just Integers, rotations has to be careful on the bit-size
rot :: Bool -> Int -> Int -> Integer -> Integer
rot toLeft sz amt x
  | sz < 2 = x
  | True   = norm x y' `shiftL` y  .|. norm (x `shiftR` y') y
  where (y, y') | toLeft = (amt `mod` sz, sz - y)
                | True   = (sz - y', amt `mod` sz)
        norm v s = v .&. ((1 `shiftL` s) - 1)

sbvFromInteger :: Kind -> Integer -> SBV a
sbvFromInteger k n = SBV k (Left (normCW (CW k (CWInteger n))))

-- | Replacement for 'testBit'. Since 'testBit' requires a 'Bool' to be returned,
-- we cannot implement it for symbolic words. Index 0 is the least-significant bit.
sbvTestBit :: (Num a, Bits a, SymWord a) => SBV a -> Int -> SBool
sbvTestBit x i = (x .&. sbvFromInteger k (bit i)) ./= sbvFromInteger k 0
  where k = kindOf x

-- | Replacement for 'popCount'. Since 'popCount' returns an 'Int', we cannot implement
-- it for symbolic words. Here, we return an 'SWord8', which can overflow when used on
-- quantities that have more than 255 bits. Currently, that's only the 'SInteger' type
-- that SBV supports, all other types are safe. Even with 'SInteger', this will only
-- overflow if there are at least 256-bits set in the number, and the smallest such
-- number is 2^256-1, which is a pretty darn big number to worry about for practical
-- purposes. In any case, we do not support 'sbvPopCount' for unbounded symbolic integers,
-- as the only possible implementation wouldn't symbolically terminate. So the only overflow
-- issue is with really-really large concrete 'SInteger' values.
sbvPopCount :: (Num a, Bits a, SymWord a) => SBV a -> SWord8
sbvPopCount x
  | isReal x          = error "SBV.sbvPopCount: Called on a real value"
  | isConcrete x      = go 0 x
  | not (isBounded x) = error "SBV.sbvPopCount: Called on an infinite precision symbolic value"
  | True              = sum [ite b 1 0 | b <- blastLE x]
  where -- concrete case
        go !c 0 = c
        go !c w = go (c+1) (w .&. (w-1))

-- | Generalization of 'setBit' based on a symbolic boolean. Note that 'setBit' and
-- 'clearBit' are still available on Symbolic words, this operation comes handy when
-- the condition to set/clear happens to be symbolic.
setBitTo :: (Num a, Bits a, SymWord a) => SBV a -> Int -> SBool -> SBV a
setBitTo x i b = ite b (setBit x i) (clearBit x i)

-- | Generalization of 'shiftL', when the shift-amount is symbolic. Since Haskell's
-- 'shiftL' only takes an 'Int' as the shift amount, it cannot be used when we have
-- a symbolic amount to shift with. The shift amount must be an unsigned quantity.
sbvShiftLeft :: (SIntegral a, SIntegral b) => SBV a -> SBV b -> SBV a
sbvShiftLeft x i
  | isSigned i = error "sbvShiftLeft: shift amount should be unsigned"
  | True       = select [x `shiftL` k | k <- [0 .. ghcBitSize x - 1]] z i
    where z = sbvFromInteger (kindOf x) 0

-- | Generalization of 'shiftR', when the shift-amount is symbolic. Since Haskell's
-- 'shiftR' only takes an 'Int' as the shift amount, it cannot be used when we have
-- a symbolic amount to shift with. The shift amount must be an unsigned quantity.
--
-- NB. If the shiftee is signed, then this is an arithmetic shift; otherwise it's logical,
-- following the usual Haskell convention. See 'sbvSignedShiftArithRight' for a variant
-- that explicitly uses the msb as the sign bit, even for unsigned underlying types.
sbvShiftRight :: (SIntegral a, SIntegral b) => SBV a -> SBV b -> SBV a
sbvShiftRight x i
  | isSigned i = error "sbvShiftRight: shift amount should be unsigned"
  | True       = select [x `shiftR` k | k <- [0 .. ghcBitSize x - 1]] z i
    where z = sbvFromInteger (kindOf x) 0

-- | Arithmetic shift-right with a symbolic unsigned shift amount. This is equivalent
-- to 'sbvShiftRight' when the argument is signed. However, if the argument is unsigned,
-- then it explicitly treats its msb as a sign-bit, and uses it as the bit that
-- gets shifted in. Useful when using the underlying unsigned bit representation to implement
-- custom signed operations. Note that there is no direct Haskell analogue of this function.
sbvSignedShiftArithRight:: (SIntegral a, SIntegral b) => SBV a -> SBV b -> SBV a
sbvSignedShiftArithRight x i
  | isSigned i = error "sbvSignedShiftArithRight: shift amount should be unsigned"
  | isSigned x = sbvShiftRight x i
  | True       = ite (msb x)
                     (complement (sbvShiftRight (complement x) i))
                     (sbvShiftRight x i)

-- | Generalization of 'rotateL', when the shift-amount is symbolic. Since Haskell's
-- 'rotateL' only takes an 'Int' as the shift amount, it cannot be used when we have
-- a symbolic amount to shift with. The shift amount must be an unsigned quantity.
sbvRotateLeft :: (SIntegral a, SIntegral b) => SBV a -> SBV b -> SBV a
sbvRotateLeft x i
  | isSigned i = error "sbvRotateLeft: shift amount should be unsigned"
  | True       = select [x `rotateL` k | k <- [0 .. ghcBitSize x - 1]] z i
    where z = sbvFromInteger (kindOf x) 0

-- | Generalization of 'rotateR', when the shift-amount is symbolic. Since Haskell's
-- 'rotateR' only takes an 'Int' as the shift amount, it cannot be used when we have
-- a symbolic amount to shift with. The shift amount must be an unsigned quantity.
sbvRotateRight :: (SIntegral a, SIntegral b) => SBV a -> SBV b -> SBV a
sbvRotateRight x i
  | isSigned i = error "sbvRotateRight: shift amount should be unsigned"
  | True       = select [x `rotateR` k | k <- [0 .. ghcBitSize x - 1]] z i
    where z = sbvFromInteger (kindOf x) 0

-- | Full adder. Returns the carry-out from the addition.
--
-- N.B. Only works for unsigned types. Signed arguments will be rejected.
fullAdder :: SIntegral a => SBV a -> SBV a -> (SBool, SBV a)
fullAdder a b
  | isSigned a = error "fullAdder: only works on unsigned numbers"
  | True       = (a .> s ||| b .> s, s)
  where s = a + b

-- | Full multiplier: Returns both the high-order and the low-order bits in a tuple,
-- thus fully accounting for the overflow.
--
-- N.B. Only works for unsigned types. Signed arguments will be rejected.
--
-- N.B. The higher-order bits are determined using a simple shift-add multiplier,
-- thus involving bit-blasting. It'd be naive to expect SMT solvers to deal efficiently
-- with properties involving this function, at least with the current state of the art.
fullMultiplier :: SIntegral a => SBV a -> SBV a -> (SBV a, SBV a)
fullMultiplier a b
  | isSigned a = error "fullMultiplier: only works on unsigned numbers"
  | True       = (go (ghcBitSize a) 0 a, a*b)
  where go 0 p _ = p
        go n p x = let (c, p')  = ite (lsb x) (fullAdder p b) (false, p)
                       (o, p'') = shiftIn c p'
                       (_, x')  = shiftIn o x
                   in go (n-1) p'' x'
        shiftIn k v = (lsb v, mask .|. (v `shiftR` 1))
           where mask = ite k (bit (ghcBitSize v - 1)) 0

-- | Little-endian blasting of a word into its bits. Also see the 'FromBits' class.
blastLE :: (Num a, Bits a, SymWord a) => SBV a -> [SBool]
blastLE x
 | isReal x          = error "SBV.blastLE: Called on a real value"
 | not (isBounded x) = error "SBV.blastLE: Called on an infinite precision value"
 | True              = map (sbvTestBit x) [0 .. intSizeOf x - 1]

-- | Big-endian blasting of a word into its bits. Also see the 'FromBits' class.
blastBE :: (Num a, Bits a, SymWord a) => SBV a -> [SBool]
blastBE = reverse . blastLE

-- | Least significant bit of a word, always stored at index 0.
lsb :: (Num a, Bits a, SymWord a) => SBV a -> SBool
lsb x = sbvTestBit x 0

-- | Most significant bit of a word, always stored at the last position.
msb :: (Num a, Bits a, SymWord a) => SBV a -> SBool
msb x
 | isReal x          = error "SBV.msb: Called on a real value"
 | not (isBounded x) = error "SBV.msb: Called on an infinite precision value"
 | True              = sbvTestBit x (intSizeOf x - 1)

-- Enum instance. These instances are suitable for use with concrete values,
-- and will be less useful for symbolic values around. Note that `fromEnum` requires
-- a concrete argument for obvious reasons. Other variants (succ, pred, [x..]) etc are similarly
-- limited. While symbolic variants can be defined for many of these, they will just diverge
-- as final sizes cannot be determined statically.
instance (Show a, Bounded a, Integral a, Num a, SymWord a) => Enum (SBV a) where
  succ x
    | v == (maxBound :: a) = error $ "Enum.succ{" ++ showType x ++ "}: tried to take `succ' of maxBound"
    | True                 = fromIntegral $ v + 1
    where v = enumCvt "succ" x
  pred x
    | v == (minBound :: a) = error $ "Enum.pred{" ++ showType x ++ "}: tried to take `pred' of minBound"
    | True                 = fromIntegral $ v - 1
    where v = enumCvt "pred" x
  toEnum x
    | xi < fromIntegral (minBound :: a) || xi > fromIntegral (maxBound :: a)
    = error $ "Enum.toEnum{" ++ showType r ++ "}: " ++ show x ++ " is out-of-bounds " ++ show (minBound :: a, maxBound :: a)
    | True
    = r
    where xi :: Integer
          xi = fromIntegral x
          r  :: SBV a
          r  = fromIntegral x
  fromEnum x
     | r < fromIntegral (minBound :: Int) || r > fromIntegral (maxBound :: Int)
     = error $ "Enum.fromEnum{" ++ showType x ++ "}:  value " ++ show r ++ " is outside of Int's bounds " ++ show (minBound :: Int, maxBound :: Int)
     | True
     = fromIntegral r
    where r :: Integer
          r = enumCvt "fromEnum" x
  enumFrom x = map fromIntegral [xi .. fromIntegral (maxBound :: a)]
     where xi :: Integer
           xi = enumCvt "enumFrom" x
  enumFromThen x y
     | yi >= xi  = map fromIntegral [xi, yi .. fromIntegral (maxBound :: a)]
     | True      = map fromIntegral [xi, yi .. fromIntegral (minBound :: a)]
       where xi, yi :: Integer
             xi = enumCvt "enumFromThen.x" x
             yi = enumCvt "enumFromThen.y" y
  enumFromThenTo x y z = map fromIntegral [xi, yi .. zi]
       where xi, yi, zi :: Integer
             xi = enumCvt "enumFromThenTo.x" x
             yi = enumCvt "enumFromThenTo.y" y
             zi = enumCvt "enumFromThenTo.z" z

-- | Helper function for use in enum operations
enumCvt :: (SymWord a, Integral a, Num b) => String -> SBV a -> b
enumCvt w x = case unliteral x of
                Nothing -> error $ "Enum." ++ w ++ "{" ++ showType x ++ "}: Called on symbolic value " ++ show x
                Just v  -> fromIntegral v

-- | The 'SDivisible' class captures the essence of division.
-- Unfortunately we cannot use Haskell's 'Integral' class since the 'Real'
-- and 'Enum' superclasses are not implementable for symbolic bit-vectors.
-- However, 'quotRem' and 'divMod' makes perfect sense, and the 'SDivisible' class captures
-- this operation. One issue is how division by 0 behaves. The verification
-- technology requires total functions, and there are several design choices
-- here. We follow Isabelle/HOL approach of assigning the value 0 for division
-- by 0. Therefore, we impose the following law:
--
--     @ x `sQuotRem` 0 = (0, x) @
--     @ x `sDivMod`  0 = (0, x) @
--
-- Note that our instances implement this law even when @x@ is @0@ itself.
--
-- NB. 'quot' truncates toward zero, while 'div' truncates toward negative infinity.
--
-- Minimal complete definition: 'sQuotRem', 'sDivMod'
class SDivisible a where
  sQuotRem :: a -> a -> (a, a)
  sDivMod  :: a -> a -> (a, a)
  sQuot    :: a -> a -> a
  sRem     :: a -> a -> a
  sDiv     :: a -> a -> a
  sMod     :: a -> a -> a

  x `sQuot` y = fst $ x `sQuotRem` y
  x `sRem`  y = snd $ x `sQuotRem` y
  x `sDiv`  y = fst $ x `sDivMod`  y
  x `sMod`  y = snd $ x `sDivMod`  y

instance SDivisible Word64 where
  sQuotRem x 0 = (0, x)
  sQuotRem x y = x `quotRem` y
  sDivMod  x 0 = (0, x)
  sDivMod  x y = x `divMod` y

instance SDivisible Int64 where
  sQuotRem x 0 = (0, x)
  sQuotRem x y = x `quotRem` y
  sDivMod  x 0 = (0, x)
  sDivMod  x y = x `divMod` y

instance SDivisible Word32 where
  sQuotRem x 0 = (0, x)
  sQuotRem x y = x `quotRem` y
  sDivMod  x 0 = (0, x)
  sDivMod  x y = x `divMod` y

instance SDivisible Int32 where
  sQuotRem x 0 = (0, x)
  sQuotRem x y = x `quotRem` y
  sDivMod  x 0 = (0, x)
  sDivMod  x y = x `divMod` y

instance SDivisible Word16 where
  sQuotRem x 0 = (0, x)
  sQuotRem x y = x `quotRem` y
  sDivMod  x 0 = (0, x)
  sDivMod  x y = x `divMod` y

instance SDivisible Int16 where
  sQuotRem x 0 = (0, x)
  sQuotRem x y = x `quotRem` y
  sDivMod  x 0 = (0, x)
  sDivMod  x y = x `divMod` y

instance SDivisible Word8 where
  sQuotRem x 0 = (0, x)
  sQuotRem x y = x `quotRem` y
  sDivMod  x 0 = (0, x)
  sDivMod  x y = x `divMod` y

instance SDivisible Int8 where
  sQuotRem x 0 = (0, x)
  sQuotRem x y = x `quotRem` y
  sDivMod  x 0 = (0, x)
  sDivMod  x y = x `divMod` y

instance SDivisible Integer where
  sQuotRem x 0 = (0, x)
  sQuotRem x y = x `quotRem` y
  sDivMod  x 0 = (0, x)
  sDivMod  x y = x `divMod` y

instance SDivisible CW where
  sQuotRem a b
    | CWInteger x <- cwVal a, CWInteger y <- cwVal b
    = let (r1, r2) = sQuotRem x y in (normCW a{ cwVal = CWInteger r1 }, normCW b{ cwVal = CWInteger r2 })
  sQuotRem a b = error $ "SBV.sQuotRem: impossible, unexpected args received: " ++ show (a, b)
  sDivMod a b
    | CWInteger x <- cwVal a, CWInteger y <- cwVal b
    = let (r1, r2) = sDivMod x y in (normCW a { cwVal = CWInteger r1 }, normCW b { cwVal = CWInteger r2 })
  sDivMod a b = error $ "SBV.sDivMod: impossible, unexpected args received: " ++ show (a, b)

instance SDivisible SWord64 where
  sQuotRem = liftQRem
  sDivMod  = liftDMod

instance SDivisible SInt64 where
  sQuotRem = liftQRem
  sDivMod  = liftDMod

instance SDivisible SWord32 where
  sQuotRem = liftQRem
  sDivMod  = liftDMod

instance SDivisible SInt32 where
  sQuotRem = liftQRem
  sDivMod  = liftDMod

instance SDivisible SWord16 where
  sQuotRem = liftQRem
  sDivMod  = liftDMod

instance SDivisible SInt16 where
  sQuotRem = liftQRem
  sDivMod  = liftDMod

instance SDivisible SWord8 where
  sQuotRem = liftQRem
  sDivMod  = liftDMod

instance SDivisible SInt8 where
  sQuotRem = liftQRem
  sDivMod  = liftDMod

liftQRem :: (SymWord a, Num a, SDivisible a) => SBV a -> SBV a -> (SBV a, SBV a)
liftQRem x y = ite (y .== z) (z, x) (qr x y)
  where qr (SBV sgnsz (Left a)) (SBV _ (Left b)) = let (q, r) = sQuotRem a b in (SBV sgnsz (Left q), SBV sgnsz (Left r))
        qr a@(SBV sgnsz _)      b                = (SBV sgnsz (Right (cache (mk Quot))), SBV sgnsz (Right (cache (mk Rem))))
                where mk o st = do sw1 <- sbvToSW st a
                                   sw2 <- sbvToSW st b
                                   mkSymOp o st sgnsz sw1 sw2
        z = sbvFromInteger (kindOf x) 0

-- Conversion from quotRem (truncate to 0) to divMod (truncate towards negative infinity)
liftDMod :: (SymWord a, Num a, SDivisible a, SDivisible (SBV a)) => SBV a -> SBV a -> (SBV a, SBV a)
liftDMod x y = ite (y .== z) (z, x) $ ite (signum r .== negate (signum y)) (q-1, r+y) qr
   where qr@(q, r) = x `sQuotRem` y
         z = sbvFromInteger (kindOf x) 0

-- SInteger instance for quotRem/divMod are tricky!
-- SMT-Lib only has Euclidean operations, but Haskell
-- uses "truncate to 0" for quotRem, and "truncate to negative infinity" for divMod.
-- So, we cannot just use the above liftings directly.
instance SDivisible SInteger where
  sDivMod = liftDMod
  sQuotRem x y
    | not (isSymbolic x || isSymbolic y)
    = liftQRem x y
    | True
    = ite (y .== 0) (0, x) (qE+i, rE-i*y)
    where (qE, rE) = liftQRem x y   -- for integers, this is euclidean due to SMTLib semantics
          i = ite (x .>= 0 ||| rE .== 0) 0
            $ ite (y .>  0)              1 (-1)

-- Quickcheck interface

-- The Arbitrary instance for SFunArray returns an array initialized
-- to an arbitrary element
instance (SymWord b, Arbitrary b) => Arbitrary (SFunArray a b) where
  arbitrary = arbitrary >>= \r -> return $ SFunArray (const r)

instance (SymWord a, Arbitrary a) => Arbitrary (SBV a) where
  arbitrary = liftM literal arbitrary

-- |  Symbolic conditionals are modeled by the 'Mergeable' class, describing
-- how to merge the results of an if-then-else call with a symbolic test. SBV
-- provides all basic types as instances of this class, so users only need
-- to declare instances for custom data-types of their programs as needed.
--
-- The function 'select' is a total-indexing function out of a list of choices
-- with a default value, simulating array/list indexing. It's an n-way generalization
-- of the 'ite' function.
--
-- Minimal complete definition: 'symbolicMerge'
class Mergeable a where
   -- | Merge two values based on the condition. The first argument states
   -- whether we force the then-and-else branches before the merging, at the
   -- word level. This is an efficiency concern; one that we'd rather not
   -- make but unfortunately necessary for getting symbolic simulation
   -- working efficiently.
   symbolicMerge :: Bool -> SBool -> a -> a -> a
   -- | Total indexing operation. @select xs default index@ is intuitively
   -- the same as @xs !! index@, except it evaluates to @default@ if @index@
   -- overflows
   select :: (SymWord b, Num b) => [a] -> a -> SBV b -> a
   -- NB. Earlier implementation of select used the binary-search trick
   -- on the index to chop down the search space. While that is a good trick
   -- in general, it doesn't work for SBV since we do not have any notion of
   -- "concrete" subwords: If an index is symbolic, then all its bits are
   -- symbolic as well. So, the binary search only pays off only if the indexed
   -- list is really humongous, which is not very common in general. (Also,
   -- for the case when the list is bit-vectors, we use SMT tables anyhow.)
   select xs err ind
    | isReal ind = error "SBV.select: unsupported real valued select/index expression"
    | True       = walk xs ind err
    where walk []     _ acc = acc
          walk (e:es) i acc = walk es (i-1) (ite (i .== 0) e acc)


-- | If-then-else. This is by definition 'symbolicMerge' with both
-- branches forced. This is typically the desired behavior, but also
-- see 'iteLazy' should you need more laziness.
ite :: Mergeable a => SBool -> a -> a -> a
ite t a b
  | Just r <- unliteral t = if r then a else b
  | True                  = symbolicMerge True t a b

-- | A Lazy version of ite, which does not force its arguments. This might
-- cause issues for symbolic simulation with large thunks around, so use with
-- care.
iteLazy :: Mergeable a => SBool -> a -> a -> a
iteLazy t a b
  | Just r <- unliteral t = if r then a else b
  | True                  = symbolicMerge False t a b

-- | Branch on a condition, much like 'ite'. The exception is that SBV will
-- check to make sure if the test condition is feasible by making an external
-- call to the SMT solver. Note that this can be expensive, thus we shall use
-- a time-out value ('sBranchTimeOut'). There might be zero, one, or two such
-- external calls per 'sBranch' call:
--
--    - If condition is statically known to be True/False: 0 calls
--           - In this case, we simply constant fold..
--
--    - If condition is determined to be unsatisfiable   : 1 call
--           - In this case, we know then-branch is infeasible, so just take the else-branch
--
--    - If condition is determined to be satisfable      : 2 calls
--           - In this case, we know then-branch is feasible, but we still have to check if the else-branch is
--
-- In summary, 'sBranch' calls can be expensive, but they can help with the so-called symbolic-termination
-- problem. See "Data.SBV.Examples.Misc.SBranch" for an example.
sBranch :: Mergeable a => SBool -> a -> a -> a
sBranch t a b
  | Just r <- unliteral c = if r then a else b
  | True                  = symbolicMerge False c a b
  where c = reduceInPathCondition t

-- SBV
instance SymWord a => Mergeable (SBV a) where
    symbolicMerge force t a b
      | Just r <- unliteral t
      = if r then a else b
      | force, Just av <- unliteral a, Just bv <- unliteral b, rationalSBVCheck a b, av == bv
      = a
      | True
      = SBV k $ Right $ cache c
      where k = kindOf a
            c st = do swt <- sbvToSW st t
                      case () of
                        () | swt == trueSW  -> sbvToSW st a       -- these two cases should never be needed as we expect symbolicMerge to be
                        () | swt == falseSW -> sbvToSW st b       -- called with symbolic tests, but just in case..
                        () -> do {- It is tempting to record the choice of the test expression here as we branch down to the 'then' and 'else' branches. That is,
                                    when we evaluate 'a', we can make use of the fact that the test expression is True, and similarly we can use the fact that it
                                    is False when b is evaluated. In certain cases this can cut down on symbolic simulation significantly, for instance if
                                    repetitive decisions are made in a recursive loop. Unfortunately, the implementation of this idea is quite tricky, due to
                                    our sharing based implementation. As the 'then' branch is evaluated, we will create many expressions that are likely going
                                    to be "reused" when the 'else' branch is executed. But, it would be *dead wrong* to share those values, as they were "cached"
                                    under the incorrect assumptions. To wit, consider the following:

                                       foo x y = ite (y .== 0) k (k+1)
                                         where k = ite (y .== 0) x (x+1)

                                    When we reduce the 'then' branch of the first ite, we'd record the assumption that y is 0. But while reducing the 'then' branch, we'd
                                    like to share 'k', which would evaluate (correctly) to 'x' under the given assumption. When we backtrack and evaluate the 'else'
                                    branch of the first ite, we'd see 'k' is needed again, and we'd look it up from our sharing map to find (incorrectly) that its value
                                    is 'x', which was stored there under the assumption that y was 0, which no longer holds. Clearly, this is unsound.

                                    A sound implementation would have to precisely track which assumptions were active at the time expressions get shared. That is,
                                    in the above example, we should record that the value of 'k' was cached under the assumption that 'y' is 0. While sound, this
                                    approach unfortunately leads to significant loss of valid sharing when the value itself had nothing to do with the assumption itself.
                                    To wit, consider:

                                       foo x y = ite (y .== 0) k (k+1)
                                         where k = x+5

                                    If we tracked the assumptions, we would recompute 'k' twice, since the branch assumptions would differ. Clearly, there is no need to
                                    re-compute 'k' in this case since its value is independent of y. Note that the whole SBV performance story is based on agressive sharing,
                                    and losing that would have other significant ramifications.

                                    The "proper" solution would be to track, with each shared computation, precisely which assumptions it actually *depends* on, rather
                                    than blindly recording all the assumptions present at that time. SBV's symbolic simulation engine clearly has all the info needed to do this
                                    properly, but the implementation is not straightforward at all. For each subexpression, we would need to chase down its dependencies
                                    transitively, which can require a lot of scanning of the generated program causing major slow-down; thus potentially defeating the
                                    whole purpose of sharing in the first place.

                                    Design choice: Keep it simple, and simply do not track the assumption at all. This will maximize sharing, at the cost of evaluating
                                    unreachable branches. I think the simplicity is more important at this point than efficiency.

                                    Also note that the user can avoid most such issues by properly combining if-then-else's with common conditions together. That is, the
                                    first program above should be written like this:

                                      foo x y = ite (y .== 0) x (x+2)

                                    In general, the following transformations should be done whenever possible:

                                      ite e1 (ite e1 e2 e3) e4  --> ite e1 e2 e4
                                      ite e1 e2 (ite e1 e3 e4)  --> ite e1 e2 e4

                                    This is in accordance with the general rule-of-thumb stating conditionals should be avoided as much as possible. However, we might prefer
                                    the following:

                                      ite e1 (f e2 e4) (f e3 e5) --> f (ite e1 e2 e3) (ite e1 e4 e5)

                                   especially if this expression happens to be inside 'f's body itself (i.e., when f is recursive), since it reduces the number of
                                   recursive calls. Clearly, programming with symbolic simulation in mind is another kind of beast alltogether.
                                 -}
                                 swa <- sbvToSW (st `extendPathCondition` (&&& t))      a -- evaluate 'then' branch
                                 swb <- sbvToSW (st `extendPathCondition` (&&& bnot t)) b -- evaluate 'else' branch
                                 case () of               -- merge:
                                   () | swa == swb                      -> return swa
                                   () | swa == trueSW && swb == falseSW -> return swt
                                   () | swa == falseSW && swb == trueSW -> newExpr st k (SBVApp Not [swt])
                                   ()                                   -> newExpr st k (SBVApp Ite [swt, swa, swb])
    -- Custom version of select that translates to SMT-Lib tables at the base type of words
    select xs err ind
      | SBV _ (Left c) <- ind = case cwVal c of
                                  CWInteger i -> if i < 0 || i >= genericLength xs
                                                 then err
                                                 else xs `genericIndex` i
                                  _           -> error "SBV.select: unsupported real valued select/index expression"
    select xs err ind  = SBV kElt $ Right $ cache r
       where kInd = kindOf ind
             kElt = kindOf err
             r st  = do sws <- mapM (sbvToSW st) xs
                        swe <- sbvToSW st err
                        if all (== swe) sws  -- off-chance that all elts are the same
                           then return swe
                           else do idx <- getTableIndex st kInd kElt sws
                                   swi <- sbvToSW st ind
                                   let len = length xs
                                   newExpr st kElt (SBVApp (LkUp (idx, kInd, kElt, len) swi swe) [])

-- Unit
instance Mergeable () where
   symbolicMerge _ _ _ _ = ()
   select _ _ _ = ()

-- Mergeable instances for List/Maybe/Either/Array are useful, but can
-- throw exceptions if there is no structural matching of the results
-- It's a question whether we should really keep them..

-- Lists
instance Mergeable a => Mergeable [a] where
  symbolicMerge f t xs ys
    | lxs == lys = zipWith (symbolicMerge f t) xs ys
    | True       = error $ "SBV.Mergeable.List: No least-upper-bound for lists of differing size " ++ show (lxs, lys)
    where (lxs, lys) = (length xs, length ys)

-- Maybe
instance Mergeable a => Mergeable (Maybe a) where
  symbolicMerge _ _ Nothing  Nothing  = Nothing
  symbolicMerge f t (Just a) (Just b) = Just $ symbolicMerge f t a b
  symbolicMerge _ _ a b = error $ "SBV.Mergeable.Maybe: No least-upper-bound for " ++ show (k a, k b)
      where k Nothing = "Nothing"
            k _       = "Just"

-- Either
instance (Mergeable a, Mergeable b) => Mergeable (Either a b) where
  symbolicMerge f t (Left a)  (Left b)  = Left  $ symbolicMerge f t a b
  symbolicMerge f t (Right a) (Right b) = Right $ symbolicMerge f t a b
  symbolicMerge _ _ a b = error $ "SBV.Mergeable.Either: No least-upper-bound for " ++ show (k a, k b)
     where k (Left _)  = "Left"
           k (Right _) = "Right"

-- Arrays
instance (Ix a, Mergeable b) => Mergeable (Array a b) where
  symbolicMerge f t a b
    | ba == bb = listArray ba (zipWith (symbolicMerge f t) (elems a) (elems b))
    | True     = error $ "SBV.Mergeable.Array: No least-upper-bound for rangeSizes" ++ show (k ba, k bb)
    where [ba, bb] = map bounds [a, b]
          k = rangeSize

-- Functions
instance Mergeable b => Mergeable (a -> b) where
  symbolicMerge f t g h x = symbolicMerge f t (g x) (h x)
  {- Following definition, while correct, is utterly inefficient. Since the
     application is delayed, this hangs on to the inner list and all the
     impending merges, even when ind is concrete. Thus, it's much better to
     simply use the default definition for the function case.
  -}
  -- select xs err ind = \x -> select (map ($ x) xs) (err x) ind

-- 2-Tuple
instance (Mergeable a, Mergeable b) => Mergeable (a, b) where
  symbolicMerge f t (i0, i1) (j0, j1) = (i i0 j0, i i1 j1)
    where i a b = symbolicMerge f t a b
  select xs (err1, err2) ind = (select as err1 ind, select bs err2 ind)
    where (as, bs) = unzip xs

-- 3-Tuple
instance (Mergeable a, Mergeable b, Mergeable c) => Mergeable (a, b, c) where
  symbolicMerge f t (i0, i1, i2) (j0, j1, j2) = (i i0 j0, i i1 j1, i i2 j2)
    where i a b = symbolicMerge f t a b
  select xs (err1, err2, err3) ind = (select as err1 ind, select bs err2 ind, select cs err3 ind)
    where (as, bs, cs) = unzip3 xs

-- 4-Tuple
instance (Mergeable a, Mergeable b, Mergeable c, Mergeable d) => Mergeable (a, b, c, d) where
  symbolicMerge f t (i0, i1, i2, i3) (j0, j1, j2, j3) = (i i0 j0, i i1 j1, i i2 j2, i i3 j3)
    where i a b = symbolicMerge f t a b
  select xs (err1, err2, err3, err4) ind = (select as err1 ind, select bs err2 ind, select cs err3 ind, select ds err4 ind)
    where (as, bs, cs, ds) = unzip4 xs

-- 5-Tuple
instance (Mergeable a, Mergeable b, Mergeable c, Mergeable d, Mergeable e) => Mergeable (a, b, c, d, e) where
  symbolicMerge f t (i0, i1, i2, i3, i4) (j0, j1, j2, j3, j4) = (i i0 j0, i i1 j1, i i2 j2, i i3 j3, i i4 j4)
    where i a b = symbolicMerge f t a b
  select xs (err1, err2, err3, err4, err5) ind = (select as err1 ind, select bs err2 ind, select cs err3 ind, select ds err4 ind, select es err5 ind)
    where (as, bs, cs, ds, es) = unzip5 xs

-- 6-Tuple
instance (Mergeable a, Mergeable b, Mergeable c, Mergeable d, Mergeable e, Mergeable f) => Mergeable (a, b, c, d, e, f) where
  symbolicMerge f t (i0, i1, i2, i3, i4, i5) (j0, j1, j2, j3, j4, j5) = (i i0 j0, i i1 j1, i i2 j2, i i3 j3, i i4 j4, i i5 j5)
    where i a b = symbolicMerge f t a b
  select xs (err1, err2, err3, err4, err5, err6) ind = (select as err1 ind, select bs err2 ind, select cs err3 ind, select ds err4 ind, select es err5 ind, select fs err6 ind)
    where (as, bs, cs, ds, es, fs) = unzip6 xs

-- 7-Tuple
instance (Mergeable a, Mergeable b, Mergeable c, Mergeable d, Mergeable e, Mergeable f, Mergeable g) => Mergeable (a, b, c, d, e, f, g) where
  symbolicMerge f t (i0, i1, i2, i3, i4, i5, i6) (j0, j1, j2, j3, j4, j5, j6) = (i i0 j0, i i1 j1, i i2 j2, i i3 j3, i i4 j4, i i5 j5, i i6 j6)
    where i a b = symbolicMerge f t a b
  select xs (err1, err2, err3, err4, err5, err6, err7) ind = (select as err1 ind, select bs err2 ind, select cs err3 ind, select ds err4 ind, select es err5 ind, select fs err6 ind, select gs err7 ind)
    where (as, bs, cs, ds, es, fs, gs) = unzip7 xs

-- Bounded instances
instance (SymWord a, Bounded a) => Bounded (SBV a) where
  minBound = literal minBound
  maxBound = literal maxBound

-- Arrays

-- SArrays are both "EqSymbolic" and "Mergeable"
instance EqSymbolic (SArray a b) where
  (SArray _ a) .== (SArray _ b) = SBV KBool $ Right $ cache c
    where c st = do ai <- uncacheAI a st
                    bi <- uncacheAI b st
                    newExpr st KBool (SBVApp (ArrEq ai bi) [])

-- When merging arrays; we'll ignore the force argument. This is arguably
-- the right thing to do as we've too many things and likely we want to keep it efficient.
instance SymWord b => Mergeable (SArray a b) where
  symbolicMerge _ = mergeArrays

-- SFunArrays are only "Mergeable". Although a brute
-- force equality can be defined, any non-toy instance
-- will suffer from efficiency issues; so we don't define it
instance SymArray SFunArray where
  newArray _        = newArray_ -- the name is irrelevant in this case
  newArray_  mbiVal = return $ SFunArray $ const $ fromMaybe (error "Reading from an uninitialized array entry") mbiVal
  readArray  (SFunArray f)     = f
  resetArray (SFunArray _) a   = SFunArray $ const a
  writeArray (SFunArray f) a b = SFunArray (\a' -> ite (a .== a') b (f a'))
  mergeArrays t (SFunArray g) (SFunArray h) = SFunArray (\x -> ite t (g x) (h x))

-- When merging arrays; we'll ignore the force argument. This is arguably
-- the right thing to do as we've too many things and likely we want to keep it efficient.
instance SymWord b => Mergeable (SFunArray a b) where
  symbolicMerge _ = mergeArrays

-- | Uninterpreted constants and functions. An uninterpreted constant is
-- a value that is indexed by its name. The only property the prover assumes
-- about these values are that they are equivalent to themselves; i.e., (for
-- functions) they return the same results when applied to same arguments.
-- We support uninterpreted-functions as a general means of black-box'ing
-- operations that are /irrelevant/ for the purposes of the proof; i.e., when
-- the proofs can be performed without any knowledge about the function itself.
--
-- Minimal complete definition: 'sbvUninterpret'. However, most instances in
-- practice are already provided by SBV, so end-users should not need to define their
-- own instances.
class Uninterpreted a where
  -- | Uninterpret a value, receiving an object that can be used instead. Use this version
  -- when you do not need to add an axiom about this value.
  uninterpret :: String -> a
  -- | Uninterpret a value, only for the purposes of code-generation. For execution
  -- and verification the value is used as is. For code-generation, the alternate
  -- definition is used. This is useful when we want to take advantage of native
  -- libraries on the target languages.
  cgUninterpret :: String -> [String] -> a -> a
  -- | Most generalized form of uninterpretation, this function should not be needed
  -- by end-user-code, but is rather useful for the library development.
  sbvUninterpret :: Maybe ([String], a) -> String -> a

  -- minimal complete definition: 'sbvUninterpret'
  uninterpret             = sbvUninterpret Nothing
  cgUninterpret nm code v = sbvUninterpret (Just (code, v)) nm

mkUninterpreted :: [Kind] -> [SBV ()] -> String -> SBV a
mkUninterpreted ks args nm = SBV ka $ Right $ cache result where
  ka = last ks
  result st = do
    newUninterpreted st nm (SBVType ks) Nothing
    sws <- mapM (sbvToSW st) args
    mapM_ forceSWArg sws
    newExpr st ka $ SBVApp (Uninterpreted nm) sws

-- Plain constants
instance HasKind a => Uninterpreted (SBV a) where
  sbvUninterpret mbCgData nm
     | Just (_, v) <- mbCgData = v
     | True                    = SBV ka $ Right $ cache result
    where ka = kindOf (undefined :: a)
          result st | Just (_, v) <- mbCgData, inProofMode st = sbvToSW st v
                    | True = do newUninterpreted st nm (SBVType [ka]) (fst `fmap` mbCgData)
                                newExpr st ka $ SBVApp (Uninterpreted nm) []

-- Functions of one argument
instance (SymWord b, HasKind a) => Uninterpreted (SBV b -> SBV a) where
  sbvUninterpret mbCgData nm = f
    where f arg0
           | Just (_, v) <- mbCgData, isConcrete arg0
           = v arg0
           | True
           = SBV ka $ Right $ cache result
           where ka = kindOf (undefined :: a)
                 kb = kindOf (undefined :: b)
                 result st | Just (_, v) <- mbCgData, inProofMode st = sbvToSW st (v arg0)
                           | True = do newUninterpreted st nm (SBVType [kb, ka]) (fst `fmap` mbCgData)
                                       sw0 <- sbvToSW st arg0
                                       mapM_ forceSWArg [sw0]
                                       newExpr st ka $ SBVApp (Uninterpreted nm) [sw0]

-- Functions of two arguments
instance (SymWord c, SymWord b, HasKind a) => Uninterpreted (SBV c -> SBV b -> SBV a) where
  sbvUninterpret mbCgData nm = f
    where f arg0 arg1
           | Just (_, v) <- mbCgData, isConcrete arg0, isConcrete arg1
           = v arg0 arg1
           | True
           = SBV ka $ Right $ cache result
           where ka = kindOf (undefined :: a)
                 kb = kindOf (undefined :: b)
                 kc = kindOf (undefined :: c)
                 result st | Just (_, v) <- mbCgData, inProofMode st = sbvToSW st (v arg0 arg1)
                           | True = do newUninterpreted st nm (SBVType [kc, kb, ka]) (fst `fmap` mbCgData)
                                       sw0 <- sbvToSW st arg0
                                       sw1 <- sbvToSW st arg1
                                       mapM_ forceSWArg [sw0, sw1]
                                       newExpr st ka $ SBVApp (Uninterpreted nm) [sw0, sw1]

-- Functions of three arguments
instance (SymWord d, SymWord c, SymWord b, HasKind a) => Uninterpreted (SBV d -> SBV c -> SBV b -> SBV a) where
  sbvUninterpret mbCgData nm = f
    where f arg0 arg1 arg2
           | Just (_, v) <- mbCgData, isConcrete arg0, isConcrete arg1, isConcrete arg2
           = v arg0 arg1 arg2
           | True
           = SBV ka $ Right $ cache result
           where ka = kindOf (undefined :: a)
                 kb = kindOf (undefined :: b)
                 kc = kindOf (undefined :: c)
                 kd = kindOf (undefined :: d)
                 result st | Just (_, v) <- mbCgData, inProofMode st = sbvToSW st (v arg0 arg1 arg2)
                           | True = do newUninterpreted st nm (SBVType [kd, kc, kb, ka]) (fst `fmap` mbCgData)
                                       sw0 <- sbvToSW st arg0
                                       sw1 <- sbvToSW st arg1
                                       sw2 <- sbvToSW st arg2
                                       mapM_ forceSWArg [sw0, sw1, sw2]
                                       newExpr st ka $ SBVApp (Uninterpreted nm) [sw0, sw1, sw2]

-- Functions of four arguments
instance (SymWord e, SymWord d, SymWord c, SymWord b, HasKind a) => Uninterpreted (SBV e -> SBV d -> SBV c -> SBV b -> SBV a) where
  sbvUninterpret mbCgData nm = f
    where f arg0 arg1 arg2 arg3
           | Just (_, v) <- mbCgData, isConcrete arg0, isConcrete arg1, isConcrete arg2, isConcrete arg3
           = v arg0 arg1 arg2 arg3
           | True
           = SBV ka $ Right $ cache result
           where ka = kindOf (undefined :: a)
                 kb = kindOf (undefined :: b)
                 kc = kindOf (undefined :: c)
                 kd = kindOf (undefined :: d)
                 ke = kindOf (undefined :: e)
                 result st | Just (_, v) <- mbCgData, inProofMode st = sbvToSW st (v arg0 arg1 arg2 arg3)
                           | True = do newUninterpreted st nm (SBVType [ke, kd, kc, kb, ka]) (fst `fmap` mbCgData)
                                       sw0 <- sbvToSW st arg0
                                       sw1 <- sbvToSW st arg1
                                       sw2 <- sbvToSW st arg2
                                       sw3 <- sbvToSW st arg3
                                       mapM_ forceSWArg [sw0, sw1, sw2, sw3]
                                       newExpr st ka $ SBVApp (Uninterpreted nm) [sw0, sw1, sw2, sw3]

-- Functions of five arguments
instance (SymWord f, SymWord e, SymWord d, SymWord c, SymWord b, HasKind a) => Uninterpreted (SBV f -> SBV e -> SBV d -> SBV c -> SBV b -> SBV a) where
  sbvUninterpret mbCgData nm = f
    where f arg0 arg1 arg2 arg3 arg4
           | Just (_, v) <- mbCgData, isConcrete arg0, isConcrete arg1, isConcrete arg2, isConcrete arg3, isConcrete arg4
           = v arg0 arg1 arg2 arg3 arg4
           | True
           = SBV ka $ Right $ cache result
           where ka = kindOf (undefined :: a)
                 kb = kindOf (undefined :: b)
                 kc = kindOf (undefined :: c)
                 kd = kindOf (undefined :: d)
                 ke = kindOf (undefined :: e)
                 kf = kindOf (undefined :: f)
                 result st | Just (_, v) <- mbCgData, inProofMode st = sbvToSW st (v arg0 arg1 arg2 arg3 arg4)
                           | True = do newUninterpreted st nm (SBVType [kf, ke, kd, kc, kb, ka]) (fst `fmap` mbCgData)
                                       sw0 <- sbvToSW st arg0
                                       sw1 <- sbvToSW st arg1
                                       sw2 <- sbvToSW st arg2
                                       sw3 <- sbvToSW st arg3
                                       sw4 <- sbvToSW st arg4
                                       mapM_ forceSWArg [sw0, sw1, sw2, sw3, sw4]
                                       newExpr st ka $ SBVApp (Uninterpreted nm) [sw0, sw1, sw2, sw3, sw4]

-- Functions of six arguments
instance (SymWord g, SymWord f, SymWord e, SymWord d, SymWord c, SymWord b, HasKind a) => Uninterpreted (SBV g -> SBV f -> SBV e -> SBV d -> SBV c -> SBV b -> SBV a) where
  sbvUninterpret mbCgData nm = f
    where f arg0 arg1 arg2 arg3 arg4 arg5
           | Just (_, v) <- mbCgData, isConcrete arg0, isConcrete arg1, isConcrete arg2, isConcrete arg3, isConcrete arg4, isConcrete arg5
           = v arg0 arg1 arg2 arg3 arg4 arg5
           | True
           = SBV ka $ Right $ cache result
           where ka = kindOf (undefined :: a)
                 kb = kindOf (undefined :: b)
                 kc = kindOf (undefined :: c)
                 kd = kindOf (undefined :: d)
                 ke = kindOf (undefined :: e)
                 kf = kindOf (undefined :: f)
                 kg = kindOf (undefined :: g)
                 result st | Just (_, v) <- mbCgData, inProofMode st = sbvToSW st (v arg0 arg1 arg2 arg3 arg4 arg5)
                           | True = do newUninterpreted st nm (SBVType [kg, kf, ke, kd, kc, kb, ka]) (fst `fmap` mbCgData)
                                       sw0 <- sbvToSW st arg0
                                       sw1 <- sbvToSW st arg1
                                       sw2 <- sbvToSW st arg2
                                       sw3 <- sbvToSW st arg3
                                       sw4 <- sbvToSW st arg4
                                       sw5 <- sbvToSW st arg5
                                       mapM_ forceSWArg [sw0, sw1, sw2, sw3, sw4, sw5]
                                       newExpr st ka $ SBVApp (Uninterpreted nm) [sw0, sw1, sw2, sw3, sw4, sw5]

-- Functions of seven arguments
instance (SymWord h, SymWord g, SymWord f, SymWord e, SymWord d, SymWord c, SymWord b, HasKind a)
            => Uninterpreted (SBV h -> SBV g -> SBV f -> SBV e -> SBV d -> SBV c -> SBV b -> SBV a) where
  sbvUninterpret mbCgData nm = f
    where f arg0 arg1 arg2 arg3 arg4 arg5 arg6
           | Just (_, v) <- mbCgData, isConcrete arg0, isConcrete arg1, isConcrete arg2, isConcrete arg3, isConcrete arg4, isConcrete arg5, isConcrete arg6
           = v arg0 arg1 arg2 arg3 arg4 arg5 arg6
           | True
           = SBV ka $ Right $ cache result
           where ka = kindOf (undefined :: a)
                 kb = kindOf (undefined :: b)
                 kc = kindOf (undefined :: c)
                 kd = kindOf (undefined :: d)
                 ke = kindOf (undefined :: e)
                 kf = kindOf (undefined :: f)
                 kg = kindOf (undefined :: g)
                 kh = kindOf (undefined :: h)
                 result st | Just (_, v) <- mbCgData, inProofMode st = sbvToSW st (v arg0 arg1 arg2 arg3 arg4 arg5 arg6)
                          | True = do newUninterpreted st nm (SBVType [kh, kg, kf, ke, kd, kc, kb, ka]) (fst `fmap` mbCgData)
                                      sw0 <- sbvToSW st arg0
                                      sw1 <- sbvToSW st arg1
                                      sw2 <- sbvToSW st arg2
                                      sw3 <- sbvToSW st arg3
                                      sw4 <- sbvToSW st arg4
                                      sw5 <- sbvToSW st arg5
                                      sw6 <- sbvToSW st arg6
                                      mapM_ forceSWArg [sw0, sw1, sw2, sw3, sw4, sw5, sw6]
                                      newExpr st ka $ SBVApp (Uninterpreted nm) [sw0, sw1, sw2, sw3, sw4, sw5, sw6]

-- Uncurried functions of two arguments
instance (SymWord c, SymWord b, HasKind a) => Uninterpreted ((SBV c, SBV b) -> SBV a) where
  sbvUninterpret mbCgData nm = let f = sbvUninterpret (uc2 `fmap` mbCgData) nm in uncurry f
    where uc2 (cs, fn) = (cs, curry fn)

-- Uncurried functions of three arguments
instance (SymWord d, SymWord c, SymWord b, HasKind a) => Uninterpreted ((SBV d, SBV c, SBV b) -> SBV a) where
  sbvUninterpret mbCgData nm = let f = sbvUninterpret (uc3 `fmap` mbCgData) nm in \(arg0, arg1, arg2) -> f arg0 arg1 arg2
    where uc3 (cs, fn) = (cs, \a b c -> fn (a, b, c))

-- Uncurried functions of four arguments
instance (SymWord e, SymWord d, SymWord c, SymWord b, HasKind a)
            => Uninterpreted ((SBV e, SBV d, SBV c, SBV b) -> SBV a) where
  sbvUninterpret mbCgData nm = let f = sbvUninterpret (uc4 `fmap` mbCgData) nm in \(arg0, arg1, arg2, arg3) -> f arg0 arg1 arg2 arg3
    where uc4 (cs, fn) = (cs, \a b c d -> fn (a, b, c, d))

-- Uncurried functions of five arguments
instance (SymWord f, SymWord e, SymWord d, SymWord c, SymWord b, HasKind a)
            => Uninterpreted ((SBV f, SBV e, SBV d, SBV c, SBV b) -> SBV a) where
  sbvUninterpret mbCgData nm = let f = sbvUninterpret (uc5 `fmap` mbCgData) nm in \(arg0, arg1, arg2, arg3, arg4) -> f arg0 arg1 arg2 arg3 arg4
    where uc5 (cs, fn) = (cs, \a b c d e -> fn (a, b, c, d, e))

-- Uncurried functions of six arguments
instance (SymWord g, SymWord f, SymWord e, SymWord d, SymWord c, SymWord b, HasKind a)
            => Uninterpreted ((SBV g, SBV f, SBV e, SBV d, SBV c, SBV b) -> SBV a) where
  sbvUninterpret mbCgData nm = let f = sbvUninterpret (uc6 `fmap` mbCgData) nm in \(arg0, arg1, arg2, arg3, arg4, arg5) -> f arg0 arg1 arg2 arg3 arg4 arg5
    where uc6 (cs, fn) = (cs, \a b c d e f -> fn (a, b, c, d, e, f))

-- Uncurried functions of seven arguments
instance (SymWord h, SymWord g, SymWord f, SymWord e, SymWord d, SymWord c, SymWord b, HasKind a)
            => Uninterpreted ((SBV h, SBV g, SBV f, SBV e, SBV d, SBV c, SBV b) -> SBV a) where
  sbvUninterpret mbCgData nm = let f = sbvUninterpret (uc7 `fmap` mbCgData) nm in \(arg0, arg1, arg2, arg3, arg4, arg5, arg6) -> f arg0 arg1 arg2 arg3 arg4 arg5 arg6
    where uc7 (cs, fn) = (cs, \a b c d e f g -> fn (a, b, c, d, e, f, g))

-- | Adding arbitrary constraints. When adding constraints, one has to be careful about
-- making sure they are not inconsistent. The function 'isVacuous' can be use for this purpose.
-- Here is an example. Consider the following predicate:
--
-- >>> let pred = do { x <- forall "x"; constrain $ x .< x; return $ x .>= (5 :: SWord8) }
--
-- This predicate asserts that all 8-bit values are larger than 5, subject to the constraint that the
-- values considered satisfy @x .< x@, i.e., they are less than themselves. Since there are no values that
-- satisfy this constraint, the proof will pass vacuously:
--
-- >>> prove pred
-- Q.E.D.
--
-- We can use 'isVacuous' to make sure to see that the pass was vacuous:
--
-- >>> isVacuous pred
-- True
--
-- While the above example is trivial, things can get complicated if there are multiple constraints with
-- non-straightforward relations; so if constraints are used one should make sure to check the predicate
-- is not vacuously true. Here's an example that is not vacuous:
--
--  >>> let pred' = do { x <- forall "x"; constrain $ x .> 6; return $ x .>= (5 :: SWord8) }
--
-- This time the proof passes as expected:
--
--  >>> prove pred'
--  Q.E.D.
--
-- And the proof is not vacuous:
--
--  >>> isVacuous pred'
--  False
constrain :: SBool -> Symbolic ()
constrain c = addConstraint Nothing c (bnot c)

-- | Adding a probabilistic constraint. The 'Double' argument is the probability
-- threshold. Probabilistic constraints are useful for 'genTest' and 'quickCheck'
-- calls where we restrict our attention to /interesting/ parts of the input domain.
pConstrain :: Double -> SBool -> Symbolic ()
pConstrain t c = addConstraint (Just t) c (bnot c)

-- | Boolean symbolic reduction. See if we can reduce a boolean condition to true/false
-- using the path context information, by making external calls to the SMT solvers. Used in the
-- implementation of 'sBranch'.
reduceInPathCondition :: SBool -> SBool
reduceInPathCondition b
  | isConcrete b = b -- No reduction is needed, already a concrete value
  | True         = SBV k $ Right $ cache c
  where k    = kindOf b
        c st = do -- Now that we know our boolean is not obviously true/false. Need to make an external
                  -- call to the SMT solver to see if we can prove it is necessarily one of those
                  let pc = getPathCondition st
                  satTrue <- isSBranchFeasibleInState st "then" (pc &&& b)
                  if not satTrue
                     then return falseSW          -- condition is not satisfiable; so it must be necessarily False.
                     else do satFalse <- isSBranchFeasibleInState st "else" (pc &&& bnot b)
                             if not satFalse      -- negation of the condition is not satisfiable; so it must be necessarily True.
                                then return trueSW
                                else sbvToSW st b -- condition is not necessarily always True/False. So, keep symbolic.

-- Quickcheck interface on symbolic-booleans..
instance Testable SBool where
  property (SBV _ (Left b)) = property (cwToBool b)
  property s                = error $ "Cannot quick-check in the presence of uninterpreted constants! (" ++ show s ++ ")"

instance Testable (Symbolic SBool) where
  property m = QC.whenFail (putStrLn msg) $ QC.monadicIO test
    where runOnce g = do (r, Result _ tvals _ _ cs _ _ _ _ _ cstrs _) <- runSymbolic' (Concrete g) m
                         let cval = fromMaybe (error "Cannot quick-check in the presence of uninterpeted constants!") . (`lookup` cs)
                             cond = all (cwToBool . cval) cstrs
                         when (isSymbolic r) $ error $ "Cannot quick-check in the presence of uninterpreted constants! (" ++ show r ++ ")"
                         if cond then if r `isConcretely` id
                                         then return False
                                         else do putStrLn $ complain tvals
                                                 return True
                                 else runOnce g -- cstrs failed, go again
          test = do die <- QC.run $ newStdGen >>= runOnce
                    when die $ fail "Falsifiable"
          msg = "*** SBV: See the custom counter example reported above."
          complain []     = "*** SBV Counter Example: Predicate contains no universally quantified variables."
          complain qcInfo = intercalate "\n" $ "*** SBV Counter Example:" : map (("  " ++) . info) qcInfo
            where maxLen = maximum (0:[length s | (s, _) <- qcInfo])
                  shN s = s ++ replicate (maxLen - length s) ' '
                  info (n, cw) = shN n ++ " = " ++ show cw

-- | Explicit sharing combinator. The SBV library has internal caching/hash-consing mechanisms
-- built in, based on Andy Gill's type-safe obervable sharing technique (see: <http://ittc.ku.edu/~andygill/paper.php?label=DSLExtract09>).
-- However, there might be times where being explicit on the sharing can help, especially in experimental code. The 'slet' combinator
-- ensures that its first argument is computed once and passed on to its continuation, explicitly indicating the intent of sharing. Most
-- use cases of the SBV library should simply use Haskell's @let@ construct for this purpose.
slet :: (HasKind a, HasKind b) => SBV a -> (SBV a -> SBV b) -> SBV b
slet x f = SBV k $ Right $ cache r
    where k    = kindOf (undefined `asTypeOf` f x)
          r st = do xsw <- sbvToSW st x
                    let xsbv = SBV (kindOf x) (Right (cache (const (return xsw))))
                        res  = f xsbv
                    sbvToSW st res

-- We use 'isVacuous' and 'prove' only for the "test" section in this file, and GHC complains about that. So, this shuts it up.
__unused :: a
__unused = error "__unused" (isVacuous :: SBool -> IO Bool) (prove :: SBool -> IO ThmResult)

{-# ANN module "HLint: ignore Eta reduce"         #-}
{-# ANN module "HLint: ignore Reduce duplication" #-}
