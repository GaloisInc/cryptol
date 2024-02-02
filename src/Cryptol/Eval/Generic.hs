-- |
-- Module      :  Cryptol.Eval.Generic
-- Copyright   :  (c) 2013-2020 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE BangPatterns #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
-- See Note [-Wincomplete-uni-patterns and irrefutable patterns] in Cryptol.TypeCheck.TypePat
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Cryptol.Eval.Generic where

import qualified Control.Exception as X
import Control.Monad(join)
import Control.Monad.IO.Class (MonadIO(..))
import System.Random.TF.Gen (seedTFGen)

import Data.Bits ((.&.), shiftR)
import Data.Maybe (fromMaybe)
import qualified Data.Map.Strict as Map
import Data.Map(Map)
import Data.Ratio ((%))

import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Solver.InfNat (Nat'(..),nMul,nAdd)
import Cryptol.Backend
import Cryptol.Backend.Concrete (Concrete(..))
import Cryptol.Backend.Monad( Eval, evalPanic, EvalError(..), Unsupported(..) )
import Cryptol.Backend.SeqMap
import Cryptol.Backend.WordValue
import Cryptol.Testing.Random( randomValue )

import Cryptol.Eval.Prims
import Cryptol.Eval.Type
import Cryptol.Eval.Value
import Cryptol.Utils.Ident (PrimIdent, prelPrim, floatPrim)
import Cryptol.Utils.Logger(logPrint)
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.PP
import Cryptol.Utils.RecordMap


{-# SPECIALIZE mkLit :: Concrete -> TValue -> Integer -> Eval (GenValue Concrete)
  #-}

-- | Make a numeric literal value at the given type.
mkLit :: Backend sym => sym -> TValue -> Integer -> SEval sym (GenValue sym)
mkLit sym ty i =
  case ty of
    TVBit                        -> pure $ VBit (bitLit sym (i > 0))
    TVInteger                    -> VInteger <$> integerLit sym i
    TVIntMod m
      | m == 0                   -> evalPanic "mkLit" ["0 modulus not allowed"]
      | otherwise                -> VInteger <$> integerLit sym (i `mod` m)
    TVFloat e p                  -> VFloat <$> fpLit sym e p (fromInteger i)
    TVSeq w TVBit                -> word sym w i
    TVRational                   -> VRational <$> (intToRational sym =<< integerLit sym i)
    _                            -> evalPanic "Cryptol.Eval.Prim.evalConst"
                                    [ "Invalid type for number" ]

{-# SPECIALIZE ecNumberV :: Concrete -> Prim Concrete
  #-}

-- | Make a numeric constant.
ecNumberV :: Backend sym => sym -> Prim sym
ecNumberV sym =
  PNumPoly \valT ->
  PTyPoly \ty ->
  PPrim
  case valT of
    Nat v -> mkLit sym ty v
    _ -> evalPanic "Cryptol.Eval.Prim.evalConst"
             ["Unexpected Inf in constant."
             , show valT
             , show ty
             ]


{-# SPECIALIZE intV :: Concrete -> Integer -> TValue -> Eval (GenValue Concrete)
  #-}
intV :: Backend sym => sym -> SInteger sym -> TValue -> SEval sym (GenValue sym)
intV sym i =
  ringNullary sym
    (\w -> wordFromInt sym w i)
    (pure i)
    (\m -> intToZn sym m i)
    (intToRational sym i)
    (\e p -> fpRndMode sym >>= \r -> fpFromInteger sym e p r i)

{-# SPECIALIZE ratioV :: Concrete -> Prim Concrete #-}
ratioV :: Backend sym => sym -> Prim sym
ratioV sym =
  PFun   \x ->
  PFun   \y ->
  PPrim
    do x' <- fromVInteger <$> x
       y' <- fromVInteger <$> y
       VRational <$> ratio sym x' y'

{-# SPECIALIZE ecFractionV :: Concrete -> Prim Concrete
  #-}
ecFractionV :: Backend sym => sym -> Prim sym
ecFractionV sym =
  PFinPoly \n  ->
  PFinPoly \d  ->
  PFinPoly \_r ->
  PTyPoly  \ty ->
  PPrim
    case ty of
      TVFloat e p -> VFloat <$> fpLit sym e p (n % d)
      TVRational ->
        do x <- integerLit sym n
           y <- integerLit sym d
           VRational <$> ratio sym x y

      _ -> evalPanic "ecFractionV"
            [ "Unexpected `FLiteral` type: " ++ show ty ]



{-# SPECIALIZE fromZV :: Concrete -> Prim Concrete #-}
fromZV :: Backend sym => sym -> Prim sym
fromZV sym =
  PFinPoly \n ->
  PFun     \v ->
  PPrim
    (VInteger <$> (znToInt sym n . fromVInteger =<< v))

-- Operation Lifting -----------------------------------------------------------


type Binary sym = TValue -> GenValue sym -> GenValue sym -> SEval sym (GenValue sym)

{-# SPECIALIZE binary :: Binary Concrete -> Prim Concrete
  #-}
binary :: Backend sym => Binary sym -> Prim sym
binary f = PTyPoly \ty ->
           PFun    \a  ->
           PFun    \b  ->
           PPrim $
             do x <- a
                y <- b
                f ty x y

type Unary sym = TValue -> GenValue sym -> SEval sym (GenValue sym)

{-# SPECIALIZE unary :: Unary Concrete -> Prim Concrete
  #-}
unary :: Backend sym => Unary sym -> Prim sym
unary f = PTyPoly \ty ->
          PFun    \a  ->
          PPrim (f ty =<< a)

type BinWord sym = Integer -> SWord sym -> SWord sym -> SEval sym (SWord sym)

{-# SPECIALIZE ringBinary :: Concrete -> BinWord Concrete ->
      (SInteger Concrete -> SInteger Concrete -> SEval Concrete (SInteger Concrete)) ->
      (Integer -> SInteger Concrete -> SInteger Concrete -> SEval Concrete (SInteger Concrete)) ->
      (SRational Concrete -> SRational Concrete -> SEval Concrete (SRational Concrete)) ->
      (SFloat Concrete -> SFloat Concrete -> SEval Concrete (SFloat Concrete)) ->
      Binary Concrete
  #-}

ringBinary :: forall sym.
  Backend sym =>
  sym ->
  BinWord sym ->
  (SInteger sym -> SInteger sym -> SEval sym (SInteger sym)) ->
  (Integer -> SInteger sym -> SInteger sym -> SEval sym (SInteger sym)) ->
  (SRational sym -> SRational sym -> SEval sym (SRational sym)) ->
  (SFloat sym -> SFloat sym -> SEval sym (SFloat sym)) ->
  Binary sym
ringBinary sym opw opi opz opq opfp = loop
  where
  loop' :: TValue
        -> SEval sym (GenValue sym)
        -> SEval sym (GenValue sym)
        -> SEval sym (GenValue sym)
  loop' ty l r = join (loop ty <$> l <*> r)

  loop :: TValue
       -> GenValue sym
       -> GenValue sym
       -> SEval sym (GenValue sym)
  loop ty l r = case ty of
    TVBit ->
      evalPanic "ringBinary" ["Bit not in class Ring"]

    TVInteger ->
      VInteger <$> opi (fromVInteger l) (fromVInteger r)

    TVIntMod n ->
      VInteger <$> opz n (fromVInteger l) (fromVInteger r)

    TVFloat {} ->
      VFloat <$> opfp (fromVFloat l) (fromVFloat r)

    TVRational ->
      VRational <$> opq (fromVRational l) (fromVRational r)

    TVArray{} ->
      evalPanic "arithBinary" ["Array not in class Ring"]

    TVSeq w a
      -- words and finite sequences
      | isTBit a -> do
                  lw <- fromVWord sym "ringLeft" l
                  rw <- fromVWord sym "ringRight" r
                  stk <- sGetCallStack sym
                  VWord w . wordVal <$> (sWithCallStack sym stk (opw w lw rw))
      | otherwise -> VSeq w <$> (join (zipSeqMap sym (loop a) (Nat w) <$>
                                      (fromSeq "ringBinary left" l) <*>
                                      (fromSeq "ringBinary right" r)))

    TVStream a ->
      -- streams
      VStream <$> (join (zipSeqMap sym (loop a) Inf <$>
                             (fromSeq "ringBinary left" l) <*>
                             (fromSeq "ringBinary right" r)))

    -- functions
    TVFun _ ety ->
      lam sym $ \ x -> loop' ety (fromVFun sym l x) (fromVFun sym r x)

    -- tuples
    TVTuple tys ->
      do ls <- mapM (sDelay sym) (fromVTuple l)
         rs <- mapM (sDelay sym) (fromVTuple r)
         return $ VTuple (zipWith3 loop' tys ls rs)

    -- records
    TVRec fs ->
      do VRecord <$>
            traverseRecordMap
              (\f fty -> sDelay sym (loop' fty (lookupRecord f l) (lookupRecord f r)))
              fs

    TVNominal {} ->
      evalPanic "ringBinary" ["Nominal type not in `Ring`"]

type UnaryWord sym = Integer -> SWord sym -> SEval sym (SWord sym)


{-# SPECIALIZE ringUnary ::
  Concrete ->
  UnaryWord Concrete ->
  (SInteger Concrete -> SEval Concrete (SInteger Concrete)) ->
  (Integer -> SInteger Concrete -> SEval Concrete (SInteger Concrete)) ->
  (SRational Concrete -> SEval Concrete (SRational Concrete)) ->
  (SFloat Concrete -> SEval Concrete (SFloat Concrete)) ->
  Unary Concrete
  #-}
ringUnary :: forall sym.
  Backend sym =>
  sym ->
  UnaryWord sym ->
  (SInteger sym -> SEval sym (SInteger sym)) ->
  (Integer -> SInteger sym -> SEval sym (SInteger sym)) ->
  (SRational sym -> SEval sym (SRational sym)) ->
  (SFloat sym -> SEval sym (SFloat sym)) ->
  Unary sym
ringUnary sym opw opi opz opq opfp = loop
  where
  loop' :: TValue -> SEval sym (GenValue sym) -> SEval sym (GenValue sym)
  loop' ty v = loop ty =<< v

  loop :: TValue -> GenValue sym -> SEval sym (GenValue sym)
  loop ty v = case ty of

    TVBit ->
      evalPanic "ringUnary" ["Bit not in class Ring"]

    TVInteger ->
      VInteger <$> opi (fromVInteger v)

    TVIntMod n ->
      VInteger <$> opz n (fromVInteger v)

    TVFloat {} ->
      VFloat <$> opfp (fromVFloat v)

    TVRational ->
      VRational <$> opq (fromVRational v)

    TVArray{} ->
      evalPanic "arithUnary" ["Array not in class Ring"]

    TVSeq w a
      -- words and finite sequences
      | isTBit a -> do
              wx <- fromVWord sym "ringUnary" v
              stk <- sGetCallStack sym
              VWord w . wordVal <$> sWithCallStack sym stk (opw w wx)
      | otherwise -> VSeq w <$> (mapSeqMap sym (loop a) (Nat w) =<< fromSeq "ringUnary" v)

    TVStream a ->
      VStream <$> (mapSeqMap sym (loop a) Inf =<< fromSeq "ringUnary" v)

    -- functions
    TVFun _ ety ->
      lam sym $ \ y -> loop' ety (fromVFun sym v y)

    -- tuples
    TVTuple tys ->
      do as <- mapM (sDelay sym) (fromVTuple v)
         return $ VTuple (zipWith loop' tys as)

    -- records
    TVRec fs ->
      VRecord <$>
        traverseRecordMap
          (\f fty -> sDelay sym (loop' fty (lookupRecord f v)))
          fs

    TVNominal {} -> evalPanic "ringUnary" ["Nominal type not in `Ring`"]


{-# SPECIALIZE ringNullary ::
  Concrete ->
  (Integer -> SEval Concrete (SWord Concrete)) ->
  SEval Concrete (SInteger Concrete) ->
  (Integer -> SEval Concrete (SInteger Concrete)) ->
  SEval Concrete (SRational Concrete) ->
  (Integer -> Integer -> SEval Concrete (SFloat Concrete)) ->
  TValue ->
  SEval Concrete (GenValue Concrete)
  #-}

ringNullary :: forall sym.
  Backend sym =>
  sym ->
  (Integer -> SEval sym (SWord sym)) ->
  SEval sym (SInteger sym) ->
  (Integer -> SEval sym (SInteger sym)) ->
  SEval sym (SRational sym) ->
  (Integer -> Integer -> SEval sym (SFloat sym)) ->
  TValue ->
  SEval sym (GenValue sym)
ringNullary sym opw opi opz opq opfp = loop
  where
    loop :: TValue -> SEval sym (GenValue sym)
    loop ty =
      case ty of
        TVBit -> evalPanic "ringNullary" ["Bit not in class Ring"]

        TVInteger -> VInteger <$> opi

        TVIntMod n -> VInteger <$> opz n

        TVFloat e p -> VFloat <$> opfp e p

        TVRational -> VRational <$> opq

        TVArray{} -> evalPanic "arithNullary" ["Array not in class Ring"]

        TVSeq w a
          -- words and finite sequences
          | isTBit a ->
             do stk <- sGetCallStack sym
                VWord w . wordVal <$> sWithCallStack sym stk (opw w)
          | otherwise ->
             do v <- sDelay sym (loop a)
                pure $ VSeq w $ indexSeqMap \_i -> v

        TVStream a ->
             do v <- sDelay sym (loop a)
                pure $ VStream $ indexSeqMap \_i -> v

        TVFun _ b ->
             do v <- sDelay sym (loop b)
                lam sym (const v)

        TVTuple tys ->
             do xs <- mapM (sDelay sym . loop) tys
                pure $ VTuple xs

        TVRec fs ->
             do xs <- traverse (sDelay sym . loop) fs
                pure $ VRecord xs

        TVNominal {} ->
          evalPanic "ringNullary" ["Nominal type not in `Ring`"]

{-# SPECIALIZE integralBinary :: Concrete -> BinWord Concrete ->
      (SInteger Concrete -> SInteger Concrete -> SEval Concrete (SInteger Concrete)) ->
      Binary Concrete
  #-}

integralBinary :: forall sym.
  Backend sym =>
  sym ->
  BinWord sym ->
  (SInteger sym -> SInteger sym -> SEval sym (SInteger sym)) ->
  Binary sym
integralBinary sym opw opi ty l r = case ty of
    TVInteger ->
      VInteger <$> opi (fromVInteger l) (fromVInteger r)

    -- bitvectors
    TVSeq w a
      | isTBit a ->
          do wl <- fromVWord sym "integralBinary left" l
             wr <- fromVWord sym "integralBinary right" r
             stk <- sGetCallStack sym
             VWord w . wordVal <$> sWithCallStack sym stk (opw w wl wr)

    _ -> evalPanic "integralBinary" [show ty ++ " not int class `Integral`"]


---------------------------------------------------------------------------
-- Ring

{-# SPECIALIZE fromIntegerV :: Concrete -> Prim Concrete
  #-}
-- | Convert an unbounded integer to a value in Ring
fromIntegerV :: Backend sym => sym -> Prim sym
fromIntegerV sym =
  PTyPoly \a ->
  PFun    \v ->
  PPrim
    do i <- fromVInteger <$> v
       intV sym i a

{-# INLINE addV #-}
addV :: Backend sym => sym -> Binary sym
addV sym = ringBinary sym opw opi opz opq opfp
  where
    opw _w x y = wordPlus sym x y
    opi x y = intPlus sym x y
    opz m x y = znPlus sym m x y
    opq x y = rationalAdd sym x y
    opfp x y = fpRndMode sym >>= \r -> fpPlus sym r x y

{-# INLINE subV #-}
subV :: Backend sym => sym -> Binary sym
subV sym = ringBinary sym opw opi opz opq opfp
  where
    opw _w x y = wordMinus sym x y
    opi x y = intMinus sym x y
    opz m x y = znMinus sym m x y
    opq x y = rationalSub sym x y
    opfp x y = fpRndMode sym >>= \r -> fpMinus sym r x y

{-# INLINE negateV #-}
negateV :: Backend sym => sym -> Unary sym
negateV sym = ringUnary sym opw opi opz opq opfp
  where
    opw _w x = wordNegate sym x
    opi x = intNegate sym x
    opz m x = znNegate sym m x
    opq x = rationalNegate sym x
    opfp x = fpNeg sym x

{-# INLINE mulV #-}
mulV :: Backend sym => sym -> Binary sym
mulV sym = ringBinary sym opw opi opz opq opfp
  where
    opw _w x y = wordMult sym x y
    opi x y = intMult sym x y
    opz m x y = znMult sym m x y
    opq x y = rationalMul sym x y
    opfp x y = fpRndMode sym >>= \r -> fpMult sym r x y

--------------------------------------------------
-- Integral

{-# INLINE divV #-}
divV :: Backend sym => sym -> Binary sym
divV sym = integralBinary sym opw opi
  where
    opw _w x y = wordDiv sym x y
    opi x y = intDiv sym x y

{-# SPECIALIZE expV :: Concrete -> Prim Concrete #-}
expV :: Backend sym => sym -> Prim sym
expV sym =
  PTyPoly \aty ->
  PTyPoly \ety ->
  PFun    \am ->
  PFun    \em ->
  PPrim
     do a <- am
        e <- em
        case ety of
          TVInteger ->
            let ei = fromVInteger e in
            case integerAsLit sym ei of
              Just n
                | n == 0 ->
                   do onei <- integerLit sym 1
                      intV sym onei aty

                | n > 0 ->
                    do (_,ebits) <- enumerateIntBits' sym n ei
                       computeExponent sym aty a ebits

                | otherwise -> raiseError sym NegativeExponent

              Nothing -> liftIO (X.throw (UnsupportedSymbolicOp "integer exponentiation"))

          TVSeq _w el | isTBit el ->
            do ebits <- enumerateWordValue sym (fromWordVal "(^^)" e)
               computeExponent sym aty a ebits

          _ -> evalPanic "expV" [show ety ++ " not int class `Integral`"]


{-# SPECIALIZE computeExponent ::
      Concrete -> TValue -> GenValue Concrete -> [SBit Concrete] -> SEval Concrete (GenValue Concrete)
  #-}
computeExponent :: Backend sym =>
  sym -> TValue -> GenValue sym -> [SBit sym] -> SEval sym (GenValue sym)
computeExponent sym aty a bs0 =
  do onei <- integerLit sym 1
     one <- intV sym onei aty
     loop one (dropLeadingZeros bs0)

 where
 dropLeadingZeros [] = []
 dropLeadingZeros (b:bs)
   | Just False <- bitAsLit sym b = dropLeadingZeros bs
   | otherwise = (b:bs)

 loop acc [] = return acc
 loop acc (b:bs) =
   do sq <- mulV sym aty acc acc
      acc' <- iteValue sym b
                (mulV sym aty a sq)
                (pure sq)
      loop acc' bs

{-# INLINE modV #-}
modV :: Backend sym => sym -> Binary sym
modV sym = integralBinary sym opw opi
  where
    opw _w x y = wordMod sym x y
    opi x y = intMod sym x y

{-# SPECIALIZE toIntegerV :: Concrete -> Prim Concrete #-}
-- | Convert a word to a non-negative integer.
toIntegerV :: Backend sym => sym -> Prim sym
toIntegerV sym =
  PTyPoly \a ->
  PFun    \v ->
  PPrim
    case a of
      TVSeq _w el | isTBit el ->
        VInteger <$> (wordToInt sym =<< (fromVWord sym "toInteger" =<< v))
      TVInteger -> v
      _ -> evalPanic "toInteger" [show a ++ " not in class `Integral`"]

-----------------------------------------------------------------------------
-- Field

{-# SPECIALIZE recipV :: Concrete -> Prim Concrete #-}
recipV :: Backend sym => sym -> Prim sym
recipV sym =
  PTyPoly \a ->
  PFun    \x ->
  PPrim
    case a of
      TVRational -> VRational <$> (rationalRecip sym . fromVRational =<< x)
      TVFloat e p ->
        do one <- fpLit sym e p 1
           r   <- fpRndMode sym
           xv  <- fromVFloat <$> x
           VFloat <$> fpDiv sym r one xv
      TVIntMod m -> VInteger <$> (znRecip sym m . fromVInteger =<< x)
      _ -> evalPanic "recip"  [show a ++ "is not a Field"]

{-# SPECIALIZE fieldDivideV :: Concrete -> Prim Concrete #-}
fieldDivideV :: Backend sym => sym -> Prim sym
fieldDivideV sym =
  PTyPoly \a ->
  PFun    \x ->
  PFun    \y ->
  PPrim
    case a of
      TVRational ->
        do x' <- fromVRational <$> x
           y' <- fromVRational <$> y
           VRational <$> rationalDivide sym x' y'
      TVFloat _e _p ->
        do xv <- fromVFloat <$> x
           yv <- fromVFloat <$> y
           r  <- fpRndMode sym
           VFloat <$> fpDiv sym r xv yv
      TVIntMod m ->
        do x' <- fromVInteger <$> x
           y' <- fromVInteger <$> y
           yinv <- znRecip sym m y'
           VInteger <$> znMult sym m x' yinv

      _ -> evalPanic "recip"  [show a ++ "is not a Field"]

--------------------------------------------------------------
-- Round

{-# SPECIALIZE roundOp ::
  Concrete ->
  String ->
  (SRational Concrete -> SEval Concrete (SInteger Concrete)) ->
  (SFloat Concrete -> SEval Concrete (SInteger Concrete)) ->
  Unary Concrete #-}

roundOp ::
  Backend sym =>
  sym ->
  String ->
  (SRational sym -> SEval sym (SInteger sym)) ->
  (SFloat sym -> SEval sym (SInteger sym)) ->
  Unary sym
roundOp _sym nm qop opfp ty v =
  case ty of
    TVRational  -> VInteger <$> (qop (fromVRational v))
    TVFloat _ _ -> VInteger <$> opfp (fromVFloat v)
    _ -> evalPanic nm [show ty ++ " is not a Field"]

{-# INLINE floorV #-}
floorV :: Backend sym => sym -> Unary sym
floorV sym = roundOp sym "floor" opq opfp
  where
  opq = rationalFloor sym
  opfp = \x -> fpRndRTN sym >>= \r -> fpToInteger sym "floor" r x

{-# INLINE ceilingV #-}
ceilingV :: Backend sym => sym -> Unary sym
ceilingV sym = roundOp sym "ceiling" opq opfp
  where
  opq = rationalCeiling sym
  opfp = \x -> fpRndRTP sym >>= \r -> fpToInteger sym "ceiling" r x

{-# INLINE truncV #-}
truncV :: Backend sym => sym -> Unary sym
truncV sym = roundOp sym "trunc" opq opfp
  where
  opq = rationalTrunc sym
  opfp = \x -> fpRndRTZ sym >>= \r -> fpToInteger sym "trunc" r x

{-# INLINE roundAwayV #-}
roundAwayV :: Backend sym => sym -> Unary sym
roundAwayV sym = roundOp sym "roundAway" opq opfp
  where
  opq = rationalRoundAway sym
  opfp = \x -> fpRndRNA sym >>= \r -> fpToInteger sym "roundAway" r x

{-# INLINE roundToEvenV #-}
roundToEvenV :: Backend sym => sym -> Unary sym
roundToEvenV sym = roundOp sym "roundToEven" opq opfp
  where
  opq = rationalRoundToEven sym
  opfp = \x -> fpRndRNE sym >>= \r -> fpToInteger sym "roundToEven" r x

--------------------------------------------------------------
-- Logic

{-# INLINE andV #-}
andV :: Backend sym => sym -> Binary sym
andV sym = logicBinary sym (bitAnd sym) (wordAnd sym)

{-# INLINE orV #-}
orV :: Backend sym => sym -> Binary sym
orV sym = logicBinary sym (bitOr sym) (wordOr sym)

{-# INLINE xorV #-}
xorV :: Backend sym => sym -> Binary sym
xorV sym = logicBinary sym (bitXor sym) (wordXor sym)

{-# INLINE complementV #-}
complementV :: Backend sym => sym -> Unary sym
complementV sym = logicUnary sym (bitComplement sym) (wordComplement sym)

-- Bitvector signed div and modulus

{-# INLINE lg2V #-}
lg2V :: Backend sym => sym -> Prim sym
lg2V sym =
  PFinPoly \w ->
  PWordFun \x ->
  PPrim (VWord w . wordVal <$> wordLg2 sym x)

{-# SPECIALIZE sdivV :: Concrete -> Prim Concrete #-}
sdivV :: Backend sym => sym -> Prim sym
sdivV sym =
  PFinPoly \w ->
  PWordFun \x ->
  PWordFun \y ->
  PPrim (VWord w . wordVal <$> wordSignedDiv sym x y)

{-# SPECIALIZE smodV :: Concrete -> Prim Concrete #-}
smodV :: Backend sym => sym -> Prim sym
smodV sym  =
  PFinPoly \w ->
  PWordFun \x ->
  PWordFun \y ->
  PPrim (VWord w . wordVal <$> wordSignedMod sym x y)

{-# SPECIALIZE toSignedIntegerV :: Concrete -> Prim Concrete #-}
toSignedIntegerV :: Backend sym => sym -> Prim sym
toSignedIntegerV sym =
  PFinPoly \_w ->
  PWordFun \x ->
  PPrim (VInteger <$> wordToSignedInt sym x)

-- Cmp -------------------------------------------------------------------------

{-# SPECIALIZE cmpValue ::
  Concrete ->
  (SBit Concrete -> SBit Concrete -> SEval Concrete a -> SEval Concrete a) ->
  (SWord Concrete -> SWord Concrete -> SEval Concrete a -> SEval Concrete a) ->
  (SInteger Concrete -> SInteger Concrete -> SEval Concrete a -> SEval Concrete a) ->
  (Integer -> SInteger Concrete -> SInteger Concrete -> SEval Concrete a -> SEval Concrete a) ->
  (SRational Concrete -> SRational Concrete -> SEval Concrete a -> SEval Concrete a) ->
  (SFloat Concrete -> SFloat Concrete -> SEval Concrete a -> SEval Concrete a) ->
  (TValue -> GenValue Concrete -> GenValue Concrete -> SEval Concrete a -> SEval Concrete a)
  #-}

cmpValue ::
  Backend sym =>
  sym ->
  (SBit sym -> SBit sym -> SEval sym a -> SEval sym a) ->
  (SWord sym -> SWord sym -> SEval sym a -> SEval sym a) ->
  (SInteger sym -> SInteger sym -> SEval sym a -> SEval sym a) ->
  (Integer -> SInteger sym -> SInteger sym -> SEval sym a -> SEval sym a) ->
  (SRational sym -> SRational sym -> SEval sym a -> SEval sym a) ->
  (SFloat sym -> SFloat sym -> SEval sym a -> SEval sym a) ->
  (TValue -> GenValue sym -> GenValue sym -> SEval sym a -> SEval sym a)
cmpValue sym fb fw fi fz fq ff = cmp
  where
    cmp ty v1 v2 k =
      case ty of
        TVBit         -> fb (fromVBit v1) (fromVBit v2) k
        TVInteger     -> fi (fromVInteger v1) (fromVInteger v2) k
        TVFloat _ _   -> ff (fromVFloat v1) (fromVFloat v2) k
        TVIntMod n    -> fz n (fromVInteger v1) (fromVInteger v2) k
        TVRational    -> fq (fromVRational v1) (fromVRational v2) k
        TVArray{}     -> panic "Cryptol.Prims.Value.cmpValue"
                               [ "Arrays are not comparable" ]
        TVSeq n t
          | isTBit t  -> do w1 <- fromVWord sym "cmpValue" v1
                            w2 <- fromVWord sym "cmpValue" v2
                            fw w1 w2 k
          | otherwise -> cmpValues (repeat t)
                           (enumerateSeqMap n (fromVSeq v1))
                           (enumerateSeqMap n (fromVSeq v2))
                           k
        TVStream _    -> panic "Cryptol.Prims.Value.cmpValue"
                                [ "Infinite streams are not comparable" ]
        TVFun _ _     -> panic "Cryptol.Prims.Value.cmpValue"
                               [ "Functions are not comparable" ]
        TVTuple tys   -> cmpValues tys (fromVTuple v1) (fromVTuple v2) k
        TVRec fields  -> cmpValues
                            (recordElements fields)
                            (recordElements (fromVRecord v1))
                            (recordElements (fromVRecord v2))
                            k

        TVNominal {} -> evalPanic "cmpValue"
                          [ "Nominal type not in `Cmp`" ]

    cmpValues (t : ts) (x1 : xs1) (x2 : xs2) k =
      do x1' <- x1
         x2' <- x2
         cmp t x1' x2' (cmpValues ts xs1 xs2 k)
    cmpValues _ _ _ k = k


{-# INLINE bitLessThan #-}
bitLessThan :: Backend sym => sym -> SBit sym -> SBit sym -> SEval sym (SBit sym)
bitLessThan sym x y =
  do xnot <- bitComplement sym x
     bitAnd sym xnot y

{-# INLINE bitGreaterThan #-}
bitGreaterThan :: Backend sym => sym -> SBit sym -> SBit sym -> SEval sym (SBit sym)
bitGreaterThan sym x y = bitLessThan sym y x

{-# INLINE valEq #-}
valEq :: Backend sym => sym -> TValue -> GenValue sym -> GenValue sym -> SEval sym (SBit sym)
valEq sym ty v1 v2 = cmpValue sym fb fw fi fz fq ff ty v1 v2 (pure $ bitLit sym True)
  where
  fb x y k   = eqCombine sym (bitEq  sym x y) k
  fw x y k   = eqCombine sym (wordEq sym x y) k
  fi x y k   = eqCombine sym (intEq  sym x y) k
  fz m x y k = eqCombine sym (znEq sym m x y) k
  fq x y k   = eqCombine sym (rationalEq sym x y) k
  ff x y k   = eqCombine sym (fpEq sym x y) k

{-# INLINE valLt #-}
valLt :: Backend sym =>
  sym -> TValue -> GenValue sym -> GenValue sym -> SBit sym -> SEval sym (SBit sym)
valLt sym ty v1 v2 final = cmpValue sym fb fw fi fz fq ff ty v1 v2 (pure final)
  where
  fb x y k   = lexCombine sym (bitLessThan  sym x y) (bitEq  sym x y) k
  fw x y k   = lexCombine sym (wordLessThan sym x y) (wordEq sym x y) k
  fi x y k   = lexCombine sym (intLessThan  sym x y) (intEq  sym x y) k
  fz _ _ _ _ = panic "valLt" ["Z_n is not in `Cmp`"]
  fq x y k   = lexCombine sym (rationalLessThan sym x y) (rationalEq sym x y) k
  ff x y k   = lexCombine sym (fpLessThan   sym x y) (fpEq   sym x y) k

{-# INLINE valGt #-}
valGt :: Backend sym =>
  sym -> TValue -> GenValue sym -> GenValue sym -> SBit sym -> SEval sym (SBit sym)
valGt sym ty v1 v2 final = cmpValue sym fb fw fi fz fq ff ty v1 v2 (pure final)
  where
  fb x y k   = lexCombine sym (bitGreaterThan  sym x y) (bitEq  sym x y) k
  fw x y k   = lexCombine sym (wordGreaterThan sym x y) (wordEq sym x y) k
  fi x y k   = lexCombine sym (intGreaterThan  sym x y) (intEq  sym x y) k
  fz _ _ _ _ = panic "valGt" ["Z_n is not in `Cmp`"]
  fq x y k   = lexCombine sym (rationalGreaterThan sym x y) (rationalEq sym x y) k
  ff x y k   = lexCombine sym (fpGreaterThan   sym x y) (fpEq   sym x y) k

{-# INLINE eqCombine #-}
eqCombine :: Backend sym =>
  sym ->
  SEval sym (SBit sym) ->
  SEval sym (SBit sym) ->
  SEval sym (SBit sym)
eqCombine sym eq k = join (bitAnd sym <$> eq <*> k)

{-# INLINE lexCombine #-}
lexCombine :: Backend sym =>
  sym ->
  SEval sym (SBit sym) ->
  SEval sym (SBit sym) ->
  SEval sym (SBit sym) ->
  SEval sym (SBit sym)
lexCombine sym cmp eq k =
  do c <- cmp
     e <- eq
     bitOr sym c =<< bitAnd sym e =<< k

{-# INLINE eqV #-}
eqV :: Backend sym => sym -> Binary sym
eqV sym ty v1 v2 = VBit <$> valEq sym ty v1 v2

{-# INLINE distinctV #-}
distinctV :: Backend sym => sym -> Binary sym
distinctV sym ty v1 v2 = VBit <$> (bitComplement sym =<< valEq sym ty v1 v2)

{-# INLINE lessThanV #-}
lessThanV :: Backend sym => sym -> Binary sym
lessThanV sym ty v1 v2 = VBit <$> valLt sym ty v1 v2 (bitLit sym False)

{-# INLINE lessThanEqV #-}
lessThanEqV :: Backend sym => sym -> Binary sym
lessThanEqV sym ty v1 v2 = VBit <$> valLt sym ty v1 v2 (bitLit sym True)

{-# INLINE greaterThanV #-}
greaterThanV :: Backend sym => sym -> Binary sym
greaterThanV sym ty v1 v2 = VBit <$> valGt sym ty v1 v2 (bitLit sym False)

{-# INLINE greaterThanEqV #-}
greaterThanEqV :: Backend sym => sym -> Binary sym
greaterThanEqV sym ty v1 v2 = VBit <$> valGt sym ty v1 v2 (bitLit sym True)

{-# INLINE signedLessThanV #-}
signedLessThanV :: Backend sym => sym -> Binary sym
signedLessThanV sym ty v1 v2 = VBit <$> cmpValue sym fb fw fi fz fq ff ty v1 v2 (pure $ bitLit sym False)
  where
  fb _ _ _   = panic "signedLessThan" ["Attempted to perform signed comparison on bit type"]
  fw x y k   = lexCombine sym (wordSignedLessThan sym x y) (wordEq sym x y) k
  fi _ _ _   = panic "signedLessThan" ["Attempted to perform signed comparison on Integer type"]
  fz m _ _ _ = panic "signedLessThan" ["Attempted to perform signed comparison on Z_" ++ show m ++ " type"]
  fq _ _ _   = panic "signedLessThan" ["Attempted to perform signed comparison on Rational type"]
  ff _ _ _   = panic "signedLessThan" ["Attempted to perform signed comparison on Float"]



{-# SPECIALIZE zeroV ::
  Concrete ->
  TValue ->
  SEval Concrete (GenValue Concrete)
  #-}
zeroV :: forall sym.
  Backend sym =>
  sym ->
  TValue ->
  SEval sym (GenValue sym)
zeroV sym ty = case ty of

  -- bits
  TVBit ->
    pure (VBit (bitLit sym False))

  -- integers
  TVInteger ->
    VInteger <$> integerLit sym 0

  -- integers mod n
  TVIntMod _ ->
    VInteger <$> integerLit sym 0

  TVRational ->
    VRational <$> (intToRational sym =<< integerLit sym 0)

  TVArray{} -> evalPanic "zeroV" ["Array not in class Zero"]

  -- floating point
  TVFloat e p ->
    VFloat <$> fpLit sym e p 0

  -- sequences
  TVSeq w ety
      | isTBit ety -> word sym w 0
      | otherwise  ->
           do z <- sDelay sym (zeroV sym ety)
              pure $ VSeq w (indexSeqMap \_i -> z)

  TVStream ety ->
     do z <- sDelay sym (zeroV sym ety)
        pure $ VStream (indexSeqMap \_i -> z)

  -- functions
  TVFun _ bty ->
     do z <- sDelay sym (zeroV sym bty)
        lam sym (const z)

  -- tuples
  TVTuple tys ->
      do xs <- mapM (sDelay sym . zeroV sym) tys
         pure $ VTuple xs

  -- records
  TVRec fields ->
      do xs <- traverse (sDelay sym . zeroV sym) fields
         pure $ VRecord xs

  TVNominal {} -> evalPanic "zeroV" [ "Nominal type not in `Zero`" ]


{-# SPECIALIZE joinSeq ::
  Concrete ->
  Nat' ->
  Integer ->
  TValue ->
  SEval Concrete (SeqMap Concrete (GenValue Concrete)) ->
  SEval Concrete (GenValue Concrete)
  #-}
joinSeq ::
  Backend sym =>
  sym ->
  Nat' ->
  Integer ->
  TValue ->
  SEval sym (SeqMap sym (GenValue sym)) ->
  SEval sym (GenValue sym)

-- Special case for 0 length inner sequences.
joinSeq sym _parts 0 a _val
  = zeroV sym (TVSeq 0 a)

-- finite sequence of words
joinSeq sym (Nat parts) each TVBit val
  = do w <- delayWordValue sym (parts*each)
              (joinWords sym parts each . fmap (fromWordVal "joinV") =<< val)
       pure (VWord (parts*each) w)

-- infinite sequence of words
joinSeq sym Inf each TVBit val
  = return $ VStream $ indexSeqMap $ \i ->
      do let (q,r) = divMod i each
         xs <- val
         ys <- fromWordVal "join seq" <$> lookupSeqMap xs q
         VBit <$> indexWordValue sym ys r

-- finite or infinite sequence of non-words
joinSeq _sym parts each _a val
  = return $ vSeq $ indexSeqMap $ \i -> do
      let (q,r) = divMod i each
      xs <- val
      ys <- fromSeq "join seq" =<< lookupSeqMap xs q
      lookupSeqMap ys r
  where
  len = parts `nMul` (Nat each)
  vSeq = case len of
           Inf    -> VStream
           Nat n  -> VSeq n


{-# INLINE joinV #-}

-- | Join a sequence of sequences into a single sequence.
joinV ::
  Backend sym =>
  sym ->
  Nat' ->
  Integer ->
  TValue ->
  SEval sym (GenValue sym) ->
  SEval sym (GenValue sym)
joinV sym parts each a val =
  do xs <- sDelay sym (fromSeq "joinV" =<< val)
     joinSeq sym parts each a xs

{-# INLINE takeV #-}
takeV ::
  Backend sym =>
  sym ->
  Nat' ->
  Nat' ->
  TValue ->
  SEval sym (GenValue sym) ->
  SEval sym (GenValue sym)
takeV sym front back a val =
  case front of
    Inf -> val
    Nat front' ->
      case back of
        Nat back' | isTBit a ->
          do w <- delayWordValue sym front' (takeWordVal sym front' back' =<< (fromWordVal "takeV" <$> val))
             pure (VWord front' w)

        Inf | isTBit a ->
          do w <- delayWordValue sym front' (bitmapWordVal sym front' . fmap fromVBit =<< (fromSeq "takeV" =<< val))
             pure (VWord front' w)

        _ ->
          do xs <- delaySeqMap sym (fromSeq "takeV" =<< val)
             pure (VSeq front' xs)

{-# INLINE dropV #-}
dropV ::
  Backend sym =>
  sym ->
  Integer ->
  Nat' ->
  TValue ->
  SEval sym (GenValue sym) ->
  SEval sym (GenValue sym)
dropV sym front back a val =
  case back of
    Nat back' | isTBit a ->
      do w <- delayWordValue sym back' (dropWordVal sym front back' =<< (fromWordVal "dropV" <$> val))
         pure (VWord back' w)

    _ ->
      do xs <- delaySeqMap sym (dropSeqMap front <$> (fromSeq "dropV" =<< val))
         mkSeq sym back a xs


{-# INLINE splitV #-}

-- | Split implementation.
splitV :: Backend sym =>
  sym ->
  Nat' ->
  Integer ->
  TValue ->
  SEval sym (GenValue sym) ->
  SEval sym (GenValue sym)
splitV sym parts each a val =
    case (parts, each) of
       (Nat p, e) | isTBit a -> do
          val' <- sDelay sym (fromWordVal "splitV" <$> val)
          return $ VSeq p $ indexSeqMap $ \i ->
            VWord e <$> (extractWordVal sym e ((p-i-1)*e) =<< val')
       (Inf, e) | isTBit a -> do
          val' <- sDelay sym (fromSeq "splitV" =<< val)
          return $ VStream $ indexSeqMap $ \i ->
            VWord e <$> bitmapWordVal sym e (indexSeqMap $ \j ->
              let idx = i*e + toInteger j
               in idx `seq` do
                      xs <- val'
                      fromVBit <$> lookupSeqMap xs idx)
       (Nat p, e) -> do
          val' <- sDelay sym (fromSeq "splitV" =<< val)
          return $ VSeq p $ indexSeqMap $ \i ->
            return $ VSeq e $ indexSeqMap $ \j -> do
              xs <- val'
              lookupSeqMap xs (e * i + j)
       (Inf  , e) -> do
          val' <- sDelay sym (fromSeq "splitV" =<< val)
          return $ VStream $ indexSeqMap $ \i ->
            return $ VSeq e $ indexSeqMap $ \j -> do
              xs <- val'
              lookupSeqMap xs (e * i + j)


{-# INLINE reverseV #-}

reverseV :: forall sym.
  Backend sym =>
  sym ->
  Integer ->
  TValue ->
  SEval sym (GenValue sym) ->
  SEval sym (GenValue sym)

reverseV sym n TVBit val =
  do w <- delayWordValue sym n (reverseWordVal sym . fromWordVal "reverseV" =<< val)
     pure (VWord n w)

reverseV sym n _a val =
  do xs <- delaySeqMap sym (reverseSeqMap n <$> (fromSeq "reverseV" =<< val))
     pure (VSeq n xs)


{-# INLINE transposeV #-}

transposeV ::
  Backend sym =>
  sym ->
  Nat' ->
  Nat' ->
  TValue ->
  GenValue sym ->
  SEval sym (GenValue sym)
transposeV sym a b c xs
  | isTBit c, Nat na <- a = -- Fin a => [a][b]Bit -> [b][a]Bit
      return $ bseq $ indexSeqMap $ \bi ->
        VWord na <$> bitmapWordVal sym na (indexSeqMap $ \ai ->
         do xs' <- fromSeq "transposeV" xs
            ys <- lookupSeqMap xs' ai
            case ys of
              VStream ys' -> fromVBit <$> lookupSeqMap ys' bi
              VWord _ wv  -> indexWordValue sym wv bi
              _ -> evalPanic "transpose" ["expected sequence of bits"])

  | isTBit c, Inf <- a = -- [inf][b]Bit -> [b][inf]Bit
      return $ bseq $ indexSeqMap $ \bi ->
        return $ VStream $ indexSeqMap $ \ai ->
         do xs' <- fromSeq "transposeV" xs
            ys  <- lookupSeqMap xs' ai
            case ys of
              VStream ys' -> lookupSeqMap ys' bi
              VWord _ wv  -> VBit <$> indexWordValue sym wv bi
              _ -> evalPanic "transpose" ["expected sequence of bits"]

  | otherwise = -- [a][b]c -> [b][a]c
      return $ bseq $ indexSeqMap $ \bi ->
        return $ aseq $ indexSeqMap $ \ai -> do
          xs' <- fromSeq "transposeV 1" xs
          ys  <- fromSeq "transposeV 2" =<< lookupSeqMap xs' ai
          z   <- lookupSeqMap ys bi
          return z

 where
  bseq =
        case b of
          Nat nb -> VSeq nb
          Inf    -> VStream
  aseq =
        case a of
          Nat na -> VSeq na
          Inf    -> VStream


{-# INLINE ccatV #-}

ccatV ::
  Backend sym =>
  sym ->
  Integer ->
  Nat' ->
  TValue ->
  SEval sym (GenValue sym) ->
  SEval sym (GenValue sym) ->
  SEval sym (GenValue sym)

-- Finite bitvectors
ccatV sym front (Nat back) TVBit l r =
  do ml <- isReady sym l
     mr <- isReady sym r
     case (ml, mr) of
       (Just l', Just r') ->
         VWord (front+back) <$>
           joinWordVal sym (fromWordVal "ccatV left" l') (fromWordVal "ccatV right" r')
       _ ->
         VWord (front+back) <$> delayWordValue sym (front+back)
                (do l' <- fromWordVal "ccatV left"  <$> l
                    r' <- fromWordVal "ccatV right" <$> r
                    joinWordVal sym l' r')

-- Infinite bitstream
ccatV sym front Inf TVBit l r =
  do l'' <- sDelay sym (asBitsMap sym  . fromWordVal "ccatV left" <$> l)
     r'' <- sDelay sym (fromSeq "ccatV right" =<< r)
     pure $ VStream $ indexSeqMap $ \i ->
      if i < front then do
        ls <- l''
        VBit <$> lookupSeqMap ls i
      else do
        rs <- r''
        lookupSeqMap rs (i-front)

-- streams/sequences of nonbits
ccatV sym front back elty l r =
  do l'' <- sDelay sym (fromSeq "ccatV left" =<< l)
     r'' <- sDelay sym (fromSeq "ccatV right" =<< r)
     mkSeq sym (evalTF TCAdd [Nat front,back]) elty $ indexSeqMap $ \i ->
      if i < front then do
        ls <- l''
        lookupSeqMap ls i
      else do
        rs <- r''
        lookupSeqMap rs (i-front)


{-# SPECIALIZE logicBinary ::
  Concrete ->
  (SBit Concrete -> SBit Concrete -> SEval Concrete (SBit Concrete)) ->
  (SWord Concrete -> SWord Concrete -> SEval Concrete (SWord Concrete)) ->
  Binary Concrete
  #-}

-- | Merge two values given a binop.  This is used for and, or and xor.
logicBinary :: forall sym.
  Backend sym =>
  sym ->
  (SBit sym -> SBit sym -> SEval sym (SBit sym)) ->
  (SWord sym -> SWord sym -> SEval sym (SWord sym)) ->
  Binary sym
logicBinary sym opb opw = loop
  where
  loop' :: TValue
        -> SEval sym (GenValue sym)
        -> SEval sym (GenValue sym)
        -> SEval sym (GenValue sym)
  loop' ty l r = join (loop ty <$> l <*> r)

  loop :: TValue
        -> GenValue sym
        -> GenValue sym
        -> SEval sym (GenValue sym)

  loop ty l r = case ty of
    TVBit -> VBit <$> (opb (fromVBit l) (fromVBit r))
    TVInteger -> evalPanic "logicBinary" ["Integer not in class Logic"]
    TVIntMod _ -> evalPanic "logicBinary" ["Z not in class Logic"]
    TVRational -> evalPanic "logicBinary" ["Rational not in class Logic"]
    TVArray{} -> evalPanic "logicBinary" ["Array not in class Logic"]

    TVFloat {}  -> evalPanic "logicBinary" ["Float not in class Logic"]
    TVSeq w aty
         -- words
         | isTBit aty
              -> VWord w <$> delayWordValue sym w
                               (wordValLogicOp sym opb opw
                                    (fromWordVal "logicBinary l" l)
                                    (fromWordVal "logicBinary r" r))

         -- finite sequences
         | otherwise -> VSeq w <$>
                           (join (zipSeqMap sym (loop aty) (Nat w) <$>
                                    (fromSeq "logicBinary left" l)
                                    <*> (fromSeq "logicBinary right" r)))

    TVStream aty ->
        VStream <$> (join (zipSeqMap sym (loop aty) Inf <$>
                          (fromSeq "logicBinary left" l) <*>
                          (fromSeq "logicBinary right" r)))

    TVTuple etys -> do
        ls <- mapM (sDelay sym) (fromVTuple l)
        rs <- mapM (sDelay sym) (fromVTuple r)
        return $ VTuple $ zipWith3 loop' etys ls rs

    TVFun _ bty ->
        lam sym $ \ a -> loop' bty (fromVFun sym l a) (fromVFun sym r a)

    TVRec fields ->
      VRecord <$>
        traverseRecordMap
          (\f fty -> sDelay sym (loop' fty (lookupRecord f l) (lookupRecord f r)))
          fields

    TVNominal {} -> evalPanic "logicBinary"
                        [ "Nominal type not in `Logic`" ]

{-# SPECIALIZE logicUnary ::
  Concrete ->
  (SBit Concrete -> SEval Concrete (SBit Concrete)) ->
  (SWord Concrete -> SEval Concrete (SWord Concrete)) ->
  Unary Concrete
  #-}

logicUnary :: forall sym.
  Backend sym =>
  sym ->
  (SBit sym -> SEval sym (SBit sym)) ->
  (SWord sym -> SEval sym (SWord sym)) ->
  Unary sym
logicUnary sym opb opw = loop
  where
  loop' :: TValue -> SEval sym (GenValue sym) -> SEval sym (GenValue sym)
  loop' ty val = loop ty =<< val

  loop :: TValue -> GenValue sym -> SEval sym (GenValue sym)
  loop ty val = case ty of
    TVBit -> VBit <$> (opb (fromVBit val))

    TVInteger -> evalPanic "logicUnary" ["Integer not in class Logic"]
    TVIntMod _ -> evalPanic "logicUnary" ["Z not in class Logic"]
    TVFloat {} -> evalPanic "logicUnary" ["Float not in class Logic"]
    TVRational -> evalPanic "logicBinary" ["Rational not in class Logic"]
    TVArray{} -> evalPanic "logicUnary" ["Array not in class Logic"]

    TVSeq w ety
         -- words
         | isTBit ety
              -> VWord w <$> delayWordValue sym w (wordValUnaryOp sym opb opw (fromWordVal "logicUnary" val))

         -- finite sequences
         | otherwise
              -> VSeq w <$> (mapSeqMap sym (loop ety) (Nat w) =<< fromSeq "logicUnary" val)

         -- streams
    TVStream ety ->
         VStream <$> (mapSeqMap sym (loop ety) Inf =<< fromSeq "logicUnary" val)

    TVTuple etys ->
      do as <- mapM (sDelay sym) (fromVTuple val)
         return $ VTuple (zipWith loop' etys as)

    TVFun _ bty ->
      lam sym $ \ a -> loop' bty (fromVFun sym val a)

    TVRec fields ->
      VRecord <$>
        traverseRecordMap
          (\f fty -> sDelay sym (loop' fty (lookupRecord f val)))
          fields

    TVNominal {} -> evalPanic "logicUnary" [ "Nominal type not in `Logic`" ]


{-# INLINE assertIndexInBounds #-}
assertIndexInBounds ::
  Backend sym =>
  sym ->
  Nat' {- ^ Sequence size bounds -} ->
  Either (SInteger sym) (WordValue sym) {- ^ Index value -} ->
  SEval sym ()

-- All nonnegative integers are in bounds for an infinite sequence
assertIndexInBounds sym Inf (Left idx) =
  do ppos <- bitComplement sym =<< intLessThan sym idx =<< integerLit sym 0
     assertSideCondition sym ppos (InvalidIndex (integerAsLit sym idx))

-- If the index is an integer, test that it
-- is nonnegative and less than the concrete value of n.
assertIndexInBounds sym (Nat n) (Left idx) =
  do n' <- integerLit sym n
     ppos <- bitComplement sym =<< intLessThan sym idx =<< integerLit sym 0
     pn <- intLessThan sym idx n'
     p <- bitAnd sym ppos pn
     assertSideCondition sym p (InvalidIndex (integerAsLit sym idx))

-- Bitvectors can't index out of bounds for an infinite sequence
assertIndexInBounds _sym Inf (Right _) = return ()

-- Can't index out of bounds for a sequence that is
-- longer than the expressible index values
assertIndexInBounds sym (Nat n) (Right idx) =
  assertWordValueInBounds sym n idx

-- | Indexing operations.

{-# INLINE indexPrim #-}
indexPrim ::
  Backend sym =>
  sym ->
  IndexDirection ->
  (Nat' -> TValue -> SeqMap sym (GenValue sym) -> TValue -> SInteger sym -> SEval sym (GenValue sym)) ->
  (Nat' -> TValue -> SeqMap sym (GenValue sym) -> TValue -> Integer -> [IndexSegment sym] -> SEval sym (GenValue sym)) ->
  Prim sym
indexPrim sym dir int_op word_op =
  PNumPoly \len ->
  PTyPoly  \eltTy ->
  PTyPoly  \ix ->
  PFun     \xs ->
  PFun     \idx ->
  PPrim
   do vs <- xs >>= \case
               VWord _ w  -> return $ indexSeqMap (\i -> VBit <$> indexWordValue sym w i)
               VSeq _ vs  -> return vs
               VStream vs -> return vs
               _ -> evalPanic "Expected sequence value" ["indexPrim"]
      let vs' = case (len, dir) of
                  (_    , IndexForward)  -> vs
                  (Nat n, IndexBackward) -> reverseSeqMap n vs
                  (Inf  , IndexBackward) -> evalPanic "Expected finite sequence" ["!"]
      idx' <- asIndex sym "index" ix <$> idx
      assertIndexInBounds sym len idx'
      case idx' of
        Left i  -> int_op  len eltTy vs' ix i
        Right w -> word_op len eltTy vs' ix (wordValueSize sym w) =<< enumerateIndexSegments sym w

{-# INLINE updatePrim #-}

updatePrim ::
  Backend sym =>
  sym ->
  (Nat' -> TValue -> WordValue sym -> Either (SInteger sym) (WordValue sym) -> SEval sym (GenValue sym) -> SEval sym (WordValue sym)) ->
  (Nat' -> TValue -> SeqMap sym (GenValue sym) -> Either (SInteger sym) (WordValue sym) -> SEval sym (GenValue sym) -> SEval sym (SeqMap sym (GenValue sym))) ->
  Prim sym
updatePrim sym updateWord updateSeq =
  PNumPoly \len ->
  PTyPoly  \eltTy ->
  PTyPoly  \ix ->
  PFun     \xs ->
  PFun     \idx ->
  PFun     \val ->
  PPrim
   do idx' <- asIndex sym "update" ix <$> idx
      assertIndexInBounds sym len idx'
      case (len, eltTy) of
        (Nat n, TVBit) -> VWord n <$> delayWordValue sym n
                             (do w <- fromWordVal "updatePrim" <$> xs; updateWord len eltTy w idx' val)
        (Nat n, _    ) -> VSeq n <$> delaySeqMap sym
                             (do vs <- fromSeq "updatePrim" =<< xs; updateSeq len eltTy vs idx' val)
        (Inf  , _    ) -> VStream <$> delaySeqMap sym
                             (do vs <- fromSeq "updatePrim" =<< xs; updateSeq len eltTy vs idx' val)

{-# INLINE fromToV #-}
-- @[ 0 .. 10 ]@
fromToV :: Backend sym => sym -> Prim sym
fromToV sym =
  PNumPoly \first ->
  PNumPoly \lst ->
  PTyPoly  \ty ->
  PPrim
    let !f = mkLit sym ty in
    case (first, lst) of
      (Nat first', Nat lst') ->
        let len = 1 + (lst' - first')
        in mkSeq sym (Nat len) ty $ indexSeqMap $ \i -> f (first' + i)
      _ -> evalPanic "fromToV" ["invalid arguments"]

{-# INLINE fromThenToV #-}
-- @[ 0, 1 .. 10 ]@
fromThenToV :: Backend sym => sym -> Prim sym
fromThenToV sym =
  PNumPoly \first ->
  PNumPoly \next  ->
  PNumPoly \lst   ->
  PTyPoly  \ty    ->
  PNumPoly \len   ->
  PPrim
    let !f = mkLit sym ty in
    case (first, next, lst, len) of
      (Nat first', Nat next', Nat _lst', Nat len') ->
        let diff = next' - first'
        in mkSeq sym (Nat len') ty $ indexSeqMap $ \i -> f (first' + i*diff)
      _ -> evalPanic "fromThenToV" ["invalid arguments"]

{-# INLINE fromToLessThanV #-}
-- @[ 0 .. <10 ]@
fromToLessThanV :: Backend sym => sym -> Prim sym
fromToLessThanV sym =
  PFinPoly \first ->
  PNumPoly \bound ->
  PTyPoly  \ty ->
  PPrim
    let !f = mkLit sym ty
        ss = indexSeqMap $ \i -> f (first + i)
    in case bound of
         Inf        -> return $ VStream ss
         Nat bound' -> mkSeq sym (Nat (bound' - first)) ty ss

{-# INLINE fromToByV #-}
-- @[ 0 .. 10 by 2 ]@
fromToByV :: Backend sym => sym -> Prim sym
fromToByV sym =
  PFinPoly \first ->
  PFinPoly \lst ->
  PFinPoly \stride ->
  PTyPoly  \ty ->
  PPrim
    let !f = mkLit sym ty
        ss = indexSeqMap $ \i -> f (first + i*stride)
     in mkSeq sym (Nat (1 + ((lst - first) `div` stride))) ty ss

{-# INLINE fromToByLessThanV #-}
-- @[ 0 .. <10 by 2 ]@
fromToByLessThanV :: Backend sym => sym -> Prim sym
fromToByLessThanV sym =
  PFinPoly \first ->
  PNumPoly \bound ->
  PFinPoly \stride ->
  PTyPoly  \ty ->
  PPrim
    let !f = mkLit sym ty
        ss = indexSeqMap $ \i -> f (first + i*stride)
     in case bound of
          Inf -> return $ VStream ss
          Nat bound' -> mkSeq sym (Nat ((bound' - first + stride - 1) `div` stride)) ty ss


{-# INLINE fromToDownByV #-}
-- @[ 10 .. 0 down by 2 ]@
fromToDownByV :: Backend sym => sym -> Prim sym
fromToDownByV sym =
  PFinPoly \first ->
  PFinPoly \lst ->
  PFinPoly \stride ->
  PTyPoly  \ty ->
  PPrim
    let !f = mkLit sym ty
        ss = indexSeqMap $ \i -> f (first - i*stride)
     in mkSeq sym (Nat (1 + ((first - lst) `div` stride))) ty ss

{-# INLINE fromToDownByGreaterThanV #-}
-- @[ 10 .. >0 down by 2 ]@
fromToDownByGreaterThanV :: Backend sym => sym -> Prim sym
fromToDownByGreaterThanV sym =
  PFinPoly \first ->
  PFinPoly \bound ->
  PFinPoly \stride ->
  PTyPoly  \ty ->
  PPrim
    let !f = mkLit sym ty
        ss = indexSeqMap $ \i -> f (first - i*stride)
     in mkSeq sym (Nat ((first - bound + stride - 1) `div` stride)) ty ss

{-# INLINE infFromV #-}
infFromV :: Backend sym => sym -> Prim sym
infFromV sym =
  PTyPoly \ty ->
  PFun    \x ->
  PPrim
    do mx <- sDelay sym x
       return $ VStream $ indexSeqMap $ \i ->
         do x' <- mx
            i' <- integerLit sym i
            addV sym ty x' =<< intV sym i' ty

{-# INLINE infFromThenV #-}
infFromThenV :: Backend sym => sym -> Prim sym
infFromThenV sym =
  PTyPoly \ty ->
  PFun    \first ->
  PFun    \next ->
  PPrim
    do mxd <- sDelay sym
               (do x <- first
                   y <- next
                   d <- subV sym ty y x
                   pure (x,d))
       return $ VStream $ indexSeqMap $ \i -> do
         (x,d) <- mxd
         i' <- integerLit sym i
         addV sym ty x =<< mulV sym ty d =<< intV sym i' ty

-- Shifting ---------------------------------------------------


{-# INLINE shiftLeftReindex #-}
shiftLeftReindex :: Nat' -> Integer -> Integer -> Maybe Integer
shiftLeftReindex sz i shft =
   case sz of
     Nat n | i+shft >= n -> Nothing
     _                   -> Just (i+shft)

{-# INLINE shiftRightReindex #-}
shiftRightReindex :: Nat' -> Integer -> Integer -> Maybe Integer
shiftRightReindex _sz i shft =
   if i-shft < 0 then Nothing else Just (i-shft)

{-# INLINE rotateLeftReindex #-}
rotateLeftReindex :: Nat' -> Integer -> Integer -> Maybe Integer
rotateLeftReindex sz i shft =
   case sz of
     Inf -> evalPanic "cannot rotate infinite sequence" []
     Nat n -> Just ((i+shft) `mod` n)

{-# INLINE rotateRightReindex #-}
rotateRightReindex :: Nat' -> Integer -> Integer -> Maybe Integer
rotateRightReindex sz i shft =
   case sz of
     Inf -> evalPanic "cannot rotate infinite sequence" []
     Nat n -> Just ((i+n-shft) `mod` n)


{-# INLINE logicShift #-}
-- | Generic implementation of shifting.
--   Uses the provided word-level operation to perform the shift, when
--   possible.  Otherwise falls back on a barrel shifter that uses
--   the provided reindexing operation to implement the concrete
--   shifting operations.  The reindex operation is given the size
--   of the sequence, the requested index value for the new output sequence,
--   and the amount to shift.  The return value is an index into the original
--   sequence if in bounds, and Nothing otherwise.
logicShift :: Backend sym =>
  sym ->
  String ->
  (sym -> Nat' -> TValue -> SInteger sym -> SEval sym (SInteger sym))
     {- ^ operation for range reduction on integers -} ->
  (SWord sym -> SWord sym -> SEval sym (SWord sym))
     {- ^ word shift operation for positive indices -} ->
  (SWord sym -> SWord sym -> SEval sym (SWord sym))
     {- ^ word shift operation for negative indices -} ->
  (Nat' -> Integer -> Integer -> Maybe Integer)
     {- ^ reindexing operation for positive indices (sequence size, starting index, shift amount -} ->
  (Nat' -> Integer -> Integer -> Maybe Integer)
     {- ^ reindexing operation for negative indices (sequence size, starting index, shift amount -} ->
  Prim sym
logicShift sym nm shrinkRange wopPos wopNeg reindexPos reindexNeg =
  PNumPoly \m ->
  PTyPoly  \ix ->
  PTyPoly  \a ->
  PFun     \xs ->
  PFun     \y ->
  PPrim
    do xs' <- xs
       y' <- asIndex sym "shift" ix <$> y
       case y' of
         Left int_idx ->
           do pneg <- intLessThan sym int_idx =<< integerLit sym 0
              iteValue sym pneg
                (intShifter sym nm wopNeg reindexNeg m a xs' =<< shrinkRange sym m ix =<< intNegate sym int_idx)
                (intShifter sym nm wopPos reindexPos m a xs' =<< shrinkRange sym m ix int_idx)
         Right idx ->
           wordShifter sym nm wopPos reindexPos m a xs' idx



{-# INLINE intShifter #-}
intShifter :: Backend sym =>
   sym ->
   String ->
   (SWord sym -> SWord sym -> SEval sym (SWord sym)) ->
   (Nat' -> Integer -> Integer -> Maybe Integer) ->
   Nat' ->
   TValue ->
   GenValue sym ->
   SInteger sym ->
   SEval sym (GenValue sym)
intShifter sym nm wop reindex m a xs idx =
  case xs of
    VWord w x  -> VWord w <$> shiftWordByInteger sym wop (reindex m) x idx
    VSeq w vs  -> VSeq w  <$> shiftSeqByInteger sym (mergeValue sym) (reindex m) (zeroV sym a) m vs idx
    VStream vs -> VStream <$> shiftSeqByInteger sym (mergeValue sym) (reindex m) (zeroV sym a) m vs idx
    _ -> evalPanic "expected sequence value in shift operation" [nm]


{-# INLINE wordShifter #-}
wordShifter :: Backend sym =>
   sym ->
   String ->
   (SWord sym -> SWord sym -> SEval sym (SWord sym)) ->
   (Nat' -> Integer -> Integer -> Maybe Integer) ->
   Nat' ->
   TValue ->
   GenValue sym ->
   WordValue sym ->
   SEval sym (GenValue sym)
wordShifter sym nm wop reindex m a xs idx =
  case xs of
    VWord w x  -> VWord w <$> shiftWordByWord sym wop (reindex m) x idx
    VSeq w vs  -> VSeq w  <$> shiftSeqByWord sym (mergeValue sym) (reindex m) (zeroV sym a) (Nat w) vs idx
    VStream vs -> VStream <$> shiftSeqByWord sym (mergeValue sym) (reindex m) (zeroV sym a) Inf     vs idx
    _ -> evalPanic "expected sequence value in shift operation" [nm]



{-# INLINE shiftShrink #-}
shiftShrink :: Backend sym => sym -> Nat' -> TValue -> SInteger sym -> SEval sym (SInteger sym)
shiftShrink _sym Inf _ x = return x
shiftShrink sym (Nat w) _ x =
  do w' <- integerLit sym w
     p  <- intLessThan sym w' x
     iteInteger sym p w' x

{-# INLINE rotateShrink #-}
rotateShrink :: Backend sym => sym -> Nat' -> TValue -> SInteger sym -> SEval sym (SInteger sym)
rotateShrink _sym Inf _ _ = panic "rotateShrink" ["expected finite sequence in rotate"]
rotateShrink sym (Nat 0) _ _ = integerLit sym 0
rotateShrink sym (Nat w) _ x =
  do w' <- integerLit sym w
     intMod sym x w'

{-# INLINE sshrV #-}
sshrV :: Backend sym => sym -> Prim sym
sshrV sym =
  PFinPoly \n ->
  PTyPoly  \ix ->
  PWordFun \x ->
  PStrict  \y ->
  PPrim $
    case asIndex sym ">>$" ix y of
       Left i ->
         do pneg <- intLessThan sym i =<< integerLit sym 0
            VWord n <$> mergeWord' sym
              pneg
              (do i' <- shiftShrink sym (Nat n) ix =<< intNegate sym i
                  amt <- wordFromInt sym n i'
                  wordVal <$> wordShiftLeft sym x amt)
              (do i' <- shiftShrink sym (Nat n) ix i
                  amt <- wordFromInt sym n i'
                  wordVal <$> wordSignedShiftRight sym x amt)

       Right wv ->
         do amt <- asWordVal sym wv
            VWord n . wordVal <$> wordSignedShiftRight sym x amt

-- Miscellaneous ---------------------------------------------------------------

{-# SPECIALIZE errorV ::
  Concrete ->
  TValue ->
  String ->
  SEval Concrete (GenValue Concrete)
  #-}
errorV :: forall sym.
  Backend sym =>
  sym ->
  TValue ->
  String ->
  SEval sym (GenValue sym)
errorV sym _ty msg =
  do stk <- sGetCallStack sym
     sWithCallStack sym stk (cryUserError sym msg)

{-# INLINE valueToChar #-}

-- | Expect a word value.  Mask it to an 8-bits ASCII value
--   and return the associated character, if it is concrete.
--   Otherwise, return a '?' character
valueToChar :: Backend sym => sym -> GenValue sym -> SEval sym Char
valueToChar sym (VWord 8 wval) =
  do w <- asWordVal sym wval
     pure $! fromMaybe '?' (wordAsChar sym w)
valueToChar _ _ = evalPanic "valueToChar" ["Not an 8-bit bitvector"]

{-# INLINE valueToString #-}

valueToString :: Backend sym => sym -> GenValue sym -> SEval sym String
valueToString sym (VSeq n vals) = traverse (valueToChar sym =<<) (enumerateSeqMap n vals)
valueToString _ _ = evalPanic "valueToString" ["Not a finite sequence"]


foldlV :: Backend sym => sym -> Prim sym
foldlV sym =
  PNumPoly \_n ->
  PTyPoly  \_a ->
  PTyPoly  \_b ->
  PFun     \f ->
  PFun     \z ->
  PStrict  \v ->
  PPrim
    case v of
      VSeq n m    -> go0 f z (enumerateSeqMap n m)
      VWord _n wv -> go0 f z . map (pure . VBit) =<< (enumerateWordValue sym wv)
      _ -> panic "Cryptol.Eval.Generic.foldlV" ["Expected finite sequence"]
  where
  go0 _f a [] = a
  go0 f a bs =
    do f' <- fromVFun sym <$> f
       go1 f' a bs

  go1 _f a [] = a
  go1 f a (b:bs) =
    do f' <- fromVFun sym <$> (f a)
       go1 f (f' b) bs

foldl'V :: Backend sym => sym -> Prim sym
foldl'V sym =
  PNumPoly \_n ->
  PTyPoly  \_a ->
  PTyPoly  \_b ->
  PFun     \f ->
  PFun     \z ->
  PStrict  \v ->
  PPrim
    case v of
      VSeq n m    -> go0 f z (enumerateSeqMap n m)
      VWord _n wv -> go0 f z . map (pure . VBit) =<< (enumerateWordValue sym wv)
      _ -> panic "Cryptol.Eval.Generic.foldlV" ["Expected finite sequence"]
  where
  go0 _f a [] = a
  go0 f a bs =
    do f' <- fromVFun sym <$> f
       a' <- sDelay sym a
       forceValue =<< a'
       go1 f' a' bs

  go1 _f a [] = a
  go1 f a (b:bs) =
    do f' <- fromVFun sym <$> (f a)
       a' <- sDelay sym (f' b)
       forceValue =<< a'
       go1 f a' bs


-- scanl : {n, a, b}  (a -> b -> a) -> a -> [n]b -> [1+n]a
scanlV :: forall sym. Backend sym => sym -> Prim sym
scanlV sym =
  PNumPoly \n ->
  PTyPoly  \a ->
  PTyPoly  \_b ->
  PFun     \f ->
  PFun     \z ->
  PStrict  \v ->
  PPrim
    do sm <- case v of
            VSeq _ m   -> scan n f z m
            VWord _ wv -> scan n f z (VBit <$> asBitsMap sym wv)
            VStream m  -> scan n f z m
            _ -> panic "Cryptol.Eval.Generic.scanlV" ["Expected sequence"]
       mkSeq sym (nAdd (Nat 1) n) a sm

 where
  scan :: Nat' ->
          SEval sym (GenValue sym) ->
          SEval sym (GenValue sym) ->
          (SeqMap sym (GenValue sym)) ->
          SEval sym (SeqMap sym (GenValue sym))
  scan n f z m =
    do (result, fill) <- sDeclareHole sym "scanl"
       fill $ memoMap sym (nAdd (Nat 1) n) $ indexSeqMap $ \i ->
         if i == 0 then z
         else
           do r <- result
              f'  <- fromVFun sym <$> f
              f'' <- fromVFun sym <$> f' (lookupSeqMap r (i-1))
              f'' (lookupSeqMap m (i-1))
       result

-- Random Values ---------------------------------------------------------------

{-# SPECIALIZE randomV ::
  Concrete -> TValue -> Integer -> SEval Concrete (GenValue Concrete)
  #-}
-- | Produce a random value with the given seed. If we do not support
-- making values of the given type, return zero of that type.
-- TODO: do better than returning zero
randomV :: Backend sym => sym -> TValue -> Integer -> SEval sym (GenValue sym)
randomV sym ty seed =
  case randomValue sym ty of
    Nothing -> zeroV sym ty
    Just gen ->
      -- unpack the seed into four Word64s
      let mask64 = 0xFFFFFFFFFFFFFFFF
          unpack s = fromInteger (s .&. mask64) : unpack (s `shiftR` 64)
          (a, b, c, d) = case take 4 (unpack seed) of
                           [a', b', c', d'] -> (a', b', c', d')
                           _ -> error "randomV: impossible (infinite seed is finite)"
      in fst $ gen 100 $ seedTFGen (a, b, c, d)

--------------------------------------------------------------------------------
-- Experimental parallel primitives

parmapV :: Backend sym => sym -> Prim sym
parmapV sym =
  PTyPoly \_a ->
  PTyPoly \b ->
  PFinPoly \n ->
  PFun \f ->
  PFun \xs ->
  PPrim
    do f' <- fromVFun sym <$> f
       xs' <- xs
       m <-
         case xs' of
           VWord _n w ->
             let m = asBitsMap sym w in
             sparkParMap sym (\x -> f' (VBit <$> x)) n m
           VSeq _n m ->
             sparkParMap sym f' n m

           _ -> panic "parmapV" ["expected finite sequence!"]
       mkSeq sym (Nat n) b m


sparkParMap ::
  Backend sym =>
  sym ->
  (SEval sym a -> SEval sym (GenValue sym)) ->
  Integer ->
  SeqMap sym a ->
  SEval sym (SeqMap sym (GenValue sym))
sparkParMap sym f n m =
  finiteSeqMap sym <$> mapM (sSpark sym . g) (enumerateSeqMap n m)
 where
 g x =
   do z <- sDelay sym (f x)
      forceValue =<< z
      z

--------------------------------------------------------------------------------
-- Floating Point Operations

-- | A helper for definitng floating point constants.
fpConst ::
  Backend sym =>
  (Integer -> Integer -> SEval sym (SFloat sym)) ->
  Prim sym
fpConst mk =
  PFinPoly \e ->
  PNumPoly \ ~(Nat p) ->
  PPrim (VFloat <$> mk e p)

-- | Make a Cryptol value for a binary arithmetic function.
fpBinArithV :: Backend sym => sym -> FPArith2 sym -> Prim sym
fpBinArithV sym fun =
  PFinPoly  \_e ->
  PFinPoly  \_p ->
  PWordFun  \r ->
  PFloatFun \x ->
  PFloatFun \y ->
  PPrim (VFloat <$> fun sym r x y)

-- | Rounding mode used in FP operations that do not specify it explicitly.
fpRndMode, fpRndRNE, fpRndRNA, fpRndRTP, fpRndRTN, fpRndRTZ ::
   Backend sym => sym -> SEval sym (SWord sym)
fpRndMode    = fpRndRNE
fpRndRNE sym = wordLit sym 3 0 {- to nearest, ties to even -}
fpRndRNA sym = wordLit sym 3 1 {- to nearest, ties to away from 0 -}
fpRndRTP sym = wordLit sym 3 2 {- to +inf -}
fpRndRTN sym = wordLit sym 3 3 {- to -inf -}
fpRndRTZ sym = wordLit sym 3 4 {- to 0    -}


{-# SPECIALIZE genericFloatTable :: Concrete -> Map PrimIdent (Prim Concrete) #-}

genericFloatTable :: Backend sym => sym -> Map PrimIdent (Prim sym)
genericFloatTable sym =
  let (~>) = (,) in
  Map.fromList $ map (\(n, v) -> (floatPrim n, v))
    [ "fpNaN"       ~> fpConst (fpNaN sym)
    , "fpPosInf"    ~> fpConst (fpPosInf sym)
    , "fpFromBits"  ~> PFinPoly \e -> PFinPoly \p -> PWordFun \w ->
                       PPrim (VFloat <$> fpFromBits sym e p w)
    , "fpToBits"    ~> PFinPoly \e -> PFinPoly \p -> PFloatFun \x -> PPrim
                            (VWord (e+p) . wordVal <$> fpToBits sym x)
    , "=.="         ~> PFinPoly \_ -> PFinPoly \_ -> PFloatFun \x -> PFloatFun \y ->
                       PPrim (VBit <$> fpLogicalEq sym x y)

    , "fpIsNaN"     ~> PFinPoly \_ -> PFinPoly \_ -> PFloatFun \x ->
                       PPrim (VBit <$> fpIsNaN sym x)
    , "fpIsInf"     ~> PFinPoly \_ -> PFinPoly \_ -> PFloatFun \x ->
                       PPrim (VBit <$> fpIsInf sym x)
    , "fpIsZero"    ~> PFinPoly \_ -> PFinPoly \_ -> PFloatFun \x ->
                       PPrim (VBit <$> fpIsZero sym x)
    , "fpIsNeg"     ~> PFinPoly \_ -> PFinPoly \_ -> PFloatFun \x ->
                       PPrim (VBit <$> fpIsNeg sym x)
    , "fpIsNormal"  ~> PFinPoly \_ -> PFinPoly \_ -> PFloatFun \x ->
                       PPrim (VBit <$> fpIsNorm sym x)
    , "fpIsSubnormal" ~> PFinPoly \_ -> PFinPoly \_ -> PFloatFun \x ->
                         PPrim (VBit <$> fpIsSubnorm sym x)

    , "fpAdd"       ~> fpBinArithV sym fpPlus
    , "fpSub"       ~> fpBinArithV sym fpMinus
    , "fpMul"       ~> fpBinArithV sym fpMult
    , "fpDiv"       ~> fpBinArithV sym fpDiv
    , "fpFMA"       ~> PFinPoly \_ -> PFinPoly \_ -> PWordFun \r ->
                       PFloatFun \x -> PFloatFun \y -> PFloatFun \z ->
                       PPrim (VFloat <$> fpFMA sym r x y z)

    , "fpAbs"       ~> PFinPoly \_ -> PFinPoly \_ ->
                       PFloatFun \x ->
                       PPrim (VFloat <$> fpAbs sym x)

    , "fpSqrt"      ~> PFinPoly \_ -> PFinPoly \_ ->
                       PWordFun \r -> PFloatFun \x ->
                       PPrim (VFloat <$> fpSqrt sym r x)

    , "fpToRational" ~>
       PFinPoly \_e -> PFinPoly \_p -> PFloatFun \x ->
       PPrim (VRational <$> fpToRational sym x)

    , "fpFromRational" ~>
       PFinPoly \e -> PFinPoly \p -> PWordFun \r -> PFun \x ->
       PPrim
         do rat <- fromVRational <$> x
            VFloat <$> fpFromRational sym e p r rat

    ]


{-# SPECIALIZE genericPrimTable :: Concrete -> IO EvalOpts -> Map PrimIdent (Prim Concrete) #-}

genericPrimTable :: Backend sym => sym -> IO EvalOpts -> Map PrimIdent (Prim sym)
genericPrimTable sym getEOpts =
  Map.fromList $ map (\(n, v) -> (prelPrim n, v))

  [ -- Literals
    ("True"       , PVal $ VBit (bitLit sym True))
  , ("False"      , PVal $ VBit (bitLit sym False))
  , ("number"     , {-# SCC "Prelude::number" #-}
                    ecNumberV sym)
  , ("ratio"      , {-# SCC "Prelude::ratio" #-}
                    ratioV sym)
  , ("fraction"   , ecFractionV sym)

    -- Zero
  , ("zero"       , {-# SCC "Prelude::zero" #-}
                    PTyPoly \ty ->
                    PPrim (zeroV sym ty))

    -- Logic
  , ("&&"         , {-# SCC "Prelude::(&&)" #-}
                    binary (andV sym))
  , ("||"         , {-# SCC "Prelude::(||)" #-}
                    binary (orV sym))
  , ("^"          , {-# SCC "Prelude::(^)" #-}
                    binary (xorV sym))
  , ("complement" , {-# SCC "Prelude::complement" #-}
                    unary  (complementV sym))

    -- Ring
  , ("fromInteger", {-# SCC "Prelude::fromInteger" #-}
                    fromIntegerV sym)
  , ("+"          , {-# SCC "Prelude::(+)" #-}
                    binary (addV sym))
  , ("-"          , {-# SCC "Prelude::(-)" #-}
                    binary (subV sym))
  , ("*"          , {-# SCC "Prelude::(*)" #-}
                    binary (mulV sym))
  , ("negate"     , {-# SCC "Prelude::negate" #-}
                    unary (negateV sym))

    -- Integral
  , ("toInteger"  , {-# SCC "Prelude::toInteger" #-}
                    toIntegerV sym)
  , ("/"          , {-# SCC "Prelude::(/)" #-}
                    binary (divV sym))
  , ("%"          , {-# SCC "Prelude::(%)" #-}
                    binary (modV sym))
  , ("^^"         , {-# SCC "Prelude::(^^)" #-}
                    expV sym)
  , ("infFrom"    , {-# SCC "Prelude::infFrom" #-}
                    infFromV sym)
  , ("infFromThen", {-# SCC "Prelude::infFromThen" #-}
                    infFromThenV sym)

    -- Field
  , ("recip"      , {-# SCC "Prelude::recip" #-}
                    recipV sym)
  , ("/."         , {-# SCC "Prelude::(/.)" #-}
                    fieldDivideV sym)

    -- Round
  , ("floor"      , {-# SCC "Prelude::floor" #-}
                    unary (floorV sym))
  , ("ceiling"    , {-# SCC "Prelude::ceiling" #-}
                    unary (ceilingV sym))
  , ("trunc"      , {-# SCC "Prelude::trunc" #-}
                    unary (truncV sym))
  , ("roundAway"  , {-# SCC "Prelude::roundAway" #-}
                    unary (roundAwayV sym))
  , ("roundToEven", {-# SCC "Prelude::roundToEven" #-}
                    unary (roundToEvenV sym))

    -- Bitvector specific operations
  , ("toSignedInteger"
                  , {-# SCC "Prelude::toSignedInteger" #-}
                    toSignedIntegerV sym)
  , ("/$"         , {-# SCC "Prelude::(/$)" #-}
                    sdivV sym)
  , ("%$"         , {-# SCC "Prelude::(%$)" #-}
                    smodV sym)
  , ("lg2"        , {-# SCC "Prelude::lg2" #-}
                    lg2V sym)

    -- Cmp
  , ("<"          , {-# SCC "Prelude::(<)" #-}
                    binary (lessThanV sym))
  , (">"          , {-# SCC "Prelude::(>)" #-}
                    binary (greaterThanV sym))
  , ("<="         , {-# SCC "Prelude::(<=)" #-}
                    binary (lessThanEqV sym))
  , (">="         , {-# SCC "Prelude::(>=)" #-}
                    binary (greaterThanEqV sym))
  , ("=="         , {-# SCC "Prelude::(==)" #-}
                    binary (eqV sym))
  , ("!="         , {-# SCC "Prelude::(!=)" #-}
                    binary (distinctV sym))

    -- SignedCmp
  , ("<$"         , {-# SCC "Prelude::(<$)" #-}
                    binary (signedLessThanV sym))

    -- Finite enumerations
  , ("fromTo"     , {-# SCC "Prelude::fromTo" #-}
                    fromToV sym)

  , ("fromThenTo" , {-# SCC "Prelude::fromThenTo" #-}
                    fromThenToV sym)

  , ("fromToLessThan"
                  , {-# SCC "Prelude::fromToLessThan" #-}
                    fromToLessThanV sym)

  , ("fromToBy"   , {-# SCC "Prelude::fromToBy" #-}
                    fromToByV sym)

  , ("fromToByLessThan",
                    {-# SCC "Prelude::fromToByLessThan" #-}
                    fromToByLessThanV sym)

  , ("fromToDownBy", {-# SCC "Prelude::fromToDownBy" #-}
                     fromToDownByV sym)

  , ("fromToDownByGreaterThan"
                  , {-# SCC "Prelude::fromToDownByGreaterThan" #-}
                    fromToDownByGreaterThanV sym)

    -- Sequence manipulations
  , ("#"          , {-# SCC "Prelude::(#)" #-}
                    PFinPoly \front ->
                    PNumPoly \back  ->
                    PTyPoly  \elty  ->
                    PFun \l ->
                    PFun \r ->
                    PPrim $ ccatV sym front back elty l r)

  , ("join"       , {-# SCC "Prelude::join" #-}
                    PNumPoly \parts ->
                    PFinPoly \each  ->
                    PTyPoly  \a     ->
                    PFun     \x   ->
                    PPrim $ joinV sym parts each a x)

  , ("split"      , {-# SCC "Prelude::split" #-}
                    PNumPoly \parts ->
                    PFinPoly \each ->
                    PTyPoly  \a ->
                    PFun     \val ->
                    PPrim $ splitV sym parts each a val)

  , ("take"       , {-# SCC "Preldue::take" #-}
                    PNumPoly \front ->
                    PNumPoly \back ->
                    PTyPoly  \a ->
                    PFun     \xs ->
                    PPrim $ takeV sym front back a xs)

  , ("drop"       , {-# SCC "Preldue::drop" #-}
                    PFinPoly \front ->
                    PNumPoly \back ->
                    PTyPoly  \a ->
                    PFun     \xs ->
                    PPrim $ dropV sym front back a xs)

  , ("reverse"    , {-# SCC "Prelude::reverse" #-}
                    PFinPoly \a ->
                    PTyPoly  \b ->
                    PFun     \xs ->
                    PPrim $ reverseV sym a b xs)

  , ("transpose"  , {-# SCC "Prelude::transpose" #-}
                    PNumPoly \a ->
                    PNumPoly \b ->
                    PTyPoly  \c ->
                    PFun     \xs ->
                    PPrim $ transposeV sym a b c =<< xs)

    -- Shifts and rotates
  , ("<<"         , {-# SCC "Prelude::(<<)" #-}
                    logicShift sym "<<" shiftShrink
                      (wordShiftLeft sym) (wordShiftRight sym)
                      shiftLeftReindex shiftRightReindex)
  , (">>"         , {-# SCC "Prelude::(>>)" #-}
                    logicShift sym ">>"  shiftShrink
                      (wordShiftRight sym) (wordShiftLeft sym)
                      shiftRightReindex shiftLeftReindex)
  , ("<<<"        , {-# SCC "Prelude::(<<<)" #-}
                    logicShift sym "<<<" rotateShrink
                      (wordRotateLeft sym) (wordRotateRight sym)
                      rotateLeftReindex rotateRightReindex)
  , (">>>"        , {-# SCC "Prelude::(>>>)" #-}
                    logicShift sym ">>>" rotateShrink
                      (wordRotateRight sym) (wordRotateLeft sym)
                      rotateRightReindex rotateLeftReindex)

  , (">>$"        , {-# SCC "Prelude::(>>$)" #-}
                    sshrV sym)

    -- Misc

    -- {at,len} (fin len) => [len][8] -> at
  , ("error"      , {-# SCC "Prelude::error" #-}
                     PTyPoly  \a ->
                     PFinPoly \_ ->
                     PStrict  \s ->
                     PPrim (errorV sym a =<< valueToString sym s))

  , ("trace"       , {-# SCC "Prelude::trace" #-}
                     PNumPoly \_n ->
                     PTyPoly  \_a ->
                     PTyPoly  \_b ->
                     PFun     \s ->
                     PFun     \x ->
                     PFun     \y ->
                     PPrim
                      do msg <- valueToString sym =<< s
                         EvalOpts { evalPPOpts, evalLogger } <- liftIO getEOpts
                         doc <- ppValue sym evalPPOpts =<< x
                         liftIO $ logPrint evalLogger
                             $ if null msg then doc else text msg <+> doc
                         y)

  , ("random"      , {-# SCC "Prelude::random" #-}
                     PTyPoly  \a ->
                     PWordFun \x ->
                     PPrim
                       case wordAsLit sym x of
                         Just (_,i)  -> randomV sym a i
                         Nothing -> liftIO (X.throw (UnsupportedSymbolicOp "random")))

  , ("foldl"      , {-# SCC "Prelude::foldl" #-}
                    foldlV sym)

  , ("foldl'"     , {-# SCC "Prelude::foldl'" #-}
                    foldl'V sym)

  , ("scanl"      , {-# SCC "Prelude::scanl" #-}
                    scanlV sym)

  , ("deepseq"    , {-# SCC "Prelude::deepseq" #-}
                    PTyPoly \_a ->
                    PTyPoly \_b ->
                    PFun \x ->
                    PFun \y ->
                    PPrim do _ <- forceValue =<< x
                             y)

  , ("parmap"     , {-# SCC "Prelude::parmap" #-}
                    parmapV sym)

  , ("fromZ"      , {-# SCC "Prelude::fromZ" #-}
                    fromZV sym)

  ]
