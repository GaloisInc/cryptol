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
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Cryptol.Eval.Generic where

import qualified Control.Exception as X
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad (join, unless)

import Data.Bits (testBit,bit)
import Data.Maybe (fromMaybe)
import Data.Ratio ((%))

import Cryptol.TypeCheck.Solver.InfNat (Nat'(..),nMul,widthInteger, nAdd)
import Cryptol.Eval.Backend
import Cryptol.Eval.Concrete.Value (Concrete(..))
import Cryptol.Eval.Monad
import Cryptol.Eval.Type
import Cryptol.Eval.Value
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.RecordMap

{-# SPECIALIZE mkLit :: Concrete -> TValue -> Integer -> Eval (GenValue Concrete)
  #-}

-- | Make a numeric literal value at the given type.
mkLit :: Backend sym => sym -> TValue -> Integer -> SEval sym (GenValue sym)
mkLit sym ty i =
  case ty of
    TVInteger                    -> VInteger <$> integerLit sym i
    TVIntMod m
      | m == 0                   -> evalPanic "mkLit" ["0 modulus not allowed"]
      | otherwise                -> VInteger <$> integerLit sym (i `mod` m)
    TVFloat e p                  -> VFloat <$> fpLit sym e p (fromInteger i)
    TVSeq w TVBit                -> word sym w i
    TVRational                   -> VRational <$> (intToRational sym =<< integerLit sym i)
    _                            -> evalPanic "Cryptol.Eval.Prim.evalConst"
                                    [ "Invalid type for number" ]

{-# SPECIALIZE ecNumberV :: Concrete -> GenValue Concrete
  #-}

-- | Make a numeric constant.
ecNumberV :: Backend sym => sym -> GenValue sym
ecNumberV sym =
  nlam $ \valT ->
  VPoly $ \ty ->
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
intV sym i = ringNullary sym (\w -> wordFromInt sym w i) (pure i) (\m -> intToZn sym m i) (intToRational sym i)
            (\e p -> fpRndMode sym >>= \r -> fpFromInteger sym e p r i)

{-# SPECIALIZE ratioV :: Concrete -> GenValue Concrete #-}
ratioV :: Backend sym => sym -> GenValue sym
ratioV sym =
  lam $ \x -> return $
  lam $ \y ->
    do x' <- fromVInteger <$> x
       y' <- fromVInteger <$> y
       VRational <$> ratio sym x' y'

{-# SPECIALIZE ecFractionV :: Concrete -> GenValue Concrete
  #-}
ecFractionV :: Backend sym => sym -> GenValue sym
ecFractionV sym =
  ilam  \n ->
  ilam  \d ->
  ilam  \_r ->
  VPoly \ty ->
    case ty of
      TVFloat e p -> VFloat    <$> fpLit sym e p (n % d)
      TVRational ->
        do x <- integerLit sym n
           y <- integerLit sym d
           VRational <$> ratio sym x y

      _ -> evalPanic "ecFractionV"
            [ "Unexpected `FLiteral` type: " ++ show ty ]



{-# SPECIALIZE fromZV :: Concrete -> GenValue Concrete #-}
fromZV :: Backend sym => sym -> GenValue sym
fromZV sym =
  nlam $ \(finNat' -> n) ->
  lam $ \v -> VInteger <$> (znToInt sym n . fromVInteger =<< v)

-- Operation Lifting -----------------------------------------------------------


type Binary sym = TValue -> GenValue sym -> GenValue sym -> SEval sym (GenValue sym)

{-# INLINE binary
  #-}
binary :: Backend sym => Binary sym -> GenValue sym
binary f = tlam $ \ ty ->
            lam $ \ a  -> return $
            lam $ \ b  -> join (f ty <$> a <*> b)

type Unary sym = TValue -> GenValue sym -> SEval sym (GenValue sym)

{-# INLINE unary
  #-}
unary :: Backend sym => Unary sym -> GenValue sym
unary f = tlam $ \ ty ->
           lam $ \ a  -> f ty =<< a


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
      | isTBit a ->
          do lw <- packSeqMap sym w (fromVSeq l)
             rw <- packSeqMap sym w (fromVSeq r)
             zw <- opw w lw rw
             VSeq (Nat w) a <$> unpackSeqMap sym zw

      | otherwise ->
          VSeq (Nat w) a <$> zipSeqMap sym (loop' a) (fromVSeq l) (fromVSeq r)

    TVStream a ->
       VSeq Inf a <$> zipSeqMap sym (loop' a) (fromVSeq l) (fromVSeq r)

    -- functions
    TVFun _ ety ->
       return $ lam $ \ x -> loop' ety (fromVFun l x) (fromVFun r x)

    -- tuples
    TVTuple tys ->
      do ls <- mapM (sDelay sym Nothing) (fromVTuple l)
         rs <- mapM (sDelay sym Nothing) (fromVTuple r)
         return $ VTuple (zipWith3 loop' tys ls rs)

    -- records
    TVRec fs ->
      do VRecord <$>
            traverseRecordMap
              (\f fty -> sDelay sym Nothing (loop' fty (lookupRecord f l) (lookupRecord f r)))
              fs

    TVAbstract {} ->
      evalPanic "ringBinary" ["Abstract type not in `Ring`"]

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
      | isTBit a ->
          do wx <- packSeqMap sym w (fromVSeq v)
             wz <- opw w wx
             VSeq (Nat w) a <$> unpackSeqMap sym wz
      | otherwise ->
          VSeq (Nat w) a <$> mapSeqMap sym (loop' a) (fromVSeq v)

    TVStream a ->
      VSeq Inf a <$> mapSeqMap sym (loop' a) (fromVSeq v)

    -- functions
    TVFun _ ety ->
      return $ lam $ \ y -> loop' ety (fromVFun v y)

    -- tuples
    TVTuple tys ->
      do as <- mapM (sDelay sym Nothing) (fromVTuple v)
         return $ VTuple (zipWith loop' tys as)

    -- records
    TVRec fs ->
      VRecord <$>
        traverseRecordMap
          (\f fty -> sDelay sym Nothing (loop' fty (lookupRecord f v)))
          fs

    TVAbstract {} -> evalPanic "ringUnary" ["Abstract type not in `Ring`"]

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
          | isTBit a  -> VSeq (Nat w) a <$> (unpackSeqMap sym =<< opw w)
          | otherwise ->
             do v <- sDelay sym Nothing (loop a)
                VSeq (Nat w) a <$> generateSeqMap sym (const v)

        TVStream a ->
             do v <- sDelay sym Nothing (loop a)
                VSeq Inf a <$> generateSeqMap sym (const v)

        TVFun _ b ->
             do v <- sDelay sym Nothing (loop b)
                pure $ lam $ const $ v

        TVTuple tys ->
             do xs <- mapM (sDelay sym Nothing . loop) tys
                pure $ VTuple xs

        TVRec fs ->
             do xs <- traverse (sDelay sym Nothing . loop) fs
                pure $ VRecord xs

        TVAbstract {} ->
          evalPanic "ringNullary" ["Abstract type not in `Ring`"]

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
          do lw <- packSeqMap sym w (fromVSeq l)
             rw <- packSeqMap sym w (fromVSeq r)
             zw <- opw w lw rw
             VSeq (Nat w) a <$> unpackSeqMap sym zw

    _ -> evalPanic "integralBinary" [show ty ++ " not int class `Integral`"]


---------------------------------------------------------------------------
-- Ring

{-# SPECIALIZE fromIntegerV :: Concrete -> GenValue Concrete
  #-}
-- | Convert an unbounded integer to a value in Ring
fromIntegerV :: Backend sym => sym -> GenValue sym
fromIntegerV sym =
  tlam $ \ a ->
  lam  $ \ v ->
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

{-# SPECIALIZE expV :: Concrete -> GenValue Concrete #-}
expV :: Backend sym => sym -> GenValue sym
expV sym =
  tlam $ \aty ->
  tlam $ \ety ->
   lam $ \am -> return $
   lam $ \em ->
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
                    do ebits <- enumerateIntBits' sym n ei
                       computeExponent sym aty a ebits

                | otherwise -> raiseError sym NegativeExponent

              Nothing -> liftIO (X.throw (UnsupportedSymbolicOp "integer exponentiation"))

          TVSeq w el | isTBit el ->
            do ebits <- traverse (fromVBit <$>) (enumerateSeqMap sym w (fromVSeq e))
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
      acc' <- iteValue sym aty b
                (mulV sym aty a sq)
                (pure sq)
      loop acc' bs

{-# INLINE modV #-}
modV :: Backend sym => sym -> Binary sym
modV sym = integralBinary sym opw opi
  where
    opw _w x y = wordMod sym x y
    opi x y = intMod sym x y

{-# SPECIALIZE toIntegerV :: Concrete -> GenValue Concrete #-}
-- | Convert a word to a non-negative integer.
toIntegerV :: Backend sym => sym -> GenValue sym
toIntegerV sym =
  tlam $ \a ->
  lam $ \v ->
    case a of
      TVSeq w el | isTBit el ->
        VInteger <$> (wordToInt sym =<< (packSeqMap sym w . fromVSeq =<< v))
      TVInteger -> v
      _ -> evalPanic "toInteger" [show a ++ " not in class `Integral`"]

-----------------------------------------------------------------------------
-- Field

{-# SPECIALIZE recipV :: Concrete -> GenValue Concrete #-}
recipV :: Backend sym => sym -> GenValue sym
recipV sym =
  tlam $ \a ->
  lam $ \x ->
    case a of
      TVRational -> VRational <$> (rationalRecip sym . fromVRational =<< x)
      TVFloat e p ->
        do one <- fpLit sym e p 1
           r   <- fpRndMode sym
           xv  <- fromVFloat <$> x
           VFloat <$> fpDiv sym r one xv

      _ -> evalPanic "recip"  [show a ++ "is not a Field"]

{-# SPECIALIZE fieldDivideV :: Concrete -> GenValue Concrete #-}
fieldDivideV :: Backend sym => sym -> GenValue sym
fieldDivideV sym =
  tlam $ \a ->
  lam $ \x -> return $
  lam $ \y ->
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
lg2V :: Backend sym => sym -> GenValue sym
lg2V sym =
  nlam $ \(finNat' -> w) ->
  wlam sym $ \x ->
    VSeq (Nat w) TVBit <$> (unpackSeqMap sym =<< wordLg2 sym x)

{-# SPECIALIZE sdivV :: Concrete -> GenValue Concrete #-}
sdivV :: Backend sym => sym -> GenValue sym
sdivV sym =
  nlam $ \(finNat' -> w) ->
  wlam sym $ \x -> return $
  wlam sym $ \y ->
    VSeq (Nat w) TVBit <$> (unpackSeqMap sym =<< wordSignedDiv sym x y)

{-# SPECIALIZE smodV :: Concrete -> GenValue Concrete #-}
smodV :: Backend sym => sym -> GenValue sym
smodV sym  =
  nlam $ \(finNat' -> w) ->
  wlam sym $ \x -> return $
  wlam sym $ \y ->
    VSeq (Nat w) TVBit <$> (unpackSeqMap sym =<< wordSignedMod sym x y)

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
          | isTBit t -> -- TODO! this is too strict...
               do w1 <- packSeqMap sym n (fromVSeq v1)
                  w2 <- packSeqMap sym n (fromVSeq v2)
                  fw w1 w2 k
          | otherwise -> cmpValues (repeat t)
                           (enumerateSeqMap sym n (fromVSeq v1))
                           (enumerateSeqMap sym n (fromVSeq v2))
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
        TVAbstract {} -> evalPanic "cmpValue"
                          [ "Abstract type not in `Cmp`" ]

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

lazyBitIte :: Backend sym =>
  sym ->
  SEval sym (SBit sym) ->
  SEval sym (SBit sym) ->
  SEval sym (SBit sym) ->
  SEval sym (SBit sym)
lazyBitIte sym c x y =
  do c' <- c
     case bitAsLit sym c' of
       Just True -> x
       Just False -> y
       Nothing -> mergeEval sym (iteBit sym) c'  x y

{-# INLINE eqCombine #-}
eqCombine :: Backend sym =>
  sym ->
  SEval sym (SBit sym) ->
  SEval sym (SBit sym) ->
  SEval sym (SBit sym)
eqCombine sym eq k =
  -- if eq then k else false
  lazyBitIte sym eq k (pure (bitLit sym False))

{-# INLINE lexCombine #-}
lexCombine :: Backend sym =>
  sym ->
  SEval sym (SBit sym) ->
  SEval sym (SBit sym) ->
  SEval sym (SBit sym) ->
  SEval sym (SBit sym)
lexCombine sym cmp eq k =
  -- if cmp then true else (if eq then k else false)
  lazyBitIte sym cmp (pure (bitLit sym True))
    (lazyBitIte sym eq k (pure (bitLit sym False)))

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
           do z <- sDelay sym Nothing (zeroV sym ety)
              VSeq (Nat w) ety <$> generateSeqMap sym (const z)

  TVStream ety ->
     do z <- sDelay sym Nothing (zeroV sym ety)
        VSeq Inf ety <$> generateSeqMap sym (const z)

  -- functions
  TVFun _ bty ->
     do z <- sDelay sym Nothing (zeroV sym bty)
        pure $ lam (const z)

  -- tuples
  TVTuple tys ->
      do xs <- mapM (sDelay sym Nothing . zeroV sym) tys
         pure $ VTuple xs

  -- records
  TVRec fields ->
      do xs <- traverse (sDelay sym Nothing . zeroV sym) fields
         pure $ VRecord xs

  TVAbstract {} -> evalPanic "zeroV" [ "Abstract type not in `Zero`" ]



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
  do xs <- delaySeqMap sym (fromVSeq <$> val)
     VSeq (nMul parts (Nat each)) a <$> joinSeqMap sym each xs

splitV ::
  Backend sym =>
  sym ->
  Nat' ->
  Integer ->
  TValue ->
  SEval sym (GenValue sym) ->
  SEval sym (GenValue sym)
splitV sym parts each a val =
  do xs <- delaySeqMap sym (fromVSeq <$> val)
     VSeq parts (TVSeq each a) <$> generateSeqMap sym (\p ->
       VSeq (Nat each) a <$> dropSeqMap sym (p * each) xs)

{-# INLINE splitAtV #-}
splitAtV ::
  Backend sym =>
  sym ->
  Integer ->
  Nat' ->
  TValue ->
  SEval sym (GenValue sym) ->
  SEval sym (GenValue sym)
splitAtV sym front back a val =
  do xs <- delaySeqMap sym (fromVSeq <$> val)
     pure $ VTuple
       [ VSeq (Nat front) a <$> takeSeqMap sym front xs
       , VSeq back a <$> dropSeqMap sym front xs
       ]

{-# INLINE takeV #-}
takeV :: forall sym.
  Backend sym =>
  sym ->
  Nat' ->
  TValue ->
  SEval sym (GenValue sym) ->
  SEval sym (GenValue sym)
takeV sym Inf a v =
  VSeq Inf a <$> delaySeqMap sym (fromVSeq <$> v)
takeV sym (Nat n) a v =
  do xs <- delaySeqMap sym (fromVSeq <$> v)
     VSeq (Nat n) a <$> takeSeqMap sym n xs

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

ccatV sym front back a l r =
  do l' <- delaySeqMap sym (fromVSeq <$> l)
     r' <- delaySeqMap sym (fromVSeq <$> r)
     VSeq (nAdd (Nat front) back) a <$> concatSeqMap sym front l' r'

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
         | isTBit aty ->
              VSeq (Nat w) aty <$>
                bitwiseWordBinOp sym w
                   (\x y -> join (opb <$> x <*> y)) opw
                   (fromVSeq l) (fromVSeq r)

         -- finite sequences
         | otherwise ->
              VSeq (Nat w) aty <$>
                zipSeqMap sym (loop' aty) (fromVSeq l) (fromVSeq r)

    TVStream aty ->
        VSeq Inf aty <$> zipSeqMap sym (loop' aty) (fromVSeq l) (fromVSeq r)

    TVTuple etys -> do
        ls <- mapM (sDelay sym Nothing) (fromVTuple l)
        rs <- mapM (sDelay sym Nothing) (fromVTuple r)
        return $ VTuple $ zipWith3 loop' etys ls rs

    TVFun _ bty ->
        return $ lam $ \ a -> loop' bty (fromVFun l a) (fromVFun r a)

    TVRec fields ->
      VRecord <$>
        traverseRecordMap
          (\f fty -> sDelay sym Nothing (loop' fty (lookupRecord f l) (lookupRecord f r)))
          fields

    TVAbstract {} -> evalPanic "logicBinary"
                        [ "Abstract type not in `Logic`" ]

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
         | isTBit ety ->
              VSeq (Nat w) ety <$>
                bitwiseWordUnOp sym w
                   (\x -> opb =<< x) opw
                   (fromVSeq val)

         -- finite sequences
         | otherwise ->
              VSeq (Nat w) ety <$> mapSeqMap sym (loop' ety) (fromVSeq val)

         -- streams
    TVStream ety ->
         VSeq Inf ety <$> mapSeqMap sym (loop' ety) (fromVSeq val)

    TVTuple etys ->
      do as <- mapM (sDelay sym Nothing) (fromVTuple val)
         return $ VTuple (zipWith loop' etys as)

    TVFun _ bty ->
      return $ lam $ \ a -> loop' bty (fromVFun val a)

    TVRec fields ->
      VRecord <$>
        traverseRecordMap
          (\f fty -> sDelay sym Nothing (loop' fty (lookupRecord f val)))
          fields

    TVAbstract {} -> evalPanic "logicUnary" [ "Abstract type not in `Logic`" ]


{-# SPECIALIZE bitsValueLessThan ::
  Concrete ->
  Integer ->
  [SBit Concrete] ->
  Integer ->
  SEval Concrete (SBit Concrete)
  #-}
bitsValueLessThan ::
  Backend sym =>
  sym ->
  Integer {- ^ bit-width -} ->
  [SBit sym] {- ^ big-endian list of index bits -} ->
  Integer {- ^ Upper bound to test against -} ->
  SEval sym (SBit sym)
bitsValueLessThan sym _w [] _n = pure $ bitLit sym False
bitsValueLessThan sym w (b:bs) n
  | nbit =
      do notb <- bitComplement sym b
         bitOr sym notb =<< bitsValueLessThan sym (w-1) bs n
  | otherwise =
      do notb <- bitComplement sym b
         bitAnd sym notb =<< bitsValueLessThan sym (w-1) bs n
 where
 nbit = testBit n (fromInteger (w-1))


{-# INLINE assertIndexInBounds #-}
assertIndexInBounds ::
  Backend sym =>
  sym ->
  Nat' {- ^ Sequence size bounds -} ->
  Either (SInteger sym) (SWord sym) {- ^ Index value -} ->
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
assertIndexInBounds sym (Nat n) (Right idx)
  | n >= 2^(wordLen sym idx)
  = return ()

-- If the index is concrete, test it directly
assertIndexInBounds sym (Nat n) (Right idx)
  | Just (_w,i) <- wordAsLit sym idx
  = unless (i < n) (raiseError sym (InvalidIndex (Just i)))

-- If the index is a packed word, test that it
-- is less than the concrete value of n, which
-- fits into w bits because of the above test.
assertIndexInBounds sym (Nat n) (Right idx) =
  do n' <- wordLit sym (wordLen sym idx) n
     p <- wordLessThan sym idx n'
     assertSideCondition sym p (InvalidIndex Nothing)


-- | Indexing operations.

{-# INLINE indexPrim #-}
indexPrim ::
  Backend sym =>
  sym ->
  (Nat' -> TValue -> SeqMap sym -> TValue -> SInteger sym -> SEval sym (GenValue sym)) ->
  (Nat' -> TValue -> SeqMap sym -> TValue -> SWord sym -> SEval sym (GenValue sym)) ->
  GenValue sym
indexPrim sym int_op word_op =
  nlam $ \ len  ->
  tlam $ \ eltTy ->
  tlam $ \ ix ->
   lam $ \ xs  -> return $
   lam $ \ idx  -> do
      vs <- fromVSeq <$> xs
      idx' <- asIndex sym "index" ix =<< idx
      assertIndexInBounds sym len idx'
      case idx' of
        Left i   -> int_op len eltTy vs ix i
        Right w' -> word_op len eltTy vs ix w'

{-# INLINE updatePrim #-}

updatePrim ::
  Backend sym =>
  sym ->
  (Nat' ->
   TValue ->
   SEval sym (SeqMap sym) ->
   Either (SInteger sym) (SWord sym) ->
   SEval sym (GenValue sym) ->
   SEval sym (SeqMap sym)) ->
  GenValue sym
updatePrim sym updateSeq =
  nlam $ \len ->
  tlam $ \eltTy ->
  tlam $ \ix ->
  lam $ \xs  -> return $
  lam $ \idx -> return $
  lam $ \val -> do
    idx' <- asIndex sym "update" ix =<< idx
    assertIndexInBounds sym len idx'
    VSeq len eltTy <$> updateSeq len eltTy (fromVSeq <$> xs) idx' val

{-# INLINE fromToV #-}

-- @[ 0 .. 10 ]@
fromToV :: Backend sym => sym -> GenValue sym
fromToV sym =
  nlam $ \ first ->
  nlam $ \ lst   ->
  VPoly $ \ ty   ->
    let f = mkLit sym ty in
    case (first, lst) of
      (Nat first', Nat lst') ->
        do let len = 1 + (lst' - first')
           VSeq (Nat len) ty <$> generateSeqMap sym (\i -> f (first' + i))

      _ -> evalPanic "fromToV" ["invalid arguments"]

{-# INLINE fromThenToV #-}

-- @[ 0, 1 .. 10 ]@
fromThenToV :: Backend sym => sym -> GenValue sym
fromThenToV sym =
  nlam $ \ first ->
  nlam $ \ next  ->
  nlam $ \ lst   ->
  tlam $ \ ty    ->
  VNumPoly $ \ len   ->
    let !f = mkLit sym ty in
    case (first, next, lst, len) of
      (Nat first', Nat next', Nat _lst', Nat len') ->
        do let diff = next' - first'
           VSeq (Nat len') ty <$> generateSeqMap sym (\i -> f (first' + i*diff))
      _ -> evalPanic "fromThenToV" ["invalid arguments"]

{-# INLINE infFromV #-}
infFromV :: Backend sym => sym -> GenValue sym
infFromV sym =
  tlam $ \ ty ->
  lam  $ \ x ->
  do mx <- sDelay sym Nothing x
     VSeq Inf ty <$> generateSeqMap sym (\i ->
       do x' <- mx
          i' <- integerLit sym i
          addV sym ty x' =<< intV sym i' ty)

{-# INLINE infFromThenV #-}
infFromThenV :: Backend sym => sym -> GenValue sym
infFromThenV sym =
  tlam $ \ ty ->
  lam $ \ first -> return $
  lam $ \ next ->
  do mxd <- sDelay sym Nothing
             (do x <- first
                 y <- next
                 d <- subV sym ty y x
                 pure (x,d))
     VSeq Inf ty <$> generateSeqMap sym (\i ->
       do (x,d) <- mxd
          i' <- integerLit sym i
          addV sym ty x =<< mulV sym ty d =<< intV sym i' ty)

-- Shifting ---------------------------------------------------

-- | Barrel shift/rotate algorithm for sequences.
--   It takes the shift/rotate amount as a big-endian
--   sequence of bits and constructs a barrel shifting network
--   by shifting the initial input map concrete amounts corresponding
--   to the powers of two of the input bits.  For finite-length
--   sequences, we assume the shift amount has already been
--   reduced (via claming for shifts or taking modulus for rotates)
--   so the value is between @0@ and @n@, where @n@ is the length of
--   the sequence.  As a result, the barrel shift network will have
--   depth @min(width(n),w)@, where @w@ is the number of bits
--   in the index.
barrelShifter :: forall sym. Backend sym =>
  sym ->
  Nat' {- ^ length of the sequence being shifted -} ->
  TValue {- ^ element type of the sequence -} ->
  (SeqMap sym -> Integer -> SEval sym (SeqMap sym))
     {- ^ concrete shifting/rotation operation -} ->
  SeqMap sym  {- ^ initial value -} ->
  [SBit sym]  {- ^ bits of shift amount, in big-endian order -} ->
  SEval sym (SeqMap sym)
barrelShifter sym len tv shift_op x0 allbits =
    case len of
      Nat sz | wsz < toInteger lenbits -> go x0 wszInt (drop (lenbits - wszInt) allbits)
          where wsz = widthInteger sz
                wszInt = (fromInteger wsz) :: Int

                --lg2sz = lg2 sz
                --lg2szInt = (fromInteger lg2sz) :: Int

      _ -> go x0 lenbits allbits

  where
  lenbits = length allbits

  go :: SeqMap sym -> Int -> [SBit sym] -> SEval sym (SeqMap sym)
  go x !_ [] = return x

  go x !blen (b:bs)
    | Just True <- bitAsLit sym b
    = do x_shft <- shift_op x (bit (blen-1))
         go x_shft (blen-1) bs

    | Just False <- bitAsLit sym b
    = do go x (blen-1) bs

    | otherwise
    = do x_shft <- shift_op x (bit (blen-1))
         x' <- mergeSeqMap sym len tv b x_shft x
         go x' (blen-1) bs

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

-- | Compute the list of bits in an integer in big-endian order.
--   Fails if neither the sequence length nor the type value
--   provide an upper bound for the integer.
enumerateIntBits :: Backend sym =>
  sym ->
  Nat' ->
  SInteger sym ->
  SEval sym [SBit sym]
enumerateIntBits sym (Nat n) idx = enumerateIntBits' sym n idx
enumerateIntBits _sym Inf _ = liftIO (X.throw (UnsupportedSymbolicOp "unbounded integer shifting"))

-- | Compute the list of bits in an integer in big-endian order.
--   The integer argument is a concrete upper bound for
--   the symbolic integer.
enumerateIntBits' :: Backend sym =>
  sym ->
  Integer ->
  SInteger sym ->
  SEval sym [SBit sym]
enumerateIntBits' sym n idx =
  do w <- wordFromInt sym (widthInteger n) idx
     unpackWord sym w

-- | Generic implementation of shifting.
--   Uses the provided word-level operation to perform the shift, when
--   possible.  Otherwise falls back on a barrel shifter that uses
--   the provided reindexing operation to implement the concrete
--   shifting operations.  The reindex operation is given the size
--   of the sequence, the requested index value for the new output sequence,
--   and the amount to shift.  The return value is an index into the original
--   sequence if in bounds, and Nothing otherwise.
logicShift :: forall sym. Backend sym =>
  sym ->
  String ->
  (sym -> Nat' -> SInteger sym -> SEval sym (SInteger sym))
     {- ^ operation for range reduction on integers -} ->
  (sym -> Nat' -> SWord sym -> SEval sym (SWord sym))
     {- ^ operation for range reduction on words -} ->
  (sym -> (Integer -> SEval sym (SeqMap sym)) -> Nat' -> SeqMap sym -> Integer -> SEval sym (SeqMap sym))
     {- ^ concrete shifting operation for positive shifts -} ->
  (sym -> (Integer -> SEval sym (SeqMap sym)) -> Nat' -> SeqMap sym -> Integer -> SEval sym (SeqMap sym))
     {- ^ concrete shifting operation for negative shifts -} ->
  GenValue sym
logicShift sym nm shrinkIntRange shrinkWordRange posShift negShift =
  nlam $ \n ->
  tlam $ \ix ->
  tlam $ \a ->
  VFun $ \xs -> return $
  VFun $ \y ->
    do xs' <- delaySeqMap sym (fromVSeq <$> xs)
       y' <- asIndex sym nm ix =<< y
       let mkZro :: Integer -> SEval sym (SeqMap sym)
           mkZro i
             | TVBit <- a = do z <- wordLit sym i 0
                               unpackSeqMap sym z
             | otherwise  = do z <- zeroV sym a
                               generateSeqMap sym (const (pure z))
       case y' of
         Left int_idx ->
           do pneg <- intLessThan sym int_idx =<< integerLit sym 0
              iteValue sym (tvSeq n a) pneg
                (intShifter sym (negShift sym mkZro n) n a xs' =<< shrinkIntRange sym n =<< intNegate sym int_idx)
                (intShifter sym (posShift sym mkZro n) n a xs' =<< shrinkIntRange sym n int_idx)
         Right idx -> do
           wordShifter sym (posShift sym mkZro n) n a xs' =<< shrinkWordRange sym n idx

intShifter :: Backend sym =>
   sym ->
   (SeqMap sym -> Integer -> SEval sym (SeqMap sym)) ->
   Nat' ->
   TValue ->
   SeqMap sym ->
   SInteger sym ->
   SEval sym (GenValue sym)
intShifter sym shft n a xs idx
   | Just i <- integerAsLit sym idx = VSeq n a <$> shft xs i
   | otherwise =
       do idx_bits <- enumerateIntBits sym n idx
          VSeq n a <$> barrelShifter sym n a shft xs idx_bits

wordShifter :: Backend sym =>
   sym ->
   (SeqMap sym -> Integer -> SEval sym (SeqMap sym)) ->
   Nat' ->
   TValue ->
   SeqMap sym ->
   SWord sym ->
   SEval sym (GenValue sym)
wordShifter sym shft n a xs idx
   | Just (_,i) <- wordAsLit sym idx = VSeq n a <$> shft xs i
   | otherwise =
       do idx_bits <- unpackWord sym idx
          VSeq n a <$> barrelShifter sym n a shft xs idx_bits

shiftIntShrink :: Backend sym => sym -> Nat' -> SInteger sym -> SEval sym (SInteger sym)
shiftIntShrink _sym Inf x = return x
shiftIntShrink sym (Nat w) x =
  do w' <- integerLit sym w
     p  <- intLessThan sym w' x
     iteInteger sym p w' x

shiftWordShrink :: Backend sym => sym -> Nat' -> SWord sym -> SEval sym (SWord sym)
shiftWordShrink _sym Inf x = return x
shiftWordShrink sym (Nat w) x
  | 2^(wordLen sym x) <= w = return x
  | otherwise =
     do w' <- wordLit sym (wordLen sym x) w
        p  <- wordLessThan sym w' x
        iteWord sym p w' x

rotateIntShrink :: Backend sym => sym -> Nat' -> SInteger sym -> SEval sym (SInteger sym)
rotateIntShrink _sym Inf _ = panic "rotateIntShrink" ["expected finite sequence in rotate"]
rotateIntShrink sym (Nat 0) _ = integerLit sym 0
rotateIntShrink sym (Nat w) x =
  do w' <- integerLit sym w
     intMod sym x w'

rotateWordShrink :: Backend sym => sym -> Nat' -> SWord sym -> SEval sym (SWord sym)
rotateWordShrink _sym Inf _ = panic "rotateWordShrink" ["expected finite sequence in rotate"]
rotateWordShrink sym (Nat 0) x = wordLit sym (wordLen sym x) 0
rotateWordShrink sym (Nat w) x
  | 2^(wordLen sym x) <= w = return x
  | otherwise =
     do w' <- wordLit sym (wordLen sym x) w
        wordMod sym x w'

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
errorV sym _ty msg = cryUserError sym msg

{-# INLINE valueToChar #-}

-- | Expect a word value.  Mask it to an 8-bits ASCII value
--   and return the associated character, if it is concrete.
--   Otherwise, return a '?' character
valueToChar :: Backend sym => sym -> GenValue sym -> SEval sym Char
valueToChar sym (VSeq (Nat w) _ wval) =
  do x <- packSeqMap sym w wval
     pure $! fromMaybe '?' (wordAsChar sym x)
valueToChar _ _ = evalPanic "valueToChar" ["Not an 8-bit bitvector"]

{-# INLINE valueToString #-}

valueToString :: Backend sym => sym -> GenValue sym -> SEval sym String
valueToString sym (VSeq (Nat n) _ vals) =
   traverse (valueToChar sym =<<) (enumerateSeqMap sym n vals)
valueToString _ _ = evalPanic "valueToString" ["Not a finite sequence"]




foldlV :: Backend sym => sym -> GenValue sym
foldlV sym =
  ilam $ \_n ->
  tlam $ \_a ->
  tlam $ \_b ->
  lam $ \f -> pure $
  lam $ \z -> pure $
  lam $ \v ->
    v >>= \case
      VSeq n m    -> go0 f z (enumerateSeqMap n m)
      VWord _n wv -> go0 f z . map (pure . VBit) =<< (enumerateWordValue sym =<< wv)
      _ -> panic "Cryptol.Eval.Generic.foldlV" ["Expected finite sequence"]
  where
  go0 _f a [] = a
  go0 f a bs =
    do f' <- fromVFun <$> f
       go1 f' a bs

  go1 _f a [] = a
  go1 f a (b:bs) =
    do f' <- fromVFun <$> (f a)
       go1 f (f' b) bs

foldl'V :: Backend sym => sym -> GenValue sym
foldl'V sym =
  ilam $ \_n ->
  tlam $ \_a ->
  tlam $ \_b ->
  lam $ \f -> pure $
  lam $ \z -> pure $
  lam $ \v ->
    v >>= \case
      VSeq n m    -> go0 f z (enumerateSeqMap n m)
      VWord _n wv -> go0 f z . map (pure . VBit) =<< (enumerateWordValue sym =<< wv)
      _ -> panic "Cryptol.Eval.Generic.foldlV" ["Expected finite sequence"]
  where
  go0 _f a [] = a
  go0 f a bs =
    do f' <- fromVFun <$> f
       a' <- a
       go1 f' a' bs

  go1 _f a [] = pure a
  go1 f a (b:bs) =
    do f' <- fromVFun <$> (f (pure a))
       a' <- f' b
       go1 f a' bs

--------------------------------------------------------------------------------
-- Experimental parallel primitives

parmapV :: Backend sym => sym -> GenValue sym
parmapV sym =
  tlam $ \_a ->
  tlam $ \b ->
  ilam $ \n ->
  lam $ \f -> pure $
  lam $ \xs ->
    do f' <- fromVFun <$> f
       xs' <- fromVSeq <$> xs
       VSeq (Nat n) b <$> sparkParMap sym f' n xs'

sparkParMap ::
  Backend sym =>
  sym ->
  (SEval sym (GenValue sym) -> SEval sym (GenValue sym)) ->
  Integer ->
  SeqMap sym ->
  SEval sym (SeqMap sym)
sparkParMap sym f n m =
  finiteSeqMap sym =<< mapM (\x -> sSpark sym (forceValue sym =<< f x)) (enumerateSeqMap sym n m)

--------------------------------------------------------------------------------
-- Floating Point Operations

-- | Make a Cryptol value for a binary arithmetic function.
fpBinArithV :: Backend sym => sym -> FPArith2 sym -> GenValue sym
fpBinArithV sym fun =
  ilam \_ ->
  ilam \_ ->
  wlam sym \r ->
  pure $ flam \x ->
  pure $ flam \y ->
  VFloat <$> fun sym r x y

-- | Rounding mode used in FP operations that do not specify it explicitly.
fpRndMode, fpRndRNE, fpRndRNA, fpRndRTP, fpRndRTN, fpRndRTZ ::
   Backend sym => sym -> SEval sym (SWord sym)
fpRndMode    = fpRndRNE
fpRndRNE sym = wordLit sym 3 0 {- to nearest, ties to even -}
fpRndRNA sym = wordLit sym 3 1 {- to nearest, ties to away from 0 -}
fpRndRTP sym = wordLit sym 3 2 {- to +inf -}
fpRndRTN sym = wordLit sym 3 3 {- to -inf -}
fpRndRTZ sym = wordLit sym 3 4 {- to 0    -}
