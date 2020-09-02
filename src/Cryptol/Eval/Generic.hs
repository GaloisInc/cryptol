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
{-# LANGUAGE Safe #-}
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

import Data.Bits (testBit)
import Data.Maybe (fromMaybe)
import Data.Ratio ((%))

import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Solver.InfNat (Nat'(..),nMul,widthInteger)
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
    TVSeq w TVBit                -> pure $ word sym w i
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

{-# SPECIALIZE binary :: Binary Concrete -> GenValue Concrete
  #-}
binary :: Backend sym => Binary sym -> GenValue sym
binary f = tlam $ \ ty ->
            lam $ \ a  -> return $
            lam $ \ b  -> do
               --io $ putStrLn "Entering a binary function"
               join (f ty <$> a <*> b)

type Unary sym = TValue -> GenValue sym -> SEval sym (GenValue sym)

{-# SPECIALIZE unary :: Unary Concrete -> GenValue Concrete
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
      | isTBit a -> do
                  lw <- fromVWord sym "ringLeft" l
                  rw <- fromVWord sym "ringRight" r
                  return $ VWord w (WordVal <$> opw w lw rw)
      | otherwise -> VSeq w <$> (join (zipSeqMap (loop a) <$>
                                      (fromSeq "ringBinary left" l) <*>
                                      (fromSeq "ringBinary right" r)))

    TVStream a ->
      -- streams
      VStream <$> (join (zipSeqMap (loop a) <$>
                             (fromSeq "ringBinary left" l) <*>
                             (fromSeq "ringBinary right" r)))

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
      | isTBit a -> do
              wx <- fromVWord sym "ringUnary" v
              return $ VWord w (WordVal <$> opw w wx)
      | otherwise -> VSeq w <$> (mapSeqMap (loop a) =<< fromSeq "ringUnary" v)

    TVStream a ->
      VStream <$> (mapSeqMap (loop a) =<< fromSeq "ringUnary" v)

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
          | isTBit a -> pure $ VWord w $ (WordVal <$> opw w)
          | otherwise ->
             do v <- sDelay sym Nothing (loop a)
                pure $ VSeq w $ IndexSeqMap $ const v

        TVStream a ->
             do v <- sDelay sym Nothing (loop a)
                pure $ VStream $ IndexSeqMap $ const v

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
          do wl <- fromVWord sym "integralBinary left" l
             wr <- fromVWord sym "integralBinary right" r
             return $ VWord w (WordVal <$> opw w wl wr)

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

          TVSeq _w el | isTBit el ->
            do ebits <- enumerateWordValue sym =<< fromWordVal "(^^)" e
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

{-# SPECIALIZE toIntegerV :: Concrete -> GenValue Concrete #-}
-- | Convert a word to a non-negative integer.
toIntegerV :: Backend sym => sym -> GenValue sym
toIntegerV sym =
  tlam $ \a ->
  lam $ \v ->
    case a of
      TVSeq _w el | isTBit el ->
        VInteger <$> (wordToInt sym =<< (fromVWord sym "toInteger" =<< v))
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
  wlam sym $ \x -> return $
  VWord w (WordVal <$> wordLg2 sym x)

{-# SPECIALIZE sdivV :: Concrete -> GenValue Concrete #-}
sdivV :: Backend sym => sym -> GenValue sym
sdivV sym =
  nlam $ \(finNat' -> w) ->
  wlam sym $ \x -> return $
  wlam sym $ \y -> return $
  VWord w (WordVal <$> wordSignedDiv sym x y)

{-# SPECIALIZE smodV :: Concrete -> GenValue Concrete #-}
smodV :: Backend sym => sym -> GenValue sym
smodV sym  =
  nlam $ \(finNat' -> w) ->
  wlam sym $ \x -> return $
  wlam sym $ \y -> return $
  VWord w (WordVal <$> wordSignedMod sym x y)

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
      | isTBit ety -> pure $ word sym w 0
      | otherwise  ->
           do z <- sDelay sym Nothing (zeroV sym ety)
              pure $ VSeq w (IndexSeqMap $ const z)

  TVStream ety ->
     do z <- sDelay sym Nothing (zeroV sym ety)
        pure $ VStream (IndexSeqMap $ const z)

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

--  | otherwise = evalPanic "zeroV" ["invalid type for zero"]

{-# INLINE joinWordVal #-}
joinWordVal :: Backend sym => sym -> WordValue sym -> WordValue sym -> SEval sym (WordValue sym)
joinWordVal sym (WordVal w1) (WordVal w2)
  | wordLen sym w1 + wordLen sym w2 < largeBitSize
  = WordVal <$> joinWord sym w1 w2
joinWordVal sym w1 w2
  = pure $ LargeBitsVal (n1+n2) (concatSeqMap n1 (asBitsMap sym w1) (asBitsMap sym w2))
 where n1 = wordValueSize sym w1
       n2 = wordValueSize sym w2


{-# SPECIALIZE joinWords ::
  Concrete ->
  Integer ->
  Integer ->
  SeqMap Concrete ->
  SEval Concrete (GenValue Concrete)
  #-}
joinWords :: forall sym.
  Backend sym =>
  sym ->
  Integer ->
  Integer ->
  SeqMap sym ->
  SEval sym (GenValue sym)
joinWords sym nParts nEach xs =
  loop (WordVal <$> wordLit sym 0 0) (enumerateSeqMap nParts xs)

 where
 loop :: SEval sym (WordValue sym) -> [SEval sym (GenValue sym)] -> SEval sym (GenValue sym)
 loop !wv [] =
    VWord (nParts * nEach) <$> sDelay sym Nothing wv
 loop !wv (w : ws) =
    w >>= \case
      VWord _ w' ->
        loop (join (joinWordVal sym <$> wv <*> w')) ws
      _ -> evalPanic "joinWords: expected word value" []

{-# SPECIALIZE joinSeq ::
  Concrete ->
  Nat' ->
  Integer ->
  TValue ->
  SeqMap Concrete ->
  SEval Concrete (GenValue Concrete)
  #-}
joinSeq ::
  Backend sym =>
  sym ->
  Nat' ->
  Integer ->
  TValue ->
  SeqMap sym ->
  SEval sym (GenValue sym)

-- Special case for 0 length inner sequences.
joinSeq sym _parts 0 a _xs
  = zeroV sym (TVSeq 0 a)

-- finite sequence of words
joinSeq sym (Nat parts) each TVBit xs
  | parts * each < largeBitSize
  = joinWords sym parts each xs
  | otherwise
  = do let zs = IndexSeqMap $ \i ->
                  do let (q,r) = divMod i each
                     ys <- fromWordVal "join seq" =<< lookupSeqMap xs q
                     VBit <$> indexWordValue sym ys r
       return $ VWord (parts * each) $ pure $ LargeBitsVal (parts * each) zs

-- infinite sequence of words
joinSeq sym Inf each TVBit xs
  = return $ VStream $ IndexSeqMap $ \i ->
      do let (q,r) = divMod i each
         ys <- fromWordVal "join seq" =<< lookupSeqMap xs q
         VBit <$> indexWordValue sym ys r

-- finite or infinite sequence of non-words
joinSeq _sym parts each _a xs
  = return $ vSeq $ IndexSeqMap $ \i -> do
      let (q,r) = divMod i each
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
  GenValue sym ->
  SEval sym (GenValue sym)
joinV sym parts each a val = joinSeq sym parts each a =<< fromSeq "joinV" val


{-# INLINE splitWordVal #-}

splitWordVal ::
  Backend sym =>
  sym ->
  Integer ->
  Integer ->
  WordValue sym ->
  SEval sym (WordValue sym, WordValue sym)
splitWordVal sym leftWidth rightWidth (WordVal w) =
  do (lw, rw) <- splitWord sym leftWidth rightWidth w
     pure (WordVal lw, WordVal rw)
splitWordVal _ leftWidth rightWidth (LargeBitsVal _n xs) =
  let (lxs, rxs) = splitSeqMap leftWidth xs
   in pure (LargeBitsVal leftWidth lxs, LargeBitsVal rightWidth rxs)

{-# INLINE splitAtV #-}
splitAtV ::
  Backend sym =>
  sym ->
  Nat' ->
  Nat' ->
  TValue ->
  GenValue sym ->
  SEval sym (GenValue sym)
splitAtV sym front back a val =
  case back of

    Nat rightWidth | aBit -> do
          ws <- sDelay sym Nothing (splitWordVal sym leftWidth rightWidth =<< fromWordVal "splitAtV" val)
          return $ VTuple
                   [ VWord leftWidth  . pure . fst <$> ws
                   , VWord rightWidth . pure . snd <$> ws
                   ]

    Inf | aBit -> do
       vs <- sDelay sym Nothing (fromSeq "splitAtV" val)
       ls <- sDelay sym Nothing (fst . splitSeqMap leftWidth <$> vs)
       rs <- sDelay sym Nothing (snd . splitSeqMap leftWidth <$> vs)
       return $ VTuple [ return $ VWord leftWidth (LargeBitsVal leftWidth <$> ls)
                       , VStream <$> rs
                       ]

    _ -> do
       vs <- sDelay sym Nothing (fromSeq "splitAtV" val)
       ls <- sDelay sym Nothing (fst . splitSeqMap leftWidth <$> vs)
       rs <- sDelay sym Nothing (snd . splitSeqMap leftWidth <$> vs)
       return $ VTuple [ VSeq leftWidth <$> ls
                       , mkSeq back a <$> rs
                       ]

  where
  aBit = isTBit a

  leftWidth = case front of
    Nat n -> n
    _     -> evalPanic "splitAtV" ["invalid `front` len"]


{-# INLINE extractWordVal #-}

-- | Extract a subsequence of bits from a @WordValue@.
--   The first integer argument is the number of bits in the
--   resulting word.  The second integer argument is the
--   number of less-significant digits to discard.  Stated another
--   way, the operation `extractWordVal n i w` is equivalent to
--   first shifting `w` right by `i` bits, and then truncating to
--   `n` bits.
extractWordVal ::
  Backend sym =>
  sym ->
  Integer ->
  Integer ->
  WordValue sym ->
  SEval sym (WordValue sym)
extractWordVal sym len start (WordVal w) =
   WordVal <$> extractWord sym len start w
extractWordVal _ len start (LargeBitsVal n xs) =
   let xs' = dropSeqMap (n - start - len) xs
    in pure $ LargeBitsVal len xs'

{-# INLINE ecSplitV #-}

-- | Split implementation.
ecSplitV :: Backend sym => sym -> GenValue sym
ecSplitV sym =
  nlam $ \ parts ->
  nlam $ \ each  ->
  tlam $ \ a     ->
  lam  $ \ val ->
    case (parts, each) of
       (Nat p, Nat e) | isTBit a -> do
          ~(VWord _ val') <- val
          return $ VSeq p $ IndexSeqMap $ \i ->
            pure $ VWord e (extractWordVal sym e ((p-i-1)*e) =<< val')
       (Inf, Nat e) | isTBit a -> do
          val' <- sDelay sym Nothing (fromSeq "ecSplitV" =<< val)
          return $ VStream $ IndexSeqMap $ \i ->
            return $ VWord e $ return $ LargeBitsVal e $ IndexSeqMap $ \j ->
              let idx = i*e + toInteger j
               in idx `seq` do
                      xs <- val'
                      lookupSeqMap xs idx
       (Nat p, Nat e) -> do
          val' <- sDelay sym Nothing (fromSeq "ecSplitV" =<< val)
          return $ VSeq p $ IndexSeqMap $ \i ->
            return $ VSeq e $ IndexSeqMap $ \j -> do
              xs <- val'
              lookupSeqMap xs (e * i + j)
       (Inf  , Nat e) -> do
          val' <- sDelay sym Nothing (fromSeq "ecSplitV" =<< val)
          return $ VStream $ IndexSeqMap $ \i ->
            return $ VSeq e $ IndexSeqMap $ \j -> do
              xs <- val'
              lookupSeqMap xs (e * i + j)
       _              -> evalPanic "splitV" ["invalid type arguments to split"]

{-# INLINE reverseV #-}

reverseV :: forall sym.
  Backend sym =>
  sym ->
  GenValue sym ->
  SEval sym (GenValue sym)
reverseV _ (VSeq n xs) =
  return $ VSeq n $ reverseSeqMap n xs
reverseV sym (VWord n x) = return (VWord n (revword <$> x))
 where
 revword wv =
   let m = wordValueSize sym wv in
   LargeBitsVal m $ reverseSeqMap m $ asBitsMap sym wv
reverseV _ _ =
  evalPanic "reverseV" ["Not a finite sequence"]

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
      return $ bseq $ IndexSeqMap $ \bi ->
        return $ VWord na $ return $ LargeBitsVal na $ IndexSeqMap $ \ai ->
         do ys <- flip lookupSeqMap (toInteger ai) =<< fromSeq "transposeV" xs
            case ys of
              VStream ys' -> lookupSeqMap ys' bi
              VWord _ wv  -> VBit <$> (flip (indexWordValue sym) bi =<< wv)
              _ -> evalPanic "transpose" ["expected sequence of bits"]

  | isTBit c, Inf <- a = -- [inf][b]Bit -> [b][inf]Bit
      return $ bseq $ IndexSeqMap $ \bi ->
        return $ VStream $ IndexSeqMap $ \ai ->
         do ys <- flip lookupSeqMap ai =<< fromSeq "transposeV" xs
            case ys of
              VStream ys' -> lookupSeqMap ys' bi
              VWord _ wv  -> VBit <$> (flip (indexWordValue sym) bi =<< wv)
              _ -> evalPanic "transpose" ["expected sequence of bits"]

  | otherwise = -- [a][b]c -> [b][a]c
      return $ bseq $ IndexSeqMap $ \bi ->
        return $ aseq $ IndexSeqMap $ \ai -> do
          ys  <- flip lookupSeqMap ai =<< fromSeq "transposeV 1" xs
          z   <- flip lookupSeqMap bi =<< fromSeq "transposeV 2" ys
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
  Nat' ->
  Nat' ->
  TValue ->
  (GenValue sym) ->
  (GenValue sym) ->
  SEval sym (GenValue sym)

ccatV sym _front _back _elty (VWord m l) (VWord n r) =
  return $ VWord (m+n) (join (joinWordVal sym <$> l <*> r))

ccatV sym _front _back _elty (VWord m l) (VStream r) = do
  l' <- sDelay sym Nothing l
  return $ VStream $ IndexSeqMap $ \i ->
    if i < m then
      VBit <$> (flip (indexWordValue sym) i =<< l')
    else
      lookupSeqMap r (i-m)

ccatV sym front back elty l r = do
       l'' <- sDelay sym Nothing (fromSeq "ccatV left" l)
       r'' <- sDelay sym Nothing (fromSeq "ccatV right" r)
       let Nat n = front
       mkSeq (evalTF TCAdd [front,back]) elty <$> return (IndexSeqMap $ \i ->
        if i < n then do
         ls <- l''
         lookupSeqMap ls i
        else do
         rs <- r''
         lookupSeqMap rs (i-n))

{-# INLINE wordValLogicOp #-}

wordValLogicOp ::
  Backend sym =>
  sym ->
  (SBit sym -> SBit sym -> SEval sym (SBit sym)) ->
  (SWord sym -> SWord sym -> SEval sym (SWord sym)) ->
  WordValue sym ->
  WordValue sym ->
  SEval sym (WordValue sym)
wordValLogicOp _sym _ wop (WordVal w1) (WordVal w2) = WordVal <$> wop w1 w2

wordValLogicOp sym bop _ w1 w2 = LargeBitsVal (wordValueSize sym w1) <$> zs
     where zs = memoMap $ IndexSeqMap $ \i -> join (op <$> (lookupSeqMap xs i) <*> (lookupSeqMap ys i))
           xs = asBitsMap sym w1
           ys = asBitsMap sym w2
           op x y = VBit <$> (bop (fromVBit x) (fromVBit y))

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
              -> do v <- sDelay sym Nothing $ join
                            (wordValLogicOp sym opb opw <$>
                                    fromWordVal "logicBinary l" l <*>
                                    fromWordVal "logicBinary r" r)
                    return $ VWord w v

         -- finite sequences
         | otherwise -> VSeq w <$>
                           (join (zipSeqMap (loop aty) <$>
                                    (fromSeq "logicBinary left" l)
                                    <*> (fromSeq "logicBinary right" r)))

    TVStream aty ->
        VStream <$> (join (zipSeqMap (loop aty) <$>
                          (fromSeq "logicBinary left" l) <*>
                          (fromSeq "logicBinary right" r)))

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

{-# INLINE wordValUnaryOp #-}
wordValUnaryOp ::
  Backend sym =>
  (SBit sym -> SEval sym (SBit sym)) ->
  (SWord sym -> SEval sym (SWord sym)) ->
  WordValue sym ->
  SEval sym (WordValue sym)
wordValUnaryOp _ wop (WordVal w)  = WordVal <$> (wop w)
wordValUnaryOp bop _ (LargeBitsVal n xs) = LargeBitsVal n <$> mapSeqMap f xs
  where f x = VBit <$> (bop (fromVBit x))

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
              -> do v <- sDelay sym Nothing (wordValUnaryOp opb opw =<< fromWordVal "logicUnary" val)
                    return $ VWord w v

         -- finite sequences
         | otherwise
              -> VSeq w <$> (mapSeqMap (loop ety) =<< fromSeq "logicUnary" val)

         -- streams
    TVStream ety ->
         VStream <$> (mapSeqMap (loop ety) =<< fromSeq "logicUnary" val)

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
assertIndexInBounds sym (Nat n) (Right idx)
  | n >= 2^(wordValueSize sym idx)
  = return ()

-- If the index is concrete, test it directly
assertIndexInBounds sym (Nat n) (Right (WordVal idx))
  | Just (_w,i) <- wordAsLit sym idx
  = unless (i < n) (raiseError sym (InvalidIndex (Just i)))

-- If the index is a packed word, test that it
-- is less than the concrete value of n, which
-- fits into w bits because of the above test.
assertIndexInBounds sym (Nat n) (Right (WordVal idx)) =
  do n' <- wordLit sym (wordLen sym idx) n
     p <- wordLessThan sym idx n'
     assertSideCondition sym p (InvalidIndex Nothing)

-- If the index is an unpacked word, force all the bits
-- and compute the unsigned less-than test directly.
assertIndexInBounds sym (Nat n) (Right (LargeBitsVal w bits)) =
  do bitsList <- traverse (fromVBit <$>) (enumerateSeqMap w bits)
     p <- bitsValueLessThan sym w bitsList n
     assertSideCondition sym p (InvalidIndex Nothing)


-- | Indexing operations.

{-# INLINE indexPrim #-}
indexPrim ::
  Backend sym =>
  sym ->
  (Nat' -> TValue -> SeqMap sym -> TValue -> SInteger sym -> SEval sym (GenValue sym)) ->
  (Nat' -> TValue -> SeqMap sym -> TValue -> [SBit sym] -> SEval sym (GenValue sym)) ->
  (Nat' -> TValue -> SeqMap sym -> TValue -> SWord sym -> SEval sym (GenValue sym)) ->
  GenValue sym
indexPrim sym int_op bits_op word_op =
  nlam $ \ len  ->
  tlam $ \ eltTy ->
  tlam $ \ ix ->
   lam $ \ xs  -> return $
   lam $ \ idx  -> do
      vs <- xs >>= \case
               VWord _ w  -> w >>= \w' -> return $ IndexSeqMap (\i -> VBit <$> indexWordValue sym w' i)
               VSeq _ vs  -> return vs
               VStream vs -> return vs
               _ -> evalPanic "Expected sequence value" ["indexPrim"]
      idx' <- asIndex sym "index" ix =<< idx
      assertIndexInBounds sym len idx'
      case idx' of
        Left i                    -> int_op len eltTy vs ix i
        Right (WordVal w')        -> word_op len eltTy vs ix w'
        Right (LargeBitsVal m bs) -> bits_op len eltTy vs ix =<< traverse (fromVBit <$>) (enumerateSeqMap m bs)

{-# INLINE updatePrim #-}

updatePrim ::
  Backend sym =>
  sym ->
  (Nat' -> TValue -> WordValue sym -> Either (SInteger sym) (WordValue sym) -> SEval sym (GenValue sym) -> SEval sym (WordValue sym)) ->
  (Nat' -> TValue -> SeqMap sym    -> Either (SInteger sym) (WordValue sym) -> SEval sym (GenValue sym) -> SEval sym (SeqMap sym)) ->
  GenValue sym
updatePrim sym updateWord updateSeq =
  nlam $ \len ->
  tlam $ \eltTy ->
  tlam $ \ix ->
  lam $ \xs  -> return $
  lam $ \idx -> return $
  lam $ \val -> do
    idx' <- asIndex sym "update" ix =<< idx
    assertIndexInBounds sym len idx'
    xs >>= \case
      VWord l w  -> do w' <- sDelay sym Nothing w
                       return $ VWord l (w' >>= \w'' -> updateWord len eltTy w'' idx' val)
      VSeq l vs  -> VSeq l  <$> updateSeq len eltTy vs idx' val
      VStream vs -> VStream <$> updateSeq len eltTy vs idx' val
      _ -> evalPanic "Expected sequence value" ["updatePrim"]

{-# INLINE fromToV #-}

-- @[ 0 .. 10 ]@
fromToV :: Backend sym => sym -> GenValue sym
fromToV sym =
  nlam $ \ first ->
  nlam $ \ lst   ->
  tlam $ \ ty    ->
    let !f = mkLit sym ty in
    case (first, lst) of
      (Nat first', Nat lst') ->
        let len = 1 + (lst' - first')
        in VSeq len $ IndexSeqMap $ \i -> f (first' + i)
      _ -> evalPanic "fromToV" ["invalid arguments"]

{-# INLINE fromThenToV #-}

-- @[ 0, 1 .. 10 ]@
fromThenToV :: Backend sym => sym -> GenValue sym
fromThenToV sym =
  nlam $ \ first ->
  nlam $ \ next  ->
  nlam $ \ lst   ->
  tlam $ \ ty    ->
  nlam $ \ len   ->
    let !f = mkLit sym ty in
    case (first, next, lst, len) of
      (Nat first', Nat next', Nat _lst', Nat len') ->
        let diff = next' - first'
        in VSeq len' $ IndexSeqMap $ \i -> f (first' + i*diff)
      _ -> evalPanic "fromThenToV" ["invalid arguments"]

{-# INLINE infFromV #-}
infFromV :: Backend sym => sym -> GenValue sym
infFromV sym =
  tlam $ \ ty ->
  lam  $ \ x ->
  do mx <- sDelay sym Nothing x
     return $ VStream $ IndexSeqMap $ \i ->
       do x' <- mx
          i' <- integerLit sym i
          addV sym ty x' =<< intV sym i' ty

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
     return $ VStream $ IndexSeqMap $ \i -> do
       (x,d) <- mxd
       i' <- integerLit sym i
       addV sym ty x =<< mulV sym ty d =<< intV sym i' ty

-- Shifting ---------------------------------------------------

barrelShifter :: Backend sym =>
  sym ->
  (SeqMap sym -> Integer -> SEval sym (SeqMap sym))
     {- ^ concrete shifting operation -} ->
  SeqMap sym  {- ^ initial value -} ->
  [SBit sym]  {- ^ bits of shift amount, in big-endian order -} ->
  SEval sym (SeqMap sym)
barrelShifter sym shift_op = go
  where
  go x [] = return x

  go x (b:bs)
    | Just True <- bitAsLit sym b
    = do x_shft <- shift_op x (2 ^ length bs)
         go x_shft bs

    | Just False <- bitAsLit sym b
    = do go x bs

    | otherwise
    = do x_shft <- shift_op x (2 ^ length bs)
         x' <- memoMap (mergeSeqMap sym b x_shft x)
         go x' bs

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
  TValue ->
  SInteger sym ->
  SEval sym [SBit sym]
enumerateIntBits sym (Nat n) _ idx = enumerateIntBits' sym n idx
enumerateIntBits _sym Inf _ _ = liftIO (X.throw (UnsupportedSymbolicOp "unbounded integer shifting"))

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
  GenValue sym
logicShift sym nm shrinkRange wopPos wopNeg reindexPos reindexNeg =
  nlam $ \m ->
  tlam $ \ix ->
  tlam $ \a ->
  VFun $ \xs -> return $
  VFun $ \y ->
    do xs' <- xs
       y' <- asIndex sym "shift" ix =<< y
       case y' of
         Left int_idx ->
           do pneg <- intLessThan sym int_idx =<< integerLit sym 0
              iteValue sym pneg
                (intShifter sym nm wopNeg reindexNeg m ix a xs' =<< shrinkRange sym m ix =<< intNegate sym int_idx)
                (intShifter sym nm wopPos reindexPos m ix a xs' =<< shrinkRange sym m ix int_idx)
         Right idx ->
           wordShifter sym nm wopPos reindexPos m a xs' idx

intShifter :: Backend sym =>
   sym ->
   String ->
   (SWord sym -> SWord sym -> SEval sym (SWord sym)) ->
   (Nat' -> Integer -> Integer -> Maybe Integer) ->
   Nat' ->
   TValue ->
   TValue ->
   GenValue sym ->
   SInteger sym ->
   SEval sym (GenValue sym)
intShifter sym nm wop reindex m ix a xs idx =
   do let shiftOp vs shft =
              memoMap $ IndexSeqMap $ \i ->
                case reindex m i shft of
                  Nothing -> zeroV sym a
                  Just i' -> lookupSeqMap vs i'
      case xs of
        VWord w x ->
           return $ VWord w $ do
             x >>= \case
               WordVal x' -> WordVal <$> (wop x' =<< wordFromInt sym w idx)
               LargeBitsVal n bs0 ->
                 do idx_bits <- enumerateIntBits sym m ix idx
                    LargeBitsVal n <$> barrelShifter sym shiftOp bs0 idx_bits

        VSeq w vs0 ->
           do idx_bits <- enumerateIntBits sym m ix idx
              VSeq w <$> barrelShifter sym shiftOp vs0 idx_bits

        VStream vs0 ->
           do idx_bits <- enumerateIntBits sym m ix idx
              VStream <$> barrelShifter sym shiftOp vs0 idx_bits

        _ -> evalPanic "expected sequence value in shift operation" [nm]


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
  let shiftOp vs shft =
          memoMap $ IndexSeqMap $ \i ->
            case reindex m i shft of
              Nothing -> zeroV sym a
              Just i' -> lookupSeqMap vs i'
   in case xs of
        VWord w x ->
           return $ VWord w $ do
             x >>= \case
               WordVal x' -> WordVal <$> (wop x' =<< asWordVal sym idx)
               LargeBitsVal n bs0 ->
                 do idx_bits <- enumerateWordValue sym idx
                    LargeBitsVal n <$> barrelShifter sym shiftOp bs0 idx_bits

        VSeq w vs0 ->
           do idx_bits <- enumerateWordValue sym idx
              VSeq w <$> barrelShifter sym shiftOp vs0 idx_bits

        VStream vs0 ->
           do idx_bits <- enumerateWordValue sym idx
              VStream <$> barrelShifter sym shiftOp vs0 idx_bits

        _ -> evalPanic "expected sequence value in shift operation" [nm]


shiftShrink :: Backend sym => sym -> Nat' -> TValue -> SInteger sym -> SEval sym (SInteger sym)
shiftShrink _sym Inf _ x = return x
shiftShrink sym (Nat w) _ x =
  do w' <- integerLit sym w
     p  <- intLessThan sym w' x
     iteInteger sym p w' x

rotateShrink :: Backend sym => sym -> Nat' -> TValue -> SInteger sym -> SEval sym (SInteger sym)
rotateShrink _sym Inf _ _ = panic "rotateShrink" ["expected finite sequence in rotate"]
rotateShrink sym (Nat 0) _ _ = integerLit sym 0
rotateShrink sym (Nat w) _ x =
  do w' <- integerLit sym w
     intMod sym x w'

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
errorV sym ty msg = case ty of
  -- bits
  TVBit -> cryUserError sym msg
  TVInteger -> cryUserError sym msg
  TVIntMod _ -> cryUserError sym msg
  TVRational -> cryUserError sym msg
  TVArray{} -> cryUserError sym msg
  TVFloat {} -> cryUserError sym msg

  -- sequences
  TVSeq w ety
     | isTBit ety -> return $ VWord w $ return $ LargeBitsVal w $ IndexSeqMap $ \_ -> cryUserError sym msg
     | otherwise  -> return $ VSeq w (IndexSeqMap $ \_ -> errorV sym ety msg)

  TVStream ety ->
    return $ VStream (IndexSeqMap $ \_ -> errorV sym ety msg)

  -- functions
  TVFun _ bty ->
    return $ lam (\ _ -> errorV sym bty msg)

  -- tuples
  TVTuple tys ->
    return $ VTuple (map (\t -> errorV sym t msg) tys)

  -- records
  TVRec fields ->
    return $ VRecord $ fmap (\t -> errorV sym t msg) $ fields

  TVAbstract {} -> cryUserError sym msg


{-# INLINE valueToChar #-}

-- | Expect a word value.  Mask it to an 8-bits ASCII value
--   and return the associated character, if it is concrete.
--   Otherwise, return a '?' character
valueToChar :: Backend sym => sym -> GenValue sym -> SEval sym Char
valueToChar sym (VWord 8 wval) =
  do w <- asWordVal sym =<< wval
     pure $! fromMaybe '?' (wordAsChar sym w)
valueToChar _ _ = evalPanic "valueToChar" ["Not an 8-bit bitvector"]

{-# INLINE valueToString #-}

valueToString :: Backend sym => sym -> GenValue sym -> SEval sym String
valueToString sym (VSeq n vals) = traverse (valueToChar sym =<<) (enumerateSeqMap n vals)
valueToString _ _ = evalPanic "valueToString" ["Not a finite sequence"]

-- Merge and if/then/else

{-# INLINE iteValue #-}
iteValue :: Backend sym =>
  sym ->
  SBit sym ->
  SEval sym (GenValue sym) ->
  SEval sym (GenValue sym) ->
  SEval sym (GenValue sym)
iteValue sym b x y
  | Just True  <- bitAsLit sym b = x
  | Just False <- bitAsLit sym b = y
  | otherwise = mergeValue' sym b x y

{-# INLINE mergeWord #-}
mergeWord :: Backend sym =>
  sym ->
  SBit sym ->
  WordValue sym ->
  WordValue sym ->
  SEval sym (WordValue sym)
mergeWord sym c (WordVal w1) (WordVal w2) =
  WordVal <$> iteWord sym c w1 w2
mergeWord sym c w1 w2 =
  LargeBitsVal (wordValueSize sym w1) <$> memoMap (mergeSeqMap sym c (asBitsMap sym w1) (asBitsMap sym w2))

{-# INLINE mergeWord' #-}
mergeWord' :: Backend sym =>
  sym ->
  SBit sym ->
  SEval sym (WordValue sym) ->
  SEval sym (WordValue sym) ->
  SEval sym (WordValue sym)
mergeWord' sym = mergeEval sym (mergeWord sym)

{-# INLINE mergeValue' #-}
mergeValue' :: Backend sym =>
  sym ->
  SBit sym ->
  SEval sym (GenValue sym) ->
  SEval sym (GenValue sym) ->
  SEval sym (GenValue sym)
mergeValue' sym = mergeEval sym (mergeValue sym)

mergeValue :: Backend sym =>
  sym ->
  SBit sym ->
  GenValue sym ->
  GenValue sym ->
  SEval sym (GenValue sym)
mergeValue sym c v1 v2 =
  case (v1, v2) of
    (VRecord fs1 , VRecord fs2 ) ->
      do let res = zipRecords (\_lbl -> mergeValue' sym c) fs1 fs2
         case res of
           Left f -> panic "Cryptol.Eval.Generic" [ "mergeValue: incompatible record values", show f ]
           Right r -> pure (VRecord r)
    (VTuple vs1  , VTuple vs2  ) | length vs1 == length vs2  ->
                                  pure $ VTuple $ zipWith (mergeValue' sym c) vs1 vs2
    (VBit b1     , VBit b2     ) -> VBit <$> iteBit sym c b1 b2
    (VInteger i1 , VInteger i2 ) -> VInteger <$> iteInteger sym c i1 i2
    (VRational q1, VRational q2) -> VRational <$> iteRational sym c q1 q2
    (VWord n1 w1 , VWord n2 w2 ) | n1 == n2 -> pure $ VWord n1 $ mergeWord' sym c w1 w2
    (VSeq n1 vs1 , VSeq n2 vs2 ) | n1 == n2 -> VSeq n1 <$> memoMap (mergeSeqMap sym c vs1 vs2)
    (VStream vs1 , VStream vs2 ) -> VStream <$> memoMap (mergeSeqMap sym c vs1 vs2)
    (VFun f1     , VFun f2     ) -> pure $ VFun $ \x -> mergeValue' sym c (f1 x) (f2 x)
    (VPoly f1    , VPoly f2    ) -> pure $ VPoly $ \x -> mergeValue' sym c (f1 x) (f2 x)
    (_           , _           ) -> panic "Cryptol.Eval.Generic"
                                  [ "mergeValue: incompatible values" ]

{-# INLINE mergeSeqMap #-}
mergeSeqMap :: Backend sym =>
  sym ->
  SBit sym ->
  SeqMap sym ->
  SeqMap sym ->
  SeqMap sym
mergeSeqMap sym c x y =
  IndexSeqMap $ \i ->
    iteValue sym c (lookupSeqMap x i) (lookupSeqMap y i)



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
  tlam $ \_b ->
  ilam $ \_n ->
  lam $ \f -> pure $
  lam $ \xs ->
    do f' <- fromVFun <$> f
       xs' <- xs
       case xs' of
          VWord n w ->
            do m <- asBitsMap sym <$> w
               m' <- sparkParMap sym f' n m
               pure (VWord n (pure (LargeBitsVal n m')))
          VSeq n m ->
            VSeq n <$> sparkParMap sym f' n m

          _ -> panic "parmapV" ["expected sequence!"]


sparkParMap ::
  Backend sym =>
  sym ->
  (SEval sym (GenValue sym) -> SEval sym (GenValue sym)) ->
  Integer ->
  SeqMap sym ->
  SEval sym (SeqMap sym)
sparkParMap sym f n m =
  finiteSeqMap sym <$> mapM (sSpark sym . g) (enumerateSeqMap n m)
 where
 g x =
   do z <- sDelay sym Nothing (f x)
      forceValue =<< z
      z

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
