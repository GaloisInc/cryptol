-- |
-- Module      :  Cryptol.Eval.What4
-- Copyright   :  (c) 2020 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com

{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
module Cryptol.Eval.What4
  ( Value
  , primTable
  , floatPrims
  ) where

import qualified Control.Exception as X
import           Control.Monad (join)
import           Control.Monad.IO.Class
import           Data.Bits
import qualified Data.Map as Map
import           Data.Map (Map)

import qualified What4.Interface as W4
import qualified What4.SWord as SW
import qualified What4.Utils.AbstractDomains as W4

import Cryptol.Backend
import Cryptol.Backend.Monad ( EvalError(..), Unsupported(..) )
import Cryptol.Backend.What4
import qualified Cryptol.Backend.What4.SFloat as W4

import Cryptol.Eval.Generic
import Cryptol.Eval.Type (finNat', TValue(..))
import Cryptol.Eval.Value

import Cryptol.TypeCheck.Solver.InfNat( Nat'(..), widthInteger )
import Cryptol.Utils.Ident


type Value sym = GenValue (What4 sym)

-- See also Cryptol.Prims.Eval.primTable
primTable :: W4.IsSymExprBuilder sym => What4 sym -> Map.Map PrimIdent (Value sym)
primTable sym@(What4 w4sym _) =
  Map.union (floatPrims sym) $
  Map.fromList $ map (\(n, v) -> (prelPrim n, v))

  [ -- Literals
    ("True"        , VBit (bitLit sym True))
  , ("False"       , VBit (bitLit sym False))
  , ("number"      , ecNumberV sym) -- Converts a numeric type into its corresponding value.
                                    -- { val, rep } (Literal val rep) => rep
  , ("fraction"    , ecFractionV sym)
  , ("ratio"       , ratioV sym)

    -- Zero
  , ("zero"        , VPoly (zeroV sym))

    -- Logic
  , ("&&"          , binary (andV sym))
  , ("||"          , binary (orV sym))
  , ("^"           , binary (xorV sym))
  , ("complement"  , unary  (complementV sym))

    -- Ring
  , ("fromInteger" , fromIntegerV sym)
  , ("+"           , binary (addV sym))
  , ("-"           , binary (subV sym))
  , ("negate"      , unary (negateV sym))
  , ("*"           , binary (mulV sym))

    -- Integral
  , ("toInteger"   , toIntegerV sym)
  , ("/"           , binary (divV sym))
  , ("%"           , binary (modV sym))
  , ("^^"          , expV sym)
  , ("infFrom"     , infFromV sym)
  , ("infFromThen" , infFromThenV sym)

    -- Field
  , ("recip"       , recipV sym)
  , ("/."          , fieldDivideV sym)

    -- Round
  , ("floor"       , unary (floorV sym))
  , ("ceiling"     , unary (ceilingV sym))
  , ("trunc"       , unary (truncV sym))
  , ("roundAway"   , unary (roundAwayV sym))
  , ("roundToEven" , unary (roundToEvenV sym))

    -- Word operations
  , ("/$"          , sdivV sym)
  , ("%$"          , smodV sym)
  , ("lg2"         , lg2V sym)
  , (">>$"         , sshrV sym)

    -- Cmp
  , ("<"           , binary (lessThanV sym))
  , (">"           , binary (greaterThanV sym))
  , ("<="          , binary (lessThanEqV sym))
  , (">="          , binary (greaterThanEqV sym))
  , ("=="          , binary (eqV sym))
  , ("!="          , binary (distinctV sym))

    -- SignedCmp
  , ("<$"          , binary (signedLessThanV sym))

    -- Finite enumerations
  , ("fromTo"      , fromToV sym)
  , ("fromThenTo"  , fromThenToV sym)

    -- Sequence manipulations
  , ("#"          , -- {a,b,d} (fin a) => [a] d -> [b] d -> [a + b] d
     nlam $ \ front ->
     nlam $ \ back  ->
     tlam $ \ elty  ->
     lam  $ \ l     -> return $
     lam  $ \ r     -> join (ccatV sym front back elty <$> l <*> r))

  , ("join"       ,
     nlam $ \ parts ->
     nlam $ \ (finNat' -> each)  ->
     tlam $ \ a     ->
     lam  $ \ x     ->
       joinV sym parts each a =<< x)

  , ("split"       , ecSplitV sym)

  , ("splitAt"    ,
     nlam $ \ front ->
     nlam $ \ back  ->
     tlam $ \ a     ->
     lam  $ \ x     ->
       splitAtV sym front back a =<< x)

  , ("reverse"    , nlam $ \_a ->
                    tlam $ \_b ->
                     lam $ \xs -> reverseV sym =<< xs)

  , ("transpose"  , nlam $ \a ->
                    nlam $ \b ->
                    tlam $ \c ->
                     lam $ \xs -> transposeV sym a b c =<< xs)

    -- Shifts and rotates
  , ("<<"          , logicShift sym "<<"  shiftShrink
                        (w4bvShl w4sym) (w4bvLshr w4sym)
                        shiftLeftReindex shiftRightReindex)
  , (">>"          , logicShift sym ">>"  shiftShrink
                        (w4bvLshr w4sym) (w4bvShl w4sym)
                        shiftRightReindex shiftLeftReindex)
  , ("<<<"         , logicShift sym "<<<" rotateShrink
                        (w4bvRol w4sym) (w4bvRor w4sym)
                        rotateLeftReindex rotateRightReindex)
  , (">>>"         , logicShift sym ">>>" rotateShrink
                        (w4bvRor w4sym) (w4bvRol w4sym)
                        rotateRightReindex rotateLeftReindex)

    -- Indexing and updates
  , ("@"           , indexPrim sym (indexFront_int sym) (indexFront_bits sym) (indexFront_word sym))
  , ("!"           , indexPrim sym (indexBack_int sym) (indexBack_bits sym) (indexBack_word sym))

  , ("update"      , updatePrim sym (updateFrontSym_word sym) (updateFrontSym sym))
  , ("updateEnd"   , updatePrim sym (updateBackSym_word sym)  (updateBackSym sym))

    -- Misc

  , ("foldl"       , foldlV sym)
  , ("foldl'"      , foldl'V sym)

  , ("deepseq"     ,
      tlam $ \_a ->
      tlam $ \_b ->
       lam $ \x -> pure $
       lam $ \y ->
         do _ <- forceValue =<< x
            y)

  , ("parmap"      , parmapV sym)

  , ("fromZ"       , fromZV sym)

    -- {at,len} (fin len) => [len][8] -> at
  , ("error"       ,
      tlam $ \a ->
      nlam $ \_ ->
      VFun $ \s -> errorV sym a =<< (valueToString sym =<< s))

  , ("random"      ,
      tlam $ \a ->
      wlam sym $ \x ->
         case wordAsLit sym x of
           Just (_,i)  -> randomV sym a i
           Nothing -> cryUserError sym "cannot evaluate 'random' with symbolic inputs")

     -- The trace function simply forces its first two
     -- values before returing the third in the symbolic
     -- evaluator.
  , ("trace",
      nlam $ \_n ->
      tlam $ \_a ->
      tlam $ \_b ->
       lam $ \s -> return $
       lam $ \x -> return $
       lam $ \y -> do
         _ <- s
         _ <- x
         y)
  ]

sshrV :: W4.IsSymExprBuilder sym => What4 sym -> Value sym
sshrV sym =
  nlam $ \(Nat n) ->
  tlam $ \ix ->
  wlam sym $ \x -> return $
  lam $ \y ->
    y >>= asIndex sym ">>$" ix >>= \case
       Left i ->
         do pneg <- intLessThan sym i =<< integerLit sym 0
            zneg <- do i' <- shiftShrink sym (Nat n) ix =<< intNegate sym i
                       amt <- wordFromInt sym n i'
                       w4bvShl (w4 sym) x amt
            zpos <- do i' <- shiftShrink sym (Nat n) ix i
                       amt <- wordFromInt sym n i'
                       w4bvAshr (w4 sym) x amt
            return (VWord (SW.bvWidth x) (WordVal <$> iteWord sym pneg zneg zpos))

       Right wv ->
         do amt <- asWordVal sym wv
            return (VWord (SW.bvWidth x) (WordVal <$> w4bvAshr (w4 sym) x amt))

indexFront_int ::
  W4.IsSymExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  SeqMap (What4 sym) ->
  TValue ->
  SInteger (What4 sym) ->
  SEval (What4 sym) (Value sym)
indexFront_int sym@(What4 w4sym _) mblen _a xs ix idx
  | Just i <- W4.asInteger idx
  = lookupSeqMap xs i

  | (lo, Just hi) <- bounds
  = foldr f def [lo .. hi]

  | otherwise
  = liftIO (X.throw (UnsupportedSymbolicOp "unbounded integer indexing"))

 where
    def = raiseError sym (InvalidIndex Nothing)

    f n y =
       do p <- liftIO (W4.intEq w4sym idx =<< W4.intLit w4sym n)
          iteValue sym p (lookupSeqMap xs n) y

    bounds =
      (case W4.rangeLowBound (W4.integerBounds idx) of
        W4.Inclusive l -> max l 0
        _ -> 0
      , case (maxIdx, W4.rangeHiBound (W4.integerBounds idx)) of
          (Just n, W4.Inclusive h) -> Just (min n h)
          (Just n, _)              -> Just n
          _                        -> Nothing
      )

    -- Maximum possible in-bounds index given `Z m`
    -- type information and the length
    -- of the sequence. If the sequences is infinite and the
    -- integer is unbounded, there isn't much we can do.
    maxIdx =
      case (mblen, ix) of
        (Nat n, TVIntMod m)  -> Just (min (toInteger n) (toInteger m))
        (Nat n, _)           -> Just n
        (_    , TVIntMod m)  -> Just m
        _                    -> Nothing

indexBack_int ::
  W4.IsSymExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  SeqMap (What4 sym) ->
  TValue ->
  SInteger (What4 sym) ->
  SEval (What4 sym) (Value sym)
indexBack_int sym (Nat n) a xs ix idx = indexFront_int sym (Nat n) a (reverseSeqMap n xs) ix idx
indexBack_int _ Inf _ _ _ _ = evalPanic "Expected finite sequence" ["indexBack_int"]

indexFront_word ::
  W4.IsSymExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  SeqMap (What4 sym) ->
  TValue ->
  SWord (What4 sym) ->
  SEval (What4 sym) (Value sym)
indexFront_word sym@(What4 w4sym _) mblen _a xs _ix idx
  | Just i <- SW.bvAsUnsignedInteger idx
  = lookupSeqMap xs i

  | otherwise
  = foldr f def idxs

 where
    w = SW.bvWidth idx
    def = raiseError sym (InvalidIndex Nothing)

    f n y =
       do p <- liftIO (SW.bvEq w4sym idx =<< SW.bvLit w4sym w n)
          iteValue sym p (lookupSeqMap xs n) y

    -- maximum possible in-bounds index given the bitwidth
    -- of the index value and the length of the sequence
    maxIdx =
      case mblen of
        Nat n | n < 2^w -> n-1
        _ -> 2^w - 1

    -- concrete indices to consider, intersection of the
    -- range of values the index value might take with
    -- the legal values
    idxs =
      case SW.unsignedBVBounds idx of
        Just (lo, hi) -> [lo .. min hi maxIdx]
        _ -> [0 .. maxIdx]

indexBack_word ::
  W4.IsSymExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  SeqMap (What4 sym) ->
  TValue ->
  SWord (What4 sym) ->
  SEval (What4 sym) (Value sym)
indexBack_word sym (Nat n) a xs ix idx = indexFront_word sym (Nat n) a (reverseSeqMap n xs) ix idx
indexBack_word _ Inf _ _ _ _ = evalPanic "Expected finite sequence" ["indexBack_word"]

indexFront_bits :: forall sym.
  W4.IsSymExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  SeqMap (What4 sym) ->
  TValue ->
  [SBit (What4 sym)] ->
  SEval (What4 sym) (Value sym)
indexFront_bits sym mblen _a xs _ix bits0 = go 0 (length bits0) bits0
 where
  go :: Integer -> Int -> [W4.Pred sym] -> W4Eval sym (Value sym)
  go i _k []
    -- For indices out of range, fail
    | Nat n <- mblen
    , i >= n
    = raiseError sym (InvalidIndex (Just i))

    | otherwise
    = lookupSeqMap xs i

  go i k (b:bs)
    -- Fail early when all possible indices we could compute from here
    -- are out of bounds
    | Nat n <- mblen
    , (i `shiftL` k) >= n
    = raiseError sym (InvalidIndex Nothing)

    | otherwise
    = iteValue sym b
         (go ((i `shiftL` 1) + 1) (k-1) bs)
         (go  (i `shiftL` 1)      (k-1) bs)

indexBack_bits ::
  W4.IsSymExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  SeqMap (What4 sym) ->
  TValue ->
  [SBit (What4 sym)] ->
  SEval (What4 sym) (Value sym)
indexBack_bits sym (Nat n) a xs ix idx = indexFront_bits sym (Nat n) a (reverseSeqMap n xs) ix idx
indexBack_bits _ Inf _ _ _ _ = evalPanic "Expected finite sequence" ["indexBack_bits"]


-- | Compare a symbolic word value with a concrete integer.
wordValueEqualsInteger :: forall sym.
  W4.IsSymExprBuilder sym =>
  What4 sym ->
  WordValue (What4 sym) ->
  Integer ->
  W4Eval sym (W4.Pred sym)
wordValueEqualsInteger sym@(What4 w4sym _) wv i
  | wordValueSize sym wv < widthInteger i = return (W4.falsePred w4sym)
  | otherwise =
    case wv of
      WordVal w -> liftIO (SW.bvEq w4sym w =<< SW.bvLit w4sym (SW.bvWidth w) i)
      _ -> liftIO . bitsAre i =<< enumerateWordValueRev sym wv -- little-endian
  where
    bitsAre :: Integer -> [W4.Pred sym] -> IO (W4.Pred sym)
    bitsAre n [] = pure (W4.backendPred w4sym (n == 0))
    bitsAre n (b : bs) =
      do pb  <- bitIs (testBit n 0) b
         pbs <- bitsAre (n `shiftR` 1) bs
         W4.andPred w4sym pb pbs

    bitIs :: Bool -> W4.Pred sym -> IO (W4.Pred sym)
    bitIs b x = if b then pure x else W4.notPred w4sym x

updateFrontSym ::
  W4.IsSymExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  SeqMap (What4 sym) ->
  Either (SInteger (What4 sym)) (WordValue (What4 sym)) ->
  SEval (What4 sym) (Value sym) ->
  SEval (What4 sym) (SeqMap (What4 sym))
updateFrontSym sym _len _eltTy vs (Left idx) val =
  case W4.asInteger idx of
    Just i -> return $ updateSeqMap vs i val
    Nothing -> return $ IndexSeqMap $ \i ->
      do b <- intEq sym idx =<< integerLit sym i
         iteValue sym b val (lookupSeqMap vs i)

updateFrontSym sym _len _eltTy vs (Right wv) val =
  case wv of
    WordVal w | Just j <- SW.bvAsUnsignedInteger w ->
      return $ updateSeqMap vs j val
    _ ->
      memoMap $ IndexSeqMap $ \i ->
      do b <- wordValueEqualsInteger sym wv i
         iteValue sym b val (lookupSeqMap vs i)

updateBackSym ::
  W4.IsSymExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  SeqMap (What4 sym) ->
  Either (SInteger (What4 sym)) (WordValue (What4 sym)) ->
  SEval (What4 sym) (Value sym) ->
  SEval (What4 sym) (SeqMap (What4 sym))
updateBackSym _ Inf _ _ _ _ = evalPanic "Expected finite sequence" ["updateBackSym"]

updateBackSym sym (Nat n) _eltTy vs (Left idx) val =
  case W4.asInteger idx of
    Just i -> return $ updateSeqMap vs (n - 1 - i) val
    Nothing -> return $ IndexSeqMap $ \i ->
      do b <- intEq sym idx =<< integerLit sym (n - 1 - i)
         iteValue sym b val (lookupSeqMap vs i)

updateBackSym sym (Nat n) _eltTy vs (Right wv) val =
  case wv of
    WordVal w | Just j <- SW.bvAsUnsignedInteger w ->
      return $ updateSeqMap vs (n - 1 - j) val
    _ ->
      memoMap $ IndexSeqMap $ \i ->
      do b <- wordValueEqualsInteger sym wv (n - 1 - i)
         iteValue sym b val (lookupSeqMap vs i)


updateFrontSym_word ::
  W4.IsSymExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  WordValue (What4 sym) ->
  Either (SInteger (What4 sym)) (WordValue (What4 sym)) ->
  SEval (What4 sym) (GenValue (What4 sym)) ->
  SEval (What4 sym) (WordValue (What4 sym))
updateFrontSym_word _ Inf _ _ _ _ = evalPanic "Expected finite sequence" ["updateFrontSym_word"]

updateFrontSym_word sym (Nat _) eltTy (LargeBitsVal n bv) idx val =
  LargeBitsVal n <$> updateFrontSym sym (Nat n) eltTy bv idx val

updateFrontSym_word sym (Nat n) eltTy (WordVal bv) (Left idx) val =
  do idx' <- wordFromInt sym n idx
     updateFrontSym_word sym (Nat n) eltTy (WordVal bv) (Right (WordVal idx')) val

updateFrontSym_word sym@(What4 w4sym _) (Nat n) eltTy bv (Right wv) val =
  case wv of
    WordVal idx
      | Just j <- SW.bvAsUnsignedInteger idx ->
          updateWordValue sym bv j (fromVBit <$> val)

      | WordVal bw <- bv ->
        WordVal <$>
          do b <- fromVBit <$> val
             let sz = SW.bvWidth bw
             highbit <- liftIO (SW.bvLit w4sym sz (bit (fromInteger (sz-1))))
             msk <- w4bvLshr w4sym highbit idx
             liftIO $
               case W4.asConstantPred b of
                 Just True  -> SW.bvOr  w4sym bw msk
                 Just False -> SW.bvAnd w4sym bw =<< SW.bvNot w4sym msk
                 Nothing ->
                   do q <- SW.bvFill w4sym sz b
                      bw' <- SW.bvAnd w4sym bw =<< SW.bvNot w4sym msk
                      SW.bvXor w4sym bw' =<< SW.bvAnd w4sym q msk

    _ -> LargeBitsVal (wordValueSize sym wv) <$>
           updateFrontSym sym (Nat n) eltTy (asBitsMap sym bv) (Right wv) val


updateBackSym_word ::
  W4.IsSymExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  WordValue (What4 sym) ->
  Either (SInteger (What4 sym)) (WordValue (What4 sym)) ->
  SEval (What4 sym) (GenValue (What4 sym)) ->
  SEval (What4 sym) (WordValue (What4 sym))
updateBackSym_word _ Inf _ _ _ _ = evalPanic "Expected finite sequence" ["updateBackSym_word"]

updateBackSym_word sym (Nat _) eltTy (LargeBitsVal n bv) idx val =
  LargeBitsVal n <$> updateBackSym sym (Nat n) eltTy bv idx val

updateBackSym_word sym (Nat n) eltTy (WordVal bv) (Left idx) val =
  do idx' <- wordFromInt sym n idx
     updateBackSym_word sym (Nat n) eltTy (WordVal bv) (Right (WordVal idx')) val

updateBackSym_word sym@(What4 w4sym _) (Nat n) eltTy bv (Right wv) val =
  case wv of
    WordVal idx
      | Just j <- SW.bvAsUnsignedInteger idx ->
          updateWordValue sym bv (n - 1 - j) (fromVBit <$> val)

      | WordVal bw <- bv ->
        WordVal <$>
          do b <- fromVBit <$> val
             let sz = SW.bvWidth bw
             lowbit <- liftIO (SW.bvLit w4sym sz 1)
             msk <- w4bvShl w4sym lowbit idx
             liftIO $
               case W4.asConstantPred b of
                 Just True  -> SW.bvOr  w4sym bw msk
                 Just False -> SW.bvAnd w4sym bw =<< SW.bvNot w4sym msk
                 Nothing ->
                   do q <- SW.bvFill w4sym sz b
                      bw' <- SW.bvAnd w4sym bw =<< SW.bvNot w4sym msk
                      SW.bvXor w4sym bw' =<< SW.bvAnd w4sym q msk

    _ -> LargeBitsVal (wordValueSize sym wv) <$>
           updateBackSym sym (Nat n) eltTy (asBitsMap sym bv) (Right wv) val




-- | Table of floating point primitives
floatPrims :: W4.IsSymExprBuilder sym => What4 sym -> Map PrimIdent (Value sym)
floatPrims sym@(What4 w4sym _) =
  Map.fromList [ (floatPrim i,v) | (i,v) <- nonInfixTable ]
  where
  (~>) = (,)

  nonInfixTable =
    [ "fpNaN"       ~> fpConst (W4.fpNaN w4sym)
    , "fpPosInf"    ~> fpConst (W4.fpPosInf w4sym)
    , "fpFromBits"  ~> ilam \e -> ilam \p -> wlam sym \w ->
                       VFloat <$> liftIO (W4.fpFromBinary w4sym e p w)
    , "fpToBits"    ~> ilam \e -> ilam \p -> flam \x ->
                       pure $ VWord (e+p)
                            $ WordVal <$> liftIO (W4.fpToBinary w4sym x)
    , "=.="         ~> ilam \_ -> ilam \_ -> flam \x -> pure $ flam \y ->
                       VBit <$> liftIO (W4.fpEq w4sym x y)
    , "fpIsFinite"  ~> ilam \_ -> ilam \_ -> flam \x ->
                       VBit <$> liftIO do inf <- W4.fpIsInf w4sym x
                                          nan <- W4.fpIsNaN w4sym x
                                          weird <- W4.orPred w4sym inf nan
                                          W4.notPred w4sym weird

    , "fpAdd"       ~> fpBinArithV sym fpPlus
    , "fpSub"       ~> fpBinArithV sym fpMinus
    , "fpMul"       ~> fpBinArithV sym fpMult
    , "fpDiv"       ~> fpBinArithV sym fpDiv

    , "fpFromRational" ~>
       ilam \e -> ilam \p -> wlam sym \r -> pure $ lam \x ->
       do rat <- fromVRational <$> x
          VFloat <$> fpCvtFromRational sym e p r rat

    , "fpToRational" ~>
       ilam \_e -> ilam \_p -> flam \fp ->
       VRational <$> fpCvtToRational sym fp
    ]



-- | A helper for definitng floating point constants.
fpConst ::
  W4.IsSymExprBuilder sym =>
  (Integer -> Integer -> IO (W4.SFloat sym)) ->
  Value sym
fpConst mk =
     ilam \ e ->
 VNumPoly \ ~(Nat p) ->
 VFloat <$> liftIO (mk e p)
