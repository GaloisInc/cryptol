-- |
-- Module      :  Cryptol.Symbolic.Value
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Cryptol.Symbolic.Value
  ( SBV(..)
  , literalSWord
  , fromBitsLE
  , forallBV_, existsBV_
  , forallSBool_, existsSBool_
  , forallSInteger_, existsSInteger_
  , Value
  , TValue, isTBit, tvSeq
  , GenValue(..), lam, tlam, toStream, toFinSeq, toSeq
  , fromVBit, fromVFun, fromVPoly, fromVTuple, fromVRecord, lookupRecord
  , fromSeq, fromVWord
  , evalPanic
  , iteSValue, mergeValue, mergeWord, mergeBit, mergeBits, mergeSeqMap
  , mergeWord'
  )
  where

import Data.Bits (bit, complement)
import Data.List (foldl')
import qualified Data.Map as Map
import qualified Data.Sequence as Seq

import Data.SBV (symbolicEnv)
import Data.SBV.Dynamic

--import Cryptol.Eval.Monad
import Cryptol.Eval.Type   (TValue(..), isTBit, tvSeq)
import Cryptol.Eval.Monad  (Eval, ready)
import Cryptol.Eval.Value  ( GenValue(..), BitWord(..), lam, tlam, toStream,
                           toFinSeq, toSeq, WordValue(..),
                           fromSeq, fromVBit, fromVWord, fromVFun, fromVPoly,
                           fromVTuple, fromVRecord, lookupRecord, SeqMap(..),
                           ppBV, BV(..), integerToChar, lookupSeqMap, memoMap,
                           wordValueSize, asBitsMap)
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.PP

import Control.Monad.Trans  (liftIO)

-- SBool and SWord -------------------------------------------------------------

data SBV = SBV

fromBitsLE :: [SBit SBV] -> SWord SBV
fromBitsLE bs = foldl' f (literalSWord 0 0) bs
  where f w b = svJoin (svToWord1 b) w

literalSWord :: Int -> Integer -> SWord SBV
literalSWord w i = svInteger (KBounded False w) i

forallBV_ :: Int -> Symbolic (SWord SBV)
forallBV_ w = symbolicEnv >>= liftIO . svMkSymVar (Just ALL) (KBounded False w) Nothing

existsBV_ :: Int -> Symbolic (SWord SBV)
existsBV_ w = symbolicEnv >>= liftIO . svMkSymVar (Just EX) (KBounded False w) Nothing

forallSBool_ :: Symbolic (SBit SBV)
forallSBool_ = symbolicEnv >>= liftIO . svMkSymVar (Just ALL) KBool Nothing

existsSBool_ :: Symbolic (SBit SBV)
existsSBool_ = symbolicEnv >>= liftIO . svMkSymVar (Just EX) KBool Nothing

forallSInteger_ :: Symbolic (SBit SBV)
forallSInteger_ = symbolicEnv >>= liftIO . svMkSymVar (Just ALL) KUnbounded Nothing

existsSInteger_ :: Symbolic (SBit SBV)
existsSInteger_ = symbolicEnv >>= liftIO . svMkSymVar (Just EX) KUnbounded Nothing

-- Values ----------------------------------------------------------------------

type Value = GenValue SBV

-- Symbolic Conditionals -------------------------------------------------------

iteSValue :: SBit SBV -> Value -> Value -> Eval Value
iteSValue c x y =
  case svAsBool c of
    Just True  -> return x
    Just False -> return y
    Nothing    -> mergeValue True c x y

mergeBit :: Bool
         -> SBit SBV
         -> SBit SBV
         -> SBit SBV
         -> SBit SBV
mergeBit f c b1 b2 = svSymbolicMerge KBool f c b1 b2

mergeWord :: Bool
          -> SBit SBV
          -> WordValue SBV
          -> WordValue SBV
          -> WordValue SBV
mergeWord f c (WordVal w1) (WordVal w2) =
    WordVal $ svSymbolicMerge (kindOf w1) f c w1 w2
mergeWord f c (WordVal w1) (BitsVal ys) =
    BitsVal $ mergeBits f c (Seq.fromList $ map ready $ unpackSBV w1) ys
mergeWord f c (BitsVal xs) (WordVal w2) =
    BitsVal $ mergeBits f c xs (Seq.fromList $ map ready $ unpackSBV w2)
mergeWord f c (BitsVal xs) (BitsVal ys) =
    BitsVal $ mergeBits f c xs ys
mergeWord f c w1 w2 =
    LargeBitsVal (wordValueSize SBV w1) (mergeSeqMap f c (asBitsMap SBV w1) (asBitsMap SBV w2))

mergeWord' :: Bool
           -> SBit SBV
           -> Eval (WordValue SBV)
           -> Eval (WordValue SBV)
           -> Eval (WordValue SBV)
mergeWord' f c x y = mergeWord f c <$> x <*> y

mergeBits :: Bool
          -> SBit SBV
          -> Seq.Seq (Eval (SBit SBV))
          -> Seq.Seq (Eval (SBit SBV))
          -> Seq.Seq (Eval (SBit SBV))
mergeBits f c bs1 bs2 = Seq.zipWith mergeBit' bs1 bs2
 where mergeBit' b1 b2 = mergeBit f c <$> b1 <*> b2

mergeInteger :: Bool
             -> SBit SBV
             -> SInteger SBV
             -> SInteger SBV
             -> SInteger SBV
mergeInteger f c x y = svSymbolicMerge KUnbounded f c x y

mergeValue :: Bool -> SBit SBV -> Value -> Value -> Eval Value
mergeValue f c v1 v2 =
  case (v1, v2) of
    (VRecord fs1, VRecord fs2)  | Map.keys fs1 == Map.keys fs2 ->
                                  pure $ VRecord $ Map.intersectionWith (mergeValue' f c) fs1 fs2
    (VTuple vs1 , VTuple vs2 ) -> pure $ VTuple $ zipWith (mergeValue' f c) vs1 vs2
    (VBit b1    , VBit b2    ) -> pure $ VBit $ mergeBit f c b1 b2
    (VInteger i1, VInteger i2) -> pure $ VInteger $ mergeInteger f c i1 i2
    (VWord n1 w1, VWord n2 w2 ) | n1 == n2 -> pure $ VWord n1 $ mergeWord' f c w1 w2
    (VSeq n1 vs1, VSeq n2 vs2 ) | n1 == n2 -> VSeq n1 <$> memoMap (mergeSeqMap f c vs1 vs2)
    (VStream vs1, VStream vs2) -> VStream <$> memoMap (mergeSeqMap f c vs1 vs2)
    (VFun f1    , VFun f2    ) -> pure $ VFun $ \x -> mergeValue' f c (f1 x) (f2 x)
    (VPoly f1   , VPoly f2   ) -> pure $ VPoly $ \x -> mergeValue' f c (f1 x) (f2 x)
    (_          , _          ) -> panic "Cryptol.Symbolic.Value"
                                  [ "mergeValue: incompatible values" ]

mergeValue' :: Bool -> SBit SBV -> Eval Value -> Eval Value -> Eval Value
mergeValue' f c x1 x2 =
  do v1 <- x1
     v2 <- x2
     mergeValue f c v1 v2

mergeSeqMap :: Bool -> SBit SBV -> SeqMap SBV -> SeqMap SBV -> SeqMap SBV
mergeSeqMap f c x y =
  IndexSeqMap $ \i ->
  do xi <- lookupSeqMap x i
     yi <- lookupSeqMap y i
     mergeValue f c xi yi

packSBV :: [SBit SBV] -> SWord SBV
packSBV bs = fromBitsLE (reverse bs)

unpackSBV :: SWord SBV -> [SBit SBV]
unpackSBV x = [ svTestBit x i | i <- reverse [0 .. intSizeOf x - 1] ]


-- Symbolic Big-endian Words -------------------------------------------------------

instance BitWord SBV where
  type SBit SBV = SVal
  type SWord SBV = SVal
  type SInteger SBV = SVal

  wordLen _ v = toInteger (intSizeOf v)
  wordAsChar _ v = integerToChar <$> svAsInteger v

  ppBit _ v
     | Just b <- svAsBool v = text $! if b then "True" else "False"
     | otherwise            = text "?"
  ppWord _ opts v
     | Just x <- svAsInteger v = ppBV opts (BV (wordLen SBV v) x)
     | otherwise               = text "[?]"
  ppInteger _ _opts v
     | Just x <- svAsInteger v = integer x
     | otherwise               = text "[?]"

  bitLit _ b     = svBool b
  wordLit _ n x  = svInteger (KBounded False (fromInteger n)) x
  integerLit _ x = svInteger KUnbounded x

  wordBit _ x idx = svTestBit x (intSizeOf x - 1 - fromInteger idx)

  wordUpdate _ x idx b = svSymbolicMerge (kindOf x) False b wtrue wfalse
    where
     i' = intSizeOf x - 1 - fromInteger idx
     wtrue  = x `svOr`  svInteger (kindOf x) (bit i' :: Integer)
     wfalse = x `svAnd` svInteger (kindOf x) (complement (bit i' :: Integer))

  packWord _ bs  = packSBV bs
  unpackWord _ x = unpackSBV x

  joinWord _ x y = svJoin x y

  splitWord _ _leftW rightW w =
    ( svExtract (intSizeOf w - 1) (fromInteger rightW) w
    , svExtract (fromInteger rightW - 1) 0 w
    )

  extractWord _ len start w =
    svExtract (fromInteger start + fromInteger len - 1) (fromInteger start) w

  wordPlus  _ a b = svPlus a b
  wordMinus _ a b = svMinus a b
  wordMult  _ a b = svTimes a b

  intPlus  _ a b = svPlus a b
  intMinus _ a b = svMinus a b
  intMult  _ a b = svTimes a b

  intModPlus  _ _m a b = svPlus a b
  intModMinus _ _m a b = svMinus a b
  intModMult  _ _m a b = svTimes a b

  wordToInt _ x = svToInteger x
  wordFromInt _ w i = svFromInteger w i

-- TODO: implement this properly in SBV using "bv2int"
svToInteger :: SWord SBV -> SInteger SBV
svToInteger w =
  case svAsInteger w of
    Nothing -> svFromIntegral KUnbounded w
    Just x  -> svInteger KUnbounded x

-- TODO: implement this properly in SBV using "int2bv"
svFromInteger :: Integer -> SInteger SBV -> SWord SBV
svFromInteger 0 _ = literalSWord 0 0
svFromInteger n i =
  case svAsInteger i of
    Nothing -> svFromIntegral (KBounded False (fromInteger n)) i
    Just x  -> literalSWord (fromInteger n) x

-- Errors ----------------------------------------------------------------------

evalPanic :: String -> [String] -> a
evalPanic cxt = panic ("[Symbolic]" ++ cxt)
