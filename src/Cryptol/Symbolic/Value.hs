-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Cryptol.Symbolic.Value
  ( SBool, SWord
  , literalSWord
  , fromBitsLE
  , forallBV_, existsBV_
  , forallSBool_, existsSBool_
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
import qualified Data.Sequence as Seq

import Data.SBV.Dynamic

--import Cryptol.Eval.Monad
import Cryptol.Eval.Type   (TValue(..), isTBit, tvSeq)
import Cryptol.Eval.Monad  (Eval, ready)
import Cryptol.Eval.Value  ( GenValue(..), BitWord(..), lam, tlam, toStream,
                           toFinSeq, toSeq, WordValue(..),
                           fromSeq, fromVBit, fromVWord, fromVFun, fromVPoly,
                           fromVTuple, fromVRecord, lookupRecord, SeqMap(..),
                           ppBV,BV(..),integerToChar, lookupSeqMap,
                           wordValueSize, asBitsMap)
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.PP

import Control.Monad.Reader (ask)
import Control.Monad.Trans  (liftIO)

-- SBool and SWord -------------------------------------------------------------

type SBool = SVal
type SWord = SVal

fromBitsLE :: [SBool] -> SWord
fromBitsLE bs = foldl' f (literalSWord 0 0) bs
  where f w b = svJoin (svToWord1 b) w

literalSWord :: Int -> Integer -> SWord
literalSWord w i = svInteger (KBounded False w) i

forallBV_ :: Int -> Symbolic SWord
forallBV_ w = ask >>= liftIO . svMkSymVar (Just ALL) (KBounded False w) Nothing

existsBV_ :: Int -> Symbolic SWord
existsBV_ w = ask >>= liftIO . svMkSymVar (Just EX) (KBounded False w) Nothing

forallSBool_ :: Symbolic SBool
forallSBool_ = ask >>= liftIO . svMkSymVar (Just ALL) KBool Nothing

existsSBool_ :: Symbolic SBool
existsSBool_ = ask >>= liftIO . svMkSymVar (Just EX) KBool Nothing

-- Values ----------------------------------------------------------------------

type Value = GenValue SBool SWord

-- Symbolic Conditionals -------------------------------------------------------

iteSValue :: SBool -> Value -> Value -> Value
iteSValue c x y =
  case svAsBool c of
    Just True  -> x
    Just False -> y
    Nothing    -> mergeValue True c x y

mergeBit :: Bool
         -> SBool
         -> SBool
         -> SBool
         -> SBool
mergeBit f c b1 b2 = svSymbolicMerge KBool f c b1 b2

mergeWord :: Bool
          -> SBool
          -> WordValue SBool SWord
          -> WordValue SBool SWord
          -> WordValue SBool SWord
mergeWord f c (WordVal w1) (WordVal w2) =
    WordVal $ svSymbolicMerge (kindOf w1) f c w1 w2
mergeWord f c (WordVal w1) (BitsVal ys) =
    BitsVal $ mergeBits f c (Seq.fromList $ map ready $ unpackWord w1) ys
mergeWord f c (BitsVal xs) (WordVal w2) =
    BitsVal $ mergeBits f c xs (Seq.fromList $ map ready $ unpackWord w2)
mergeWord f c (BitsVal xs) (BitsVal ys) =
    BitsVal $ mergeBits f c xs ys
mergeWord f c w1 w2 =
    LargeBitsVal (wordValueSize w1) (mergeSeqMap f c (asBitsMap w1) (asBitsMap w2))

mergeWord' :: Bool
           -> SBool
           -> Eval (WordValue SBool SWord)
           -> Eval (WordValue SBool SWord)
           -> Eval (WordValue SBool SWord)
mergeWord' f c x y = mergeWord f c <$> x <*> y

mergeBits :: Bool
          -> SBool
          -> Seq.Seq (Eval SBool)
          -> Seq.Seq (Eval SBool)
          -> Seq.Seq (Eval SBool)
mergeBits f c bs1 bs2 = Seq.zipWith mergeBit' bs1 bs2
 where mergeBit' b1 b2 = mergeBit f c <$> b1 <*> b2

mergeValue :: Bool -> SBool -> Value -> Value -> Value
mergeValue f c v1 v2 =
  case (v1, v2) of
    (VRecord fs1, VRecord fs2) -> VRecord $ zipWith mergeField fs1 fs2
    (VTuple vs1 , VTuple vs2 ) -> VTuple $ zipWith (\x y -> mergeValue f c <$> x <*> y) vs1 vs2
    (VBit b1    , VBit b2    ) -> VBit $ mergeBit f c b1 b2
    (VWord n1 w1, VWord n2 w2 ) | n1 == n2 -> VWord n1 (mergeWord f c <$> w1 <*> w2)
    (VSeq n1 vs1, VSeq n2 vs2 ) | n1 == n2 -> VSeq n1 $ mergeSeqMap f c vs1 vs2
    (VStream vs1, VStream vs2) -> VStream $ mergeSeqMap f c vs1 vs2
    (VFun f1    , VFun f2    ) -> VFun $ \x -> mergeValue f c <$> (f1 x) <*> (f2 x)
    (VPoly f1   , VPoly f2   ) -> VPoly $ \x -> mergeValue f c <$> (f1 x) <*> (f2 x)
    (_          , _          ) -> panic "Cryptol.Symbolic.Value"
                                  [ "mergeValue: incompatible values" ]
  where
    mergeField (n1, x1) (n2, x2)
      | n1 == n2  = (n1, mergeValue f c <$> x1 <*> x2)
      | otherwise = panic "Cryptol.Symbolic.Value"
                    [ "mergeValue.mergeField: incompatible values" ]


mergeSeqMap :: Bool -> SBool -> SeqMap SBool SWord -> SeqMap SBool SWord -> SeqMap SBool SWord
mergeSeqMap f c x y =
  IndexSeqMap $ \i -> mergeValue f c <$> lookupSeqMap x i <*> lookupSeqMap y i

-- Symbolic Big-endian Words -------------------------------------------------------

instance BitWord SBool SWord where
  wordLen v = toInteger (intSizeOf v)
  wordAsChar v = integerToChar <$> svAsInteger v

  ppBit v
     | Just b <- svAsBool v = text $! if b then "True" else "False"
     | otherwise            = text "?"
  ppWord opts v
     | Just x <- svAsInteger v = ppBV opts (BV (wordLen v) x)
     | otherwise               = text "[?]"

  bitLit b    = svBool b
  wordLit n x = svInteger (KBounded False (fromInteger n)) x

  wordBit x idx = svTestBit x (intSizeOf x - 1 - fromIntegral idx)

  wordUpdate x idx b = svSymbolicMerge (kindOf x) False b wtrue wfalse
    where
     i' = intSizeOf x - 1 - fromInteger idx
     wtrue  = x `svOr`  svInteger (kindOf x) (bit i' :: Integer)
     wfalse = x `svAnd` svInteger (kindOf x) (complement (bit i' :: Integer))

  packWord bs = fromBitsLE (reverse bs)
  unpackWord x = [ svTestBit x i | i <- reverse [0 .. intSizeOf x - 1] ]

  joinWord x y = svJoin x y

  splitWord _leftW rightW w =
    ( svExtract (intSizeOf w - 1) (fromInteger rightW) w
    , svExtract (fromInteger rightW - 1) 0 w
    )

  extractWord len start w =
    svExtract (fromInteger start + fromInteger len - 1) (fromInteger start) w

  wordPlus  = svPlus
  wordMinus = svMinus
  wordMult  = svTimes

-- Errors ----------------------------------------------------------------------

evalPanic :: String -> [String] -> a
evalPanic cxt = panic ("[Symbolic]" ++ cxt)
