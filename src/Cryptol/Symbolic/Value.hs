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
  ( SBool, SWord, SInteger
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
  )
  where

import Data.List (foldl')
import qualified Data.Sequence as Seq

import Data.SBV.Dynamic

--import Cryptol.Eval.Monad
import Cryptol.Eval.Type   (TValue(..), isTBit, tvSeq)
import Cryptol.Eval.Monad  (Eval)
import Cryptol.Eval.Value  ( GenValue(..), BitWord(..), lam, tlam, toStream,
                           toFinSeq, toSeq, WordValue(..), asBitsVal,
                           fromSeq, fromVBit, fromVWord, fromVFun, fromVPoly,
                           fromVTuple, fromVRecord, lookupRecord, SeqMap(..),
                           ppBV, BV(..), integerToChar, lookupSeqMap )
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.PP

-- SBool and SWord -------------------------------------------------------------

type SBool = SVal
type SWord = SVal
type SInteger = SVal

fromBitsLE :: [SBool] -> SWord
fromBitsLE bs = foldl' f (literalSWord 0 0) bs
  where f w b = svJoin (svToWord1 b) w

literalSWord :: Int -> Integer -> SWord
literalSWord w i = svInteger (KBounded False w) i

forallBV_ :: Int -> Symbolic SWord
forallBV_ w = svMkSymVar (Just ALL) (KBounded False w) Nothing

existsBV_ :: Int -> Symbolic SWord
existsBV_ w = svMkSymVar (Just EX) (KBounded False w) Nothing

forallSBool_ :: Symbolic SBool
forallSBool_ = svMkSymVar (Just ALL) KBool Nothing

existsSBool_ :: Symbolic SBool
existsSBool_ = svMkSymVar (Just EX) KBool Nothing

forallSInteger_ :: Symbolic SBool
forallSInteger_ = svMkSymVar (Just ALL) KUnbounded Nothing

existsSInteger_ :: Symbolic SBool
existsSInteger_ = svMkSymVar (Just EX) KUnbounded Nothing

-- Values ----------------------------------------------------------------------

type Value = GenValue SBool SWord SInteger

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
mergeWord f c w1 w2 = BitsVal $ mergeBits f c (asBitsVal w1) (asBitsVal w2)

mergeBits :: Bool
          -> SBool
          -> Seq.Seq (Eval SBool)
          -> Seq.Seq (Eval SBool)
          -> Seq.Seq (Eval SBool)
mergeBits f c bs1 bs2 = Seq.zipWith mergeBit' bs1 bs2
 where mergeBit' b1 b2 = mergeBit f c <$> b1 <*> b2

mergeInteger :: Bool
             -> SBool
             -> SInteger
             -> SInteger
             -> SInteger
mergeInteger f c x y = svSymbolicMerge KUnbounded f c x y

mergeValue :: Bool -> SBool -> Value -> Value -> Value
mergeValue f c v1 v2 =
  case (v1, v2) of
    (VRecord fs1, VRecord fs2) -> VRecord $ zipWith mergeField fs1 fs2
    (VTuple vs1 , VTuple vs2 ) -> VTuple $ zipWith (\x y -> mergeValue f c <$> x <*> y) vs1 vs2
    (VBit b1    , VBit b2    ) -> VBit $ mergeBit f c b1 b2
    (VInteger i1, VInteger i2) -> VInteger $ mergeInteger f c i1 i2
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

instance BitWord SBool SWord SInteger where
  wordLen v = toInteger (intSizeOf v)
  wordAsChar v = integerToChar <$> svAsInteger v

  ppBit v
     | Just b <- svAsBool v = text $! if b then "True" else "False"
     | otherwise            = text "?"
  ppWord opts v
     | Just x <- svAsInteger v = ppBV opts (BV (wordLen v) x)
     | otherwise               = text "[?]"
  ppInteger _opts v
     | Just x <- svAsInteger v = integer x
     | otherwise               = text "[?]"

  bitLit b    = svBool b
  wordLit n x = svInteger (KBounded False (fromInteger n)) x
  integerLit x = svInteger KUnbounded x

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

  wordToInt = svToInteger
  wordFromInt = svFromInteger

-- TODO: implement this properly in SBV using "bv2int"
svToInteger :: SWord -> SInteger
svToInteger w =
  case svAsInteger w of
    Nothing -> evalPanic "toInteger" ["unsupported symbolic argument"]
    Just x  -> svInteger KUnbounded x

-- TODO: implement this properly in SBV using "int2bv"
svFromInteger :: Integer -> SInteger -> SWord
svFromInteger n i =
  case svAsInteger i of
    Nothing -> evalPanic "fromInteger" ["unsupported symbolic argument"]
    Just x  -> literalSWord (fromInteger n) x

-- Errors ----------------------------------------------------------------------

evalPanic :: String -> [String] -> a
evalPanic cxt = panic ("[Symbolic]" ++ cxt)
