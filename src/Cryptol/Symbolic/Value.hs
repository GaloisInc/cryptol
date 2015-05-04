-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Cryptol.Symbolic.Value
  ( SBool, SWord
  , literalSWord
  , fromBitsLE
  , forallBV_, existsBV_
  , forallSBool_, existsSBool_
  , Value
  , TValue, numTValue, toNumTValue, finTValue, isTBit, isTFun, isTSeq, isTTuple, isTRec, tvSeq
  , GenValue(..), lam, tlam, toStream, toFinSeq, toSeq
  , fromVBit, fromVFun, fromVPoly, fromVTuple, fromVRecord, lookupRecord
  , fromSeq, fromVWord
  , evalPanic
  , iteValue, sBranchValue, mergeValue
  )
  where

import Data.List (foldl')

import Data.SBV.Dynamic

import Cryptol.Eval.Value (TValue, numTValue, toNumTValue, finTValue, isTBit,
                           isTFun, isTSeq, isTTuple, isTRec, tvSeq, GenValue(..),
                           BitWord(..), lam, tlam, toStream, toFinSeq, toSeq,
                           fromSeq, fromVBit, fromVWord, fromVFun, fromVPoly,
                           fromVTuple, fromVRecord, lookupRecord)
import Cryptol.Utils.Panic (panic)

-- SBool and SWord -------------------------------------------------------------

type SBool = SVal
type SWord = SVal

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

-- Values ----------------------------------------------------------------------

type Value = GenValue SBool SWord

-- Symbolic Conditionals -------------------------------------------------------

iteValue :: SBool -> Value -> Value -> Value
iteValue c x y =
  case svAsBool c of
    Just True  -> x
    Just False -> y
    Nothing    -> mergeValue True c x y

sBranchValue :: SBool -> Value -> Value -> Value
sBranchValue t x y =
  case svAsBool c of
    Just True  -> x
    Just False -> y
    Nothing    -> mergeValue False c x y
  where
    c = svReduceInPathCondition t

mergeValue :: Bool -> SBool -> Value -> Value -> Value
mergeValue f c v1 v2 =
  case (v1, v2) of
    (VRecord fs1, VRecord fs2) -> VRecord $ zipWith mergeField fs1 fs2
    (VTuple vs1 , VTuple vs2 ) -> VTuple $ zipWith (mergeValue f c) vs1 vs2
    (VBit b1    , VBit b2    ) -> VBit $ mergeBit b1 b2
    (VWord w1   , VWord w2   ) -> VWord $ mergeWord w1 w2
    (VSeq b1 vs1, VSeq _ vs2 ) -> VSeq b1 $ zipWith (mergeValue f c) vs1 vs2
    (VStream vs1, VStream vs2) -> VStream $ mergeStream vs1 vs2
    (VFun f1    , VFun f2    ) -> VFun $ \x -> mergeValue f c (f1 x) (f2 x)
    (VPoly f1   , VPoly f2   ) -> VPoly $ \x -> mergeValue f c (f1 x) (f2 x)
    (VWord w1   , _          ) -> VWord $ mergeWord w1 (fromVWord v2)
    (_          , VWord w2   ) -> VWord $ mergeWord (fromVWord v1) w2
    (_          , _          ) -> panic "Cryptol.Symbolic.Value"
                                  [ "mergeValue: incompatible values" ]
  where
    mergeBit b1 b2 = svSymbolicMerge KBool f c b1 b2
    mergeWord w1 w2 = svSymbolicMerge (svKind w1) f c w1 w2
    mergeField (n1, x1) (n2, x2)
      | n1 == n2  = (n1, mergeValue f c x1 x2)
      | otherwise = panic "Cryptol.Symbolic.Value"
                    [ "mergeValue.mergeField: incompatible values" ]
    mergeStream xs ys =
      mergeValue f c (head xs) (head ys) : mergeStream (tail xs) (tail ys)

-- Big-endian Words ------------------------------------------------------------

instance BitWord SBool SWord where
  packWord bs = fromBitsLE (reverse bs)
  unpackWord x = [ svTestBit x i | i <- reverse [0 .. svBitSize x - 1] ]

-- Errors ----------------------------------------------------------------------

evalPanic :: String -> [String] -> a
evalPanic cxt = panic ("[Symbolic]" ++ cxt)
