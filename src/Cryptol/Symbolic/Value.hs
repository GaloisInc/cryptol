-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Cryptol.Symbolic.Value
  ( Value
  , TValue, numTValue, toNumTValue, finTValue, isTBit, isTFun, isTSeq, isTTuple, isTRec, tvSeq
  , GenValue(..), lam, tlam, toStream, toFinSeq, toSeq
  , fromVBit, fromVFun, fromVPoly, fromVTuple, fromVRecord, lookupRecord
  , fromSeq, fromWord
  , evalPanic
  )
  where

import Data.Bits (bitSize)

import Cryptol.Eval.Value (TValue, numTValue, toNumTValue, finTValue, isTBit, isTFun, isTSeq, isTTuple, isTRec, tvSeq,
                           GenValue(..), lam, tlam, toStream, toFinSeq, toSeq,
                           fromVBit, fromVFun, fromVPoly, fromVTuple, fromVRecord, lookupRecord)
import Cryptol.Symbolic.BitVector
import Cryptol.Utils.Panic (panic)

import Data.SBV (SBool, fromBitsBE, sbvTestBit, Mergeable(..))

-- Values ----------------------------------------------------------------------

type Value = GenValue SBool SWord

-- Symbolic Conditionals -------------------------------------------------------

instance Mergeable Value where
  symbolicMerge f c v1 v2 =
    case (v1, v2) of
      (VRecord fs1, VRecord fs2) -> VRecord $ zipWith mergeField fs1 fs2
      (VTuple vs1 , VTuple vs2 ) -> VTuple $ zipWith (symbolicMerge f c) vs1 vs2
      (VBit b1    , VBit b2    ) -> VBit $ symbolicMerge f c b1 b2
      (VWord w1   , VWord w2   ) -> VWord $ symbolicMerge f c w1 w2
      (VSeq b1 vs1, VSeq _ vs2 ) -> VSeq b1 $ symbolicMerge f c vs1 vs2
      (VStream vs1, VStream vs2) -> VStream $ mergeStream vs1 vs2
      (VFun f1    , VFun f2    ) -> VFun $ symbolicMerge f c f1 f2
      (VPoly f1   , VPoly f2   ) -> VPoly $ symbolicMerge f c f1 f2
      (VWord w1   , _          ) -> VWord $ symbolicMerge f c w1 (fromWord v2)
      (_          , VWord w2   ) -> VWord $ symbolicMerge f c (fromWord v1) w2
      (_          , _          ) -> panic "Cryptol.Symbolic.Value"
                                      [ "symbolicMerge: incompatible values" ]
    where
      mergeField (n1, x1) (n2, x2)
        | n1 == n2  = (n1, symbolicMerge f c x1 x2)
        | otherwise = panic "Cryptol.Symbolic.Value"
                        [ "symbolicMerge.mergeField: incompatible values" ]
      mergeStream xs ys =
        symbolicMerge f c (head xs) (head ys) : mergeStream (tail xs) (tail ys)

-- Big-endian Words ------------------------------------------------------------

unpackWord :: SWord -> [SBool]
unpackWord s = [ sbvTestBit s i | i <- reverse [0 .. bitSize s - 1] ]

-- Constructors and Accessors --------------------------------------------------

fromWord :: Value -> SWord
fromWord (VWord s) = s
fromWord v = Data.SBV.fromBitsBE (map fromVBit (fromSeq v))

-- | Extract a sequence.
fromSeq :: Value -> [Value]
fromSeq v = case v of
  VSeq _ vs  -> vs
  VWord s    -> map VBit (unpackWord s)
  VStream vs -> vs
  _          -> evalPanic "fromSeq" ["not a sequence"]

-- Errors ----------------------------------------------------------------------

evalPanic :: String -> [String] -> a
evalPanic cxt = panic ("[Symbolic]" ++ cxt)
