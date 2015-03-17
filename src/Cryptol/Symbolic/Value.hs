-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Cryptol.Symbolic.Value
  ( Value
  , TValue, numTValue, toNumTValue, finTValue, isTBit, isTFun, isTSeq, isTTuple, isTRec, tvSeq
  , GenValue(..), lam, tlam, toStream, toFinSeq, toSeq
  , fromVBit, fromVFun, fromVPoly, fromVTuple, fromVRecord, lookupRecord
  , fromSeq, fromVWord
  , evalPanic
  )
  where

import Data.Bits (bitSize)

import Cryptol.Eval.Value (TValue, numTValue, toNumTValue, finTValue, isTBit, isTFun, isTSeq, isTTuple, isTRec, tvSeq,
                           GenValue(..), BitWord(..), lam, tlam, toStream, toFinSeq, toSeq, fromSeq,
                           fromVBit, fromVWord, fromVFun, fromVPoly, fromVTuple, fromVRecord, lookupRecord)
import Cryptol.Symbolic.BitVector
import Cryptol.Utils.Panic (panic)

import Data.SBV (SBool, fromBitsBE, Mergeable(..), HasKind(..), EqSymbolic(..))
import Data.SBV.Internals (symbolicMergeWithKind, genLiteral)

-- Values ----------------------------------------------------------------------

type Value = GenValue SBool SWord

-- Symbolic Conditionals -------------------------------------------------------

instance Mergeable Value where
  symbolicMerge f c v1 v2 =
    case (v1, v2) of
      (VRecord fs1, VRecord fs2) -> VRecord $ zipWith mergeField fs1 fs2
      (VTuple vs1 , VTuple vs2 ) -> VTuple $ zipWith (symbolicMerge f c) vs1 vs2
      (VBit b1    , VBit b2    ) -> VBit $ symbolicMerge f c b1 b2
      (VWord w1   , VWord w2   ) -> VWord $ mergeWord w1 w2
      (VSeq b1 vs1, VSeq _ vs2 ) -> VSeq b1 $ symbolicMerge f c vs1 vs2
      (VStream vs1, VStream vs2) -> VStream $ mergeStream vs1 vs2
      (VFun f1    , VFun f2    ) -> VFun $ symbolicMerge f c f1 f2
      (VPoly f1   , VPoly f2   ) -> VPoly $ symbolicMerge f c f1 f2
      (VWord w1   , _          ) -> VWord $ mergeWord w1 (fromVWord v2)
      (_          , VWord w2   ) -> VWord $ mergeWord (fromVWord v1) w2
      (_          , _          ) -> panic "Cryptol.Symbolic.Value"
                                      [ "symbolicMerge: incompatible values" ]
    where
      mergeWord w1 w2 = symbolicMergeWithKind (kindOf w1) f c w1 w2
      mergeField (n1, x1) (n2, x2)
        | n1 == n2  = (n1, symbolicMerge f c x1 x2)
        | otherwise = panic "Cryptol.Symbolic.Value"
                        [ "symbolicMerge.mergeField: incompatible values" ]
      mergeStream xs ys =
        symbolicMerge f c (head xs) (head ys) : mergeStream (tail xs) (tail ys)

-- Big-endian Words ------------------------------------------------------------

instance BitWord SBool SWord where
  packWord bs = Data.SBV.fromBitsBE bs
  unpackWord w = [ sbvTestBit' w i | i <- reverse [0 .. bitSize w - 1] ]

sbvTestBit' :: SWord -> Int -> SBool
sbvTestBit' w i = extract i i w .== literalSWord 1 1

-- Errors ----------------------------------------------------------------------

evalPanic :: String -> [String] -> a
evalPanic cxt = panic ("[Symbolic]" ++ cxt)
