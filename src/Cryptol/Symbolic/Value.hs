-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Cryptol.Symbolic.Value where

import Data.Bits (bitSize)

import Cryptol.Eval.Value (TValue)
import Cryptol.Symbolic.BitVector
import Cryptol.TypeCheck.AST
import Cryptol.Utils.Panic (panic)

import Data.SBV (SBool, fromBitsBE, sbvTestBit, Mergeable(..))

-- Values ----------------------------------------------------------------------

data Value
  = VRecord [(Name, Value)]   -- @ { .. } @
  | VTuple [Value]            -- @ ( .. ) @
  | VBit SBool                -- @ Bit    @
  | VWord SWord               -- @ [n]Bit @
  | VNil
  | VCons Value Value         -- @ [n]a @ head, tail
  | VFun (Value -> Value)     -- functions
  | VPoly (TValue -> Value)   -- polymorphic values (kind *)

-- Symbolic Conditionals -------------------------------------------------------

instance Mergeable Value where
  symbolicMerge c v1 v2 =
    case (v1, v2) of
      (VRecord fs1, VRecord fs2) -> VRecord $ zipWith mergeField fs1 fs2
      (VTuple vs1 , VTuple vs2 ) -> VTuple $ zipWith (symbolicMerge c) vs1 vs2
      (VBit b1    , VBit b2    ) -> VBit $ symbolicMerge c b1 b2
      (VWord w1   , VWord w2   ) -> VWord $ symbolicMerge c w1 w2
      (VNil       , VNil       ) -> VNil
      (VCons h1 t1, VCons h2 t2) -> VCons (symbolicMerge c h1 h2) (symbolicMerge c t1 t2)
      (VFun f1    , VFun f2    ) -> VFun $ symbolicMerge c f1 f2
      (VPoly f1   , VPoly f2   ) -> VPoly $ symbolicMerge c f1 f2
      (VWord w1   , _          ) -> VWord $ symbolicMerge c w1 (fromWord v2)
      (_          , VWord w2   ) -> VWord $ symbolicMerge c (fromWord v1) w2
      (_          , _          ) -> error "symbolicMerge: incompatible values"
    where
      mergeField (n1, x1) (n2, x2)
        | n1 == n2  = (n1, symbolicMerge c x1 x2)
        | otherwise = error "symbolicMerge: incompatible values"

-- Constructors and Accessors --------------------------------------------------

tlam :: (TValue -> Value) -> Value
tlam f = VPoly f

vSeq :: [Value] -> Value
vSeq []       = VNil
vSeq (x : xs) = VCons x (vSeq xs)

vApply :: Value -> Value -> Value
vApply (VFun f) v = f v
vApply _ _ = error "vApply: not a function"

fromVBit :: Value -> SBool
fromVBit (VBit b) = b
fromVBit _ = error "fromVBit: not a bit"

fromWord :: Value -> SWord
fromWord (VWord s) = s
fromWord v = Data.SBV.fromBitsBE (map fromVBit (fromSeq v))

fromSeq :: Value -> [Value]
fromSeq VNil = []
fromSeq (VCons x xs) = x : fromSeq xs
fromSeq (VWord s) = [ VBit (sbvTestBit s i) | i <- reverse [0 .. bitSize s - 1] ]
fromSeq _ = error "fromSeq: not a sequence"

fromVCons :: Value -> (Value, Value)
fromVCons (VCons h t) = (h, t)
fromVCons (VWord s) = fromVCons (foldr (\h t -> VCons h t) VNil bs)
  where bs = reverse [ VBit (sbvTestBit s i) | i <- [0 .. bitSize s - 1] ]
fromVCons _ = error "fromVCons: not a stream"

fromVFun :: Value -> (Value -> Value)
fromVFun (VFun f) = f
fromVFun _ = error "fromVFun: not a function"

fromVPoly :: Value -> (TValue -> Value)
fromVPoly (VPoly f) = f
fromVPoly _ = error "fromVPoly: not a function"

fromVTuple :: Value -> [Value]
fromVTuple (VTuple vs) = vs
fromVTuple _ = error "fromVTuple: not a tuple"

fromVRecord :: Value -> [(Name, Value)]
fromVRecord v = case v of
  VRecord fs -> fs
  _          -> evalPanic "fromVRecord" ["not a record"]

lookupRecord :: Name -> Value -> Value
lookupRecord f rec = case lookup f (fromVRecord rec) of
  Just v  -> v
  Nothing -> error "lookupRecord"

-- Errors ----------------------------------------------------------------------

evalPanic :: String -> [String] -> a
evalPanic cxt = panic ("[Symbolic]" ++ cxt)
