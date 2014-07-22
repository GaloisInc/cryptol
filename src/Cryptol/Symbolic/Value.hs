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
import Data.List (genericTake)

import Cryptol.Eval.Value (TValue, isTBit, numTValue)
import Cryptol.Symbolic.BitVector
import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Solver.InfNat(Nat'(..))
import Cryptol.Utils.Panic (panic)

import Data.SBV (SBool, fromBitsBE, sbvTestBit, Mergeable(..))

-- Values ----------------------------------------------------------------------

data Value
  = VRecord [(Name, Value)]   -- @ { .. } @
  | VTuple [Value]            -- @ ( .. ) @
  | VBit SBool                -- @ Bit    @
  | VWord SWord               -- @ [n]Bit @
  | VSeq Bool [Value]         -- @ [n]a   @
                              -- The boolean parameter indicates whether or not
                              -- this is a sequence of bits.
  | VStream [Value]           -- @ [inf]a @
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
      (VSeq b1 vs1, VSeq _ vs2 ) -> VSeq b1 $ symbolicMerge c vs1 vs2
      (VStream vs1, VStream vs2) -> VStream $ symbolicMerge c vs1 vs2
      (VFun f1    , VFun f2    ) -> VFun $ symbolicMerge c f1 f2
      (VPoly f1   , VPoly f2   ) -> VPoly $ symbolicMerge c f1 f2
      (VWord w1   , _          ) -> VWord $ symbolicMerge c w1 (fromWord v2)
      (_          , VWord w2   ) -> VWord $ symbolicMerge c (fromWord v1) w2
      (_          , _          ) -> error "symbolicMerge: incompatible values"
    where
      mergeField (n1, x1) (n2, x2)
        | n1 == n2  = (n1, symbolicMerge c x1 x2)
        | otherwise = error "symbolicMerge: incompatible values"

-- Big-endian Words ------------------------------------------------------------

unpackWord :: SWord -> [SBool]
unpackWord s = [ sbvTestBit s i | i <- reverse [0 .. bitSize s - 1] ]

-- Constructors and Accessors --------------------------------------------------

lam :: (Value -> Value) -> Value
lam  = VFun

tlam :: (TValue -> Value) -> Value
tlam f = VPoly f

-- | Generate a stream.
toStream :: [Value] -> Value
toStream  = VStream

toFinSeq :: TValue -> [Value] -> Value
toFinSeq elty = VSeq (isTBit elty)

-- | Construct either a finite sequence, or a stream.  In the finite case,
-- record whether or not the elements were bits, to aid pretty-printing.
toSeq :: TValue -> TValue -> [Value] -> Value
toSeq len elty vals = case numTValue len of
  Nat n -> toFinSeq elty (genericTake n vals)
  Inf   -> toStream vals

vApply :: Value -> Value -> Value
vApply (VFun f) v = f v
vApply _ _ = error "vApply: not a function"

fromVBit :: Value -> SBool
fromVBit (VBit b) = b
fromVBit _ = error "fromVBit: not a bit"

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
