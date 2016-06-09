-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe, PatternGuards #-}
{-# LANGUAGE DeriveGeneric #-}
module Cryptol.Eval.Type where

import Cryptol.Eval.Monad
import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Solver.InfNat
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.Ident (Ident,mkIdent)

import Data.Maybe(fromMaybe)
import qualified Data.Map.Strict as Map
import GHC.Generics (Generic)
import Control.DeepSeq
import Control.DeepSeq.Generics

-- | An evaluated type.
-- These types do not contain type variables, type synonyms, or type functions.
newtype TValue = TValue { tValTy :: Type } deriving (Generic)

instance NFData TValue where rnf = genericRnf

instance Show TValue where
  showsPrec p (TValue v) = showsPrec p v

{-
-- TODO? use these instead?
-- Type Values -----------------------------------------------------------------

-- | An easy-to-use alternative representation for type `TValue`.
data TypeVal
  = TVBit
  | TVSeq Int TypeVal
  | TVStream TypeVal
  | TVTuple [TypeVal]
  | TVRecord [(Ident, TypeVal)]
  | TVFun TypeVal TypeVal

toTypeVal :: TValue -> TypeVal
toTypeVal ty
  | isTBit ty                    = TVBit
  | Just (n, ety) <- isTSeq ty   = case numTValue n of
                                     Nat w -> TVSeq (fromInteger w) (toTypeVal ety)
                                     Inf   -> TVStream (toTypeVal ety)
  | Just (aty, bty) <- isTFun ty = TVFun (toTypeVal aty) (toTypeVal bty)
  | Just (_, tys) <- isTTuple ty = TVTuple (map toTypeVal tys)
  | Just fields <- isTRec ty     = TVRecord [ (n, toTypeVal aty) | (n, aty) <- fields ]
  | otherwise                    = panic "Cryptol.Symbolic.Prims.toTypeVal" [ "bad TValue" ]

-}


isTBit :: TValue -> Bool
isTBit (TValue ty) = case ty of
  TCon (TC TCBit) [] -> True
  _                  -> False

isTSeq :: TValue -> Maybe (TValue, TValue)
isTSeq (TValue (TCon (TC TCSeq) [t1,t2])) = Just (TValue t1, TValue t2)
isTSeq _ = Nothing

isTFun :: TValue -> Maybe (TValue, TValue)
isTFun (TValue (TCon (TC TCFun) [t1,t2])) = Just (TValue t1, TValue t2)
isTFun _ = Nothing

isTTuple :: TValue -> Maybe (Int,[TValue])
isTTuple (TValue (TCon (TC (TCTuple n)) ts)) = Just (n, map TValue ts)
isTTuple _ = Nothing

isTRec :: TValue -> Maybe [(Ident, TValue)]
isTRec (TValue (TRec fs)) = Just [ (x, TValue t) | (x,t) <- fs ]
isTRec _ = Nothing

tvSeq :: TValue -> TValue -> TValue
tvSeq (TValue x) (TValue y) = TValue (tSeq x y)



numTValue :: TValue -> Nat'
numTValue (TValue ty) =
  case ty of
    TCon (TC (TCNum x)) _ -> Nat x
    TCon (TC TCInf) _     -> Inf
    _ -> panic "Cryptol.Eval.Value.numTValue" [ "Not a numeric type:", show ty ]

toNumTValue :: Nat' -> TValue
toNumTValue (Nat n) = TValue (TCon (TC (TCNum n)) [])
toNumTValue Inf     = TValue (TCon (TC TCInf) [])

finTValue :: TValue -> Integer
finTValue tval =
  case numTValue tval of
    Nat x -> x
    Inf   -> panic "Cryptol.Eval.Value.finTValue" [ "Unexpected `inf`" ]

-- Type Evaluation -------------------------------------------------------------

-- | Evaluation for types.
evalType' :: Map.Map TVar TValue -> Type -> TValue
evalType' env = TValue . go
  where
  go ty =
    case ty of
      TVar tv ->
        case Map.lookup tv env of
          Just (TValue v)   -> v
          Nothing  -> evalPanic "evalType" ["type variable not bound", show tv]

      TCon (TF f) ts -> tValTy $ evalTF f $ map (evalType' env) ts
      TCon tc ts     -> TCon tc (map go ts)
      TUser _ _ ty'  -> go ty'
      TRec fields    -> TRec [ (f,go t) | (f,t) <- fields ]

-- | Reduce type functions, rising an exception for undefined values.
evalTF :: TFun -> [TValue] -> TValue
evalTF tf vs = TValue $ cvt $ evalTF' tf $ map numTValue vs

-- | Reduce type functions, rising an exception for undefined values.
evalTF' :: TFun -> [Nat'] -> Nat'
evalTF' f vs
  | TCAdd           <- f, [x,y]   <- vs  =      nAdd x y
  | TCSub           <- f, [x,y]   <- vs  = mb $ nSub x y
  | TCMul           <- f, [x,y]   <- vs  =      nMul x y
  | TCDiv           <- f, [x,y]   <- vs  = mb $ nDiv x y
  | TCMod           <- f, [x,y]   <- vs  = mb $ nMod x y
  | TCWidth         <- f, [x]     <- vs  =      nWidth x
  | TCExp           <- f, [x,y]   <- vs  =      nExp x y
  | TCMin           <- f, [x,y]   <- vs  =      nMin x y
  | TCMax           <- f, [x,y]   <- vs  =      nMax x y
  | TCLenFromThen   <- f, [x,y,z] <- vs  = mb $ nLenFromThen x y z
  | TCLenFromThenTo <- f, [x,y,z] <- vs  = mb $ nLenFromThenTo x y z
  | otherwise  = evalPanic "evalTF"
                        ["Unexpected type function:", show ty]

  where mb = fromMaybe (typeCannotBeDemoted ty)
        ty = TCon (TF f) (map cvt vs)


cvt :: Nat' -> Type
cvt (Nat n) = tNum n
cvt Inf     = tInf




