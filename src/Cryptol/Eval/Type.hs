-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe, PatternGuards #-}
{-# LANGUAGE DeriveAnyClass #-}
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

-- | An evaluated type of kind *.
-- These types do not contain type variables, type synonyms, or type functions.
data TValue
  = TVBit
  | TVSeq Integer TValue
  | TVStream TValue -- ^ [inf]t
  | TVTuple [TValue]
  | TVRec [(Ident, TValue)]
  | TVFun TValue TValue
    deriving (Generic, NFData)

tValTy :: TValue -> Type
tValTy tv =
  case tv of
    TVBit       -> tBit
    TVSeq n t   -> tSeq (tNum n) (tValTy t)
    TVStream t  -> tSeq tInf (tValTy t)
    TVTuple ts  -> tTuple (map tValTy ts)
    TVRec fs    -> tRec [ (f, tValTy t) | (f, t) <- fs ]
    TVFun t1 t2 -> tFun (tValTy t1) (tValTy t2)

instance Show TValue where
  showsPrec p v = showsPrec p (tValTy v)


-- Utilities -------------------------------------------------------------------

isTBit :: TValue -> Bool
isTBit TVBit = True
isTBit _ = False

tvSeq :: Nat' -> TValue -> TValue
tvSeq (Nat n) t = TVSeq n t
tvSeq Inf     t = TVStream t

finNat' :: Nat' -> Integer
finNat' n' =
  case n' of
    Nat x -> x
    Inf   -> panic "Cryptol.Eval.Value.finNat'" [ "Unexpected `inf`" ]


-- Type Evaluation -------------------------------------------------------------

type TypeEnv = Map.Map TVar (Either Nat' TValue)


-- | Evaluation for types (kind * or #).
evalType :: TypeEnv -> Type -> Either Nat' TValue
evalType env ty =
  case ty of
    TVar tv ->
      case Map.lookup tv env of
        Just v -> v
        Nothing -> evalPanic "evalType" ["type variable not bound", show tv]

    TUser _ _ ty'  -> evalType env ty'
    TRec fields    -> Right $ TVRec [ (f, val t) | (f, t) <- fields ]
    TCon (TC c) ts ->
      case (c, ts) of
        (TCBit, [])     -> Right $ TVBit
        (TCSeq, [n, t]) -> Right $ tvSeq (num n) (val t)
        (TCFun, [a, b]) -> Right $ TVFun (val a) (val b)
        (TCTuple _, _)  -> Right $ TVTuple (map val ts)
        (TCNum n, [])   -> Left $ Nat n
        (TCInf, [])     -> Left $ Inf
        -- FIXME: What about TCNewtype?
        _ -> evalPanic "evalType" ["not a value type", show ty]
    TCon (TF f) ts      -> Left $ evalTF f (map num ts)
    TCon (PC p) _       -> evalPanic "evalType" ["invalid predicate symbol", show p]
  where
    val = evalValType env
    num = evalNumType env

-- | Evaluation for value types (kind *).
evalValType :: TypeEnv -> Type -> TValue
evalValType env ty =
  case evalType env ty of
    Left _ -> evalPanic "evalValType" ["expected value type, found numeric type"]
    Right t -> t

evalNumType :: TypeEnv -> Type -> Nat'
evalNumType env ty =
  case evalType env ty of
    Left n -> n
    Right _ -> evalPanic "evalValType" ["expected numeric type, found value type"]


-- | Reduce type functions, raising an exception for undefined values.
evalTF :: TFun -> [Nat'] -> Nat'
evalTF f vs
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
        ty = TCon (TF f) (map tNat' vs)
