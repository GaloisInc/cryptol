-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe, PatternGuards #-}

module Cryptol.Eval.Type (evalType, evalValType, evalNumType, evalTF) where

import Cryptol.Eval.Env
import Cryptol.Eval.Error
import Cryptol.Eval.Value (TValue(..), tvSeq)
import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Solver.InfNat

import Data.Maybe(fromMaybe)


-- Type Evaluation -------------------------------------------------------------

-- | Evaluation for types (kind * or #).
evalType :: EvalEnv -> Type -> Either Nat' TValue
evalType env ty =
  case ty of
    TVar tv ->
      case lookupType tv env of
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
evalValType :: EvalEnv -> Type -> TValue
evalValType env ty =
  case evalType env ty of
    Left _ -> evalPanic "evalValType" ["expected value type, found numeric type"]
    Right t -> t

evalNumType :: EvalEnv -> Type -> Nat'
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
