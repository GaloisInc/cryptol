-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe, PatternGuards #-}

module Cryptol.Eval.Type (evalType, evalNumType, evalTF) where

import Cryptol.Eval.Env
import Cryptol.Eval.Error
import Cryptol.Eval.Value (TValue(..), tvSeq)
import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Solver.InfNat

import Data.Maybe(fromMaybe)


-- Type Evaluation -------------------------------------------------------------

-- | Evaluation for value types (kind *).
evalType :: EvalEnv -> Type -> TValue
evalType env = go
  where
    go ty =
      case ty of
        TVar tv ->
          case lookupType tv env of
            Just (Right v) -> v
            Just (Left _)  -> evalPanic "evalType" ["type variable has wrong kind", show tv]
            Nothing        -> evalPanic "evalType" ["type variable not bound", show tv]

        TUser _ _ ty'  -> go ty'
        TRec fields    -> TVRec [ (f, go t) | (f, t) <- fields ]
        TCon (TC c) ts ->
          case (c, ts) of
            (TCBit, [])     -> TVBit
            (TCSeq, [n, t]) -> tvSeq (evalNumType env n) (go t)
            (TCFun, [a, b]) -> TVFun (go a) (go b)
            (TCTuple _, _)  -> TVTuple (map go ts)
            -- FIXME: What about TCNewtype?
            _ -> evalPanic "evalType" ["not a value type", show ty]
        TCon (TF f) _ -> evalPanic "evalType" ["invalid type function", show f]
        TCon (PC p) _ -> evalPanic "evalType" ["invalid predicate symbol", show p]

-- | Evaluation for numeric types (kind #).
evalNumType :: EvalEnv -> Type -> Nat'
evalNumType env = go
  where
    go ty =
      case ty of
        TVar tv ->
          case lookupType tv env of
            Just (Left n)  -> n
            Just (Right _) -> evalPanic "evalNumType" ["type variable has wrong kind", show tv]
            Nothing        -> evalPanic "evalNumType" ["type variable not bound", show tv]

        TCon (TF f) ts         -> evalTF f $ map (evalNumType env) ts
        TCon (TC (TCNum n)) [] -> Nat n
        TCon (TC TCInf)     [] -> Inf
        TUser _ _ ty'          -> go ty'
        _                      -> evalPanic "evalNumType" ["not a numeric type", show ty]

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
