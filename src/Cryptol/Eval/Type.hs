-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe, PatternGuards #-}

module Cryptol.Eval.Type (evalType, evalTF) where

import Cryptol.Eval.Env
import Cryptol.Eval.Error
import Cryptol.Eval.Value (TValue(..), numTValue, toNumTValue)
import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Solver.InfNat

import Data.Maybe(fromMaybe)


-- Type Evaluation -------------------------------------------------------------

-- | Evaluation for types.
evalType :: EvalEnv -> Type -> TValue
evalType env = go
  where
  go ty =
    case ty of
      TVar tv ->
        case lookupType tv env of
          Just v   -> v
          Nothing  -> evalPanic "evalType" ["type variable not bound", show tv]

      TCon (TF f) ts -> evalTF f $ map (evalType env) ts
      TCon (TC c) ts -> evalTC c (map go ts)
      TCon (PC p) _  -> evalPanic "evalType" ["invalid predicate symbol", show p]
      TUser _ _ ty'  -> go ty'
      TRec fields    -> TVRec [ (f,go t) | (f,t) <- fields ]

evalTC :: TC -> [TValue] -> TValue
evalTC tc ts =
  case (tc, ts) of
    (TCNum n, [])   -> TVNat n
    (TCInf, [])     -> TVInf
    (TCBit, [])     -> TVBit
    (TCSeq, [n, t]) -> TVSeq n t
    (TCFun, [a, b]) -> TVFun a b
    (TCTuple _, _)  -> TVTuple ts
    -- FIXME: What about TCNewtype?
    _               -> evalPanic "evalType" ["invalid type constructor arguments", show tc]

-- | Reduce type functions, raising an exception for undefined values.
evalTF :: TFun -> [TValue] -> TValue
evalTF tf vs = toNumTValue $ evalTF' tf $ map numTValue vs

-- | Reduce type functions, raising an exception for undefined values.
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
        ty = TCon (TF f) (map tNat' vs)
