-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe, PatternGuards #-}

module Cryptol.Eval.Type (evalType, evalTF) where

import Cryptol.Eval.Env
import Cryptol.Eval.Error
import Cryptol.Eval.Value(TValue(..),numTValue)
import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Solver.InfNat

import Data.Maybe(fromMaybe)


-- Type Evaluation -------------------------------------------------------------

-- | Evaluation for types.
evalType :: EvalEnv -> Type -> TValue
evalType env = TValue . go
  where
  go ty =
    case ty of
      TVar tv ->
        case lookupType tv env of
          Just (TValue v)   -> v
          Nothing  -> evalPanic "evalType" ["type variable not bound", show tv]

      TCon (TF f) ts -> tValTy $ evalTF f $ map (evalType env) ts
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
  | TCLg2           <- f, [x]     <- vs  =      nLg2 x
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




