-- |
-- Module      :  Cryptol.TypeCheck.Unify
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe #-}
{-# LANGUAGE PatternGuards, ViewPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
module Cryptol.TypeCheck.Unify where

import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Subst

import Control.Monad.Writer (Writer, writer, runWriter)
import Data.Ord(comparing)
import Data.List(sortBy)
import qualified Data.Set as Set

import Prelude ()
import Prelude.Compat

-- | The most general unifier is a substitution and a set of constraints
-- on bound variables.
type MGU = (Subst,[Prop])

type Result a = Writer [UnificationError] a

runResult :: Result a -> (a, [UnificationError])
runResult = runWriter

data UnificationError
  = UniTypeMismatch Type Type
  | UniKindMismatch Kind Kind
  | UniTypeLenMismatch Int Int
  | UniRecursive TVar Type
  | UniNonPolyDepends TVar [TParam]
  | UniNonPoly TVar Type

uniError :: UnificationError -> Result MGU
uniError e = writer (emptyMGU, [e])


emptyMGU :: MGU
emptyMGU = (emptySubst, [])

mgu :: Type -> Type -> Result MGU

mgu (TUser c1 ts1 _) (TUser c2 ts2 _)
  | c1 == c2 && ts1 == ts2  = return emptyMGU

mgu (TVar x) t        = bindVar x t
mgu t (TVar x)        = bindVar x t

mgu (TUser _ _ t1) t2 = mgu t1 t2
mgu t1 (TUser _ _ t2) = mgu t1 t2

mgu (TCon (TC tc1) ts1) (TCon (TC tc2) ts2)
  | tc1 == tc2 = mguMany ts1 ts2

mgu (TCon (TF f1) ts1) (TCon (TF f2) ts2)
  | f1 == f2 && ts1 == ts2  = return emptyMGU

mgu t1 t2
  | TCon (TF _) _ <- t1, isNum, k1 == k2 = return (emptySubst, [t1 =#= t2])
  | TCon (TF _) _ <- t2, isNum, k1 == k2 = return (emptySubst, [t1 =#= t2])
  where
  k1 = kindOf t1
  k2 = kindOf t2

  isNum = k1 == KNum

mgu (TRec fs1) (TRec fs2)
  | ns1 == ns2 = mguMany ts1 ts2
  where
  (ns1,ts1)  = sortFields fs1
  (ns2,ts2)  = sortFields fs2
  sortFields = unzip . sortBy (comparing fst)

mgu t1 t2
  | not (k1 == k2)  = uniError $ UniKindMismatch k1 k2
  | otherwise       = uniError $ UniTypeMismatch t1 t2
  where
  k1 = kindOf t1
  k2 = kindOf t2


mguMany :: [Type] -> [Type] -> Result MGU
mguMany [] [] = return emptyMGU
mguMany (t1 : ts1) (t2 : ts2) =
  do (su1,ps1) <- mgu t1 t2
     (su2,ps2) <- mguMany (apSubst su1 ts1) (apSubst su1 ts2)
     return (su2 @@ su1, ps1 ++ ps2)
mguMany t1 t2 = uniError $ UniTypeLenMismatch (length t1) (length t2)


bindVar :: TVar -> Type -> Result MGU

bindVar x (tNoUser -> TVar y)
  | x == y                      = return emptyMGU

bindVar v@(TVBound {}) (tNoUser -> TVar v1@(TVFree {})) = bindVar v1 (TVar v)

bindVar v@(TVBound {}) t
  | k == kindOf t = if k == KNum
                       then return (emptySubst, [TVar v =#= t])
                       else uniError $ UniNonPoly v t
  | otherwise     = uniError $ UniKindMismatch k (kindOf t)
  where k = kindOf v

bindVar x@(TVFree _ xk xscope _) (tNoUser -> TVar y@(TVFree _ yk yscope _))
  | xscope `Set.isProperSubsetOf` yscope, xk == yk =
    return (uncheckedSingleSubst y (TVar x), [])
    -- In this case, we can add the reverse binding y ~> x to the
    -- substitution, but the instantiation x ~> y would be forbidden
    -- because it would allow y to escape from its scope.

bindVar x t =
  case singleSubst x t of
    Left SubstRecursive
      | kindOf x == KType -> uniError $ UniRecursive x t
      | otherwise -> return (emptySubst, [TVar x =#= t])
    Left (SubstEscaped tps) ->
      uniError $ UniNonPolyDepends x tps
    Left (SubstKindMismatch k1 k2) ->
      uniError $ UniKindMismatch k1 k2
    Right su ->
      return (su, [])
