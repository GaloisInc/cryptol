-- |
-- Module      :  Cryptol.TypeCheck.Unify
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe #-}
{-# LANGUAGE PatternGuards, ViewPatterns #-}
{-# LANGUAGE DeriveFunctor, DeriveGeneric, DeriveAnyClass #-}
{-# LANGUAGE BlockArguments, OverloadedStrings #-}
module Cryptol.TypeCheck.Unify where

import Control.DeepSeq(NFData)
import GHC.Generics(Generic)

import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Subst
import Cryptol.Utils.RecordMap
import Cryptol.Utils.Ident(Ident)
import Cryptol.ModuleSystem.Name(nameIdent)

import Cryptol.TypeCheck.PP
import Control.Monad.Writer (Writer, writer, runWriter)
import qualified Data.Set as Set

import Prelude ()
import Prelude.Compat

-- | The most general unifier is a substitution and a set of constraints
-- on bound variables.
type MGU = (Subst,[Prop])

type Result a = Writer [(Path,UnificationError)] a

runResult :: Result a -> (a, [(Path,UnificationError)])
runResult = runWriter

data UnificationError
  = UniTypeMismatch Type Type
  | UniKindMismatch Kind Kind
  | UniTypeLenMismatch Int Int
  | UniRecursive TVar Type
  | UniNonPolyDepends TVar [TParam]
  | UniNonPoly TVar Type

uniError :: Path -> UnificationError -> Result MGU
uniError p e = writer (emptyMGU, [(p,e)])


newtype Path = Path [PathElement]
  deriving (Show,Generic,NFData)

data PathElement =
    TConArg     TC      Int
  | TNominalArg NominalType Int
  | TRecArg     Ident
  deriving (Show,Generic,NFData)

rootPath :: Path
rootPath = Path []

isRootPath :: Path -> Bool
isRootPath (Path xs) = null xs

extPath :: Path -> PathElement -> Path
extPath (Path xs) x = Path (x : xs)


emptyMGU :: MGU
emptyMGU = (emptySubst, [])

doMGU :: Type -> Type -> Result MGU
doMGU t1 t2 = mgu rootPath t1 t2

mgu :: Path -> Type -> Type -> Result MGU

mgu _ (TUser c1 ts1 _) (TUser c2 ts2 _)
  | c1 == c2 && ts1 == ts2  = return emptyMGU

mgu p (TVar x) t     = bindVar p x t
mgu p t (TVar x)     = bindVar p x t

mgu p (TUser _ _ t1) t2 = mgu p t1 t2
mgu p t1 (TUser _ _ t2) = mgu p t1 t2

mgu p (TCon (TC tc1) ts1) (TCon (TC tc2) ts2)
  | tc1 == tc2 =
    let paths = [ extPath p (TConArg tc1 i) | i <- [ 0 .. ] ]
    in mguMany p paths ts1 ts2

mgu _ (TCon (TF f1) ts1) (TCon (TF f2) ts2)
  | f1 == f2 && ts1 == ts2  = return emptyMGU

-- XXX: here we loose the information about where the constarint came from
mgu _ t1 t2
  | TCon (TF _) _ <- t1, isNum, k1 == k2 = return (emptySubst, [t1 =#= t2])
  | TCon (TF _) _ <- t2, isNum, k1 == k2 = return (emptySubst, [t1 =#= t2])
  where
  k1 = kindOf t1
  k2 = kindOf t2

  isNum = k1 == KNum

mgu p (TRec fs1) (TRec fs2)
  | fieldSet fs1 == fieldSet fs2 =
    let paths = [ extPath p (TRecArg i) | (i,_) <- canonicalFields fs1 ]
    in mguMany p paths (recordElements fs1) (recordElements fs2)

mgu p (TNominal ntx xs) (TNominal nty ys)
  | ntx == nty =
    let paths = [ extPath p (TNominalArg ntx i) | i <- [ 0 .. ] ]
    in mguMany p paths xs ys

mgu p t1 t2
  | not (k1 == k2)  = uniError p $ UniKindMismatch k1 k2
  | otherwise       = uniError p $ UniTypeMismatch t1 t2
  where
  k1 = kindOf t1
  k2 = kindOf t2


-- XXX: could pass the path to the lists themselvs
mguMany :: Path -> [Path] -> [Type] -> [Type] -> Result MGU
mguMany _ _ [] [] = return emptyMGU
mguMany p (p1:ps) (t1 : ts1) (t2 : ts2) =
  do (su1,ps1) <- mgu p1 t1 t2
     (su2,ps2) <- mguMany p ps (apSubst su1 ts1) (apSubst su1 ts2)
     return (su2 @@ su1, ps1 ++ ps2)
mguMany p _ t1 t2 = uniError p $ UniTypeLenMismatch (length t1) (length t2)
-- XXX: I think by this point the types should have been kind checked,
-- so there should be no mismatches with the lengths...


bindVar :: Path -> TVar -> Type -> Result MGU

bindVar _ x (tNoUser -> TVar y)
  | x == y                      = return emptyMGU

bindVar p v@(TVBound {})
          (tNoUser -> TVar v1@(TVFree {})) = bindVar p v1 (TVar v)

bindVar p v@(TVBound {}) t
  | k == kindOf t = if k == KNum
                       then return (emptySubst, [TVar v =#= t])
                       else uniError p $ UniNonPoly v t
  | otherwise     = uniError p $ UniKindMismatch k (kindOf t)
  where k = kindOf v

bindVar _ x@(TVFree _ xk xscope _) (tNoUser -> TVar y@(TVFree _ yk yscope _))
  | xscope `Set.isProperSubsetOf` yscope, xk == yk =
    return (uncheckedSingleSubst y (TVar x), [])
    -- In this case, we can add the reverse binding y ~> x to the
    -- substitution, but the instantiation x ~> y would be forbidden
    -- because it would allow y to escape from its scope.

bindVar p x t =
  case singleSubst x t of
    Left SubstRecursive
      | kindOf x == KType -> uniError p $ UniRecursive x t
      | otherwise -> return (emptySubst, [TVar x =#= t])
    Left (SubstEscaped tps) ->
      uniError p $ UniNonPolyDepends x tps
    Left (SubstKindMismatch k1 k2) ->
      uniError p $ UniKindMismatch k1 k2
    Right su ->
      return (su, [])


--------------------------------------------------------------------------------

ppPathEl :: PathElement -> Int -> (Int -> Doc) -> Doc
ppPathEl el prec k =
  case el of
    TRecArg l -> braces (pp l <+> ":" <+> k 0 <.> comma <+> "…")

    TConArg tc n ->
      case tc of

       TCSeq -> optParens (prec > 4)
                if n == 0 then brackets (k 0) <+> "_"
                          else brackets "_" <+> (k 4)

       TCFun -> optParens (prec > 1)
                if n == 0 then k 2 <+> "->" <+> "_"
                          else "_" <+> "->" <+> k 1

       TCTuple i  -> parens (commaSep (before ++ [k 0] ++ after))
          where before = replicate n "_"
                after  = replicate (i - n - 1) "_"

       _ -> justPrefix (kindArity (kindOf tc)) (pp tc) n

    TNominalArg nt n ->
      justPrefix (length (ntParams nt)) (pp (nameIdent (ntName nt))) n

  where
  justPrefix arity fun n =
    optParens (prec > 3) (fun <+> hsep (before ++ [k 5] ++ after))
    where before = replicate n "_"
          after  = replicate (arity - n - 1) "_"

  kindArity ki =
    case ki of
      _ :-> k1 -> 1 + kindArity k1
      _        -> 0

instance PP Path where
  ppPrec prec0 (Path ps0) = go (reverse ps0) prec0
    where
    go ps prec =
      case ps of
        []       -> "ERROR"
        p : more -> ppPathEl p prec (go more)

