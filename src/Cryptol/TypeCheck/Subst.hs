-- |
-- Module      :  Cryptol.TypeCheck.Subst
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE Safe #-}
module Cryptol.TypeCheck.Subst
  ( Subst
  , emptySubst
  , SubstError(..)
  , singleSubst
  , singleTParamSubst
  , uncheckedSingleSubst
  , (@@)
  , defaultingSubst
  , listSubst
  , listParamSubst
  , isEmptySubst
  , FVS(..)
  , apSubstMaybe
  , TVars(..)
  , apSubstTypeMapKeys
  , substBinds
  , applySubstToVar
  , substToList
  , fmap', (!$), (.$)
  , mergeDistinctSubst
  ) where

import           Data.Maybe
import           Data.Either (partitionEithers)
import qualified Data.Map.Strict as Map
import qualified Data.IntMap as IntMap

import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Subst.Type
import Cryptol.TypeCheck.TypeMap
import qualified Cryptol.TypeCheck.SimpleSolver as Simp

(@@) :: Subst -> Subst -> Subst
s2 @@ s1
  | isEmptySubst s2 =
    if suDefaulting s1 || not (suDefaulting s2) then
      s1
    else
      s1{ suDefaulting = True }

s2 @@ s1 =
  S { suFreeMap = IntMap.map (fmap (apSubst s2)) (suFreeMap s1) `IntMap.union` suFreeMap s2
    , suBoundMap = IntMap.map (fmap (apSubst s2)) (suBoundMap s1) `IntMap.union` suBoundMap s2
    , suDefaulting = suDefaulting s1 || suDefaulting s2
    }



infixl 0 !$
infixl 0 .$

-- | Left-associative variant of the strict application operator '$!'.
(!$) :: (a -> b) -> a -> b
(!$) = ($!)

-- | Left-associative variant of the application operator '$'.
(.$) :: (a -> b) -> a -> b
(.$) = ($)

-- Only used internally to define fmap'.
data Done a = Done a
  deriving (Functor, Foldable, Traversable)

instance Applicative Done where
  pure x = Done x
  Done f <*> Done x = Done (f x)

-- | Strict variant of 'fmap'.
fmap' :: Traversable t => (a -> b) -> t a -> t b
fmap' f xs = case traverse f' xs of Done y -> y
  where f' x = Done $! f x

-- | Apply a substitution.  Returns `Nothing` if nothing changed.
-- Performs simplification on the result.
apSubstMaybe :: Subst -> Type -> Maybe Type
apSubstMaybe = apSubstMaybe' (Simp.simplify mempty)

applySubstToVar :: Subst -> TVar -> Maybe Type
applySubstToVar = applySubstToVar' apSubstMaybe



class TVars t where
  apSubst :: Subst -> t -> t
  -- ^ Replaces free variables. To prevent space leaks when used with
  -- large 'Subst' values, every instance of 'apSubst' should satisfy
  -- a strictness property: Forcing evaluation of @'apSubst' s x@
  -- should also force the evaluation of all recursive calls to
  -- @'apSubst' s@. This ensures that unevaluated thunks will not
  -- cause 'Subst' values to be retained on the heap.

instance TVars t => TVars (Maybe t) where
  apSubst s = fmap' (apSubst s)

instance TVars t => TVars [t] where
  apSubst s = fmap' (apSubst s)

instance (TVars s, TVars t) => TVars (s,t) where
  apSubst s (x, y) = (,) !$ apSubst s x !$ apSubst s y

instance TVars Type where
  apSubst su ty = fromMaybe ty (apSubstMaybe su ty)

instance (Traversable m, TVars a) => TVars (List m a) where
  apSubst su = fmap' (apSubst su)

instance TVars a => TVars (TypeMap a) where
  apSubst su = fmap' (apSubst su)


-- | Apply the substitution to the keys of a type map.
apSubstTypeMapKeys :: Subst -> TypeMap a -> TypeMap a
apSubstTypeMapKeys su = go (\_ x -> x) id
  where

  go :: (a -> a -> a) -> (a -> a) -> TypeMap a -> TypeMap a
  go merge atNode TM { .. } = foldl addKey tm' tys
    where
    addKey tm (ty,a) = insertWithTM merge ty a tm

    tm' = TM { tvar = Map.fromList   vars
             , tcon = fmap (lgo merge atNode) tcon
             , trec = fmap (lgo merge atNode) trec
             , tnominal = fmap (lgo merge atNode) tnominal
             }

    -- partition out variables that have been replaced with more specific types
    (vars,tys) = partitionEithers
                 [ case applySubstToVar su v of
                     Just ty -> Right (ty,a')
                     Nothing -> Left  (v, a')

                 | (v,a) <- Map.toList tvar
                 , let a' = atNode a
                 ]

  lgo :: (a -> a -> a) -> (a -> a) -> List TypeMap a -> List TypeMap a
  lgo merge atNode k = k { nil  = fmap atNode (nil k)
                         , cons = go (unionTM merge)
                                     (lgo merge atNode)
                                     (cons k)
                         }

instance TVars a => TVars (Map.Map k a) where
  -- NB, strict map
  apSubst su = Map.map (apSubst su)

instance TVars TySyn where
  apSubst su (TySyn nm params props t doc) =
    (\props' t' -> TySyn nm params props' t' doc)
      !$ apSubst su props !$ apSubst su t

{- | This instance does not need to worry about bound variable
capture, because we rely on the 'Subst' datatype invariant to ensure
that variable scopes will be properly preserved. -}

instance TVars Schema where
  apSubst su (Forall xs ps t) =
    Forall xs !$ (map doProp ps) !$ (apSubst su t)
    where
    doProp = pAnd . pSplitAnd . apSubst su
    {- NOTE: when applying a substitution to the predicates of a schema
       we preserve the number of predicate, even if some of them became
       "True" or and "And".  This is to accomodate applying substitution
       to already type checked code (e.g., when instantiating a functor)
       where the predictes in the schema need to match the corresponding
       EProofAbs in the term.
    -}

instance TVars Expr where
  apSubst su = go
    where
    go expr =
      case expr of
        ELocated r e  -> ELocated r !$ (go e)
        EApp e1 e2    -> EApp !$ (go e1) !$ (go e2)
        EAbs x t e1   -> EAbs x !$ (apSubst su t) !$ (go e1)
        ETAbs a e     -> ETAbs a !$ (go e)
        ETApp e t     -> ETApp !$ (go e) !$ (apSubst su t)
        EProofAbs p e -> EProofAbs !$ p' !$ (go e)
          where p' = pAnd (pSplitAnd (apSubst su p))
          {- NOTE: we used to panic if `pSplitAnd` didn't return a single result.
          It is useful to avoid the panic if applying the substitution to
          already type checked code (e.g., when we are instantitaing a
          functor).  In that case, we don't have the option to modify the
          `EProofAbs` because we'd have to change all call sites, but things might
          simplify because of the extra info in the substitution. -}


        EProofApp e   -> EProofApp !$ (go e)

        EVar {}       -> expr

        ETuple es     -> ETuple !$ (fmap' go es)
        ERec fs       -> ERec !$ (fmap' go fs)
        ESet ty e x v -> ESet !$ (apSubst su ty) !$ (go e) .$ x !$ (go v)
        EList es t    -> EList !$ (fmap' go es) !$ (apSubst su t)
        ESel e s      -> ESel !$ (go e) .$ s
        EComp len t e mss -> EComp !$ (apSubst su len) !$ (apSubst su t) !$ (go e) !$ (apSubst su mss)
        EIf e1 e2 e3  -> EIf !$ (go e1) !$ (go e2) !$ (go e3)
        ECase e as d  -> ECase !$ go e !$ (apSubst su <$> as)
                                       !$ (apSubst su <$> d)

        EWhere e ds   -> EWhere !$ (go e) !$ (apSubst su ds)

        EPropGuards guards ty -> ePropGuards
          !$ (\(props, e) -> (apSubst su `fmap'` props, go e)) `fmap'` guards
          !$ apSubst su ty

instance TVars CaseAlt where
  apSubst su (CaseAlt xs e) = CaseAlt !$ [(x,apSubst su t) | (x,t) <- xs]
                                      !$ apSubst su e
    -- XXX: not as strict as the rest

instance TVars Match where
  apSubst su (From x len t e) = From x !$ (apSubst su len) !$ (apSubst su t) !$ (apSubst su e)
  apSubst su (Let b)      = Let !$ (apSubst su b)

instance TVars DeclGroup where
  apSubst su (NonRecursive d) = NonRecursive !$ (apSubst su d)
  apSubst su (Recursive ds)   = Recursive !$ (apSubst su ds)

instance TVars Decl where
  apSubst su d =
    let !sig' = apSubst su (dSignature d)
        !def' = apSubst su (dDefinition d)
    in d { dSignature = sig', dDefinition = def' }

instance TVars DeclDef where
  apSubst su (DExpr e)       = DExpr !$ (apSubst su e)
  apSubst _  DPrim           = DPrim
  apSubst su (DForeign t me) = DForeign t !$ apSubst su me

-- WARNING: This applies the substitution only to the declarations.
instance TVars (ModuleG names) where
  apSubst su m =
    let !decls' = apSubst su (mDecls m)
        !funs'  = apSubst su <$> mFunctors m
    in m { mDecls = decls', mFunctors = funs' }

-- WARNING: This applies the substitution only to the declarations in modules.
instance TVars TCTopEntity where
  apSubst su ent =
    case ent of
      TCTopModule m -> TCTopModule (apSubst su m)
      TCTopSignature {} -> ent
