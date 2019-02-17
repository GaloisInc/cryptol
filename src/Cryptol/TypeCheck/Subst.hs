-- |
-- Module      :  Cryptol.TypeCheck.Subst
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE Safe #-}
module Cryptol.TypeCheck.Subst
  ( Subst
  , emptySubst
  , singleSubst
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
  ) where

import           Data.Maybe
import           Data.Either (partitionEithers)
import qualified Data.Map.Strict as Map
import qualified Data.IntMap as IntMap
import           Data.Set (Set)
import qualified Data.Set as Set

import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.PP
import Cryptol.TypeCheck.TypeMap
import qualified Cryptol.TypeCheck.SimpType as Simp
import qualified Cryptol.TypeCheck.SimpleSolver as Simp
import Cryptol.Utils.Panic(panic)
import Cryptol.Utils.Misc(anyJust)

-- | A 'Subst' value represents a substitution that maps each 'TVar'
-- to a 'Type'.
--
-- Invariant: If there is a mapping from @TVFree _ _ tps _@ to a type
-- @t@, then @t@ must not mention (directly or indirectly) any type
-- parameter that is not in @tps@. In particular, if @t@ contains a
-- variable @TVFree _ _ tps2 _@, then @tps2@ must be a subset of
-- @tps@. This ensures that applying the substitution will not permit
-- any type parameter to escape from its scope.

data Subst = S { suFreeMap :: !(IntMap.IntMap (TVar, Type))
               , suBoundMap :: !(IntMap.IntMap (TVar, Type))
               , suDefaulting :: !Bool
               }
                  deriving Show

emptySubst :: Subst
emptySubst =
  S { suFreeMap = IntMap.empty
    , suBoundMap = IntMap.empty
    , suDefaulting = False
    }

singleSubst :: TVar -> Type -> Subst
singleSubst v@(TVFree i _ _tps _) t =
  S { suFreeMap = IntMap.singleton i (v, t)
    , suBoundMap = IntMap.empty
    , suDefaulting = False
    }
singleSubst v@(TVBound tp) t =
  S { suFreeMap = IntMap.empty
    , suBoundMap = IntMap.singleton (tpUnique tp) (v, t)
    , suDefaulting = False
    }

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

-- | A defaulting substitution maps all otherwise-unmapped free
-- variables to a kind-appropriate default type (@Bit@ for value types
-- and @0@ for numeric types).
defaultingSubst :: Subst -> Subst
defaultingSubst s = s { suDefaulting = True }

-- | Makes a substitution out of a list.
-- WARNING: We do not validate the list in any way, so the caller should
-- ensure that we end up with a valid (e.g., idempotent) substitution.
listSubst :: [(TVar, Type)] -> Subst
listSubst xs
  | null xs   = emptySubst
  | otherwise = S { suFreeMap = IntMap.fromList frees
                  , suBoundMap = IntMap.fromList bounds
                  , suDefaulting = False }
  where
    (frees, bounds) = partitionEithers (map classify xs)
    classify x =
      case fst x of
        TVFree i _ _ _ -> Left (i, x)
        TVBound tp -> Right (tpUnique tp, x)

-- | Makes a substitution out of a list.
-- WARNING: We do not validate the list in any way, so the caller should
-- ensure that we end up with a valid (e.g., idempotent) substitution.
listParamSubst :: [(TParam, Type)] -> Subst
listParamSubst xs
  | null xs   = emptySubst
  | otherwise = S { suFreeMap = IntMap.empty
                  , suBoundMap = IntMap.fromList bounds
                  , suDefaulting = False }
  where
    bounds = [ (tpUnique tp, (TVBound tp, t)) | (tp, t) <- xs ]

isEmptySubst :: Subst -> Bool
isEmptySubst su = IntMap.null (suFreeMap su) && IntMap.null (suBoundMap su)

-- Returns the empty set if this is a defaulting substitution
substBinds :: Subst -> Set TVar
substBinds su
  | suDefaulting su = Set.empty
  | otherwise       = Set.fromList (map fst (assocsSubst su))

substToList :: Subst -> [(TVar, Type)]
substToList s
  | suDefaulting s = panic "substToList" ["Defaulting substitution."]
  | otherwise = assocsSubst s

assocsSubst :: Subst -> [(TVar, Type)]
assocsSubst s = frees ++ bounds
  where
    frees = IntMap.elems (suFreeMap s)
    bounds = IntMap.elems (suBoundMap s)

instance PP (WithNames Subst) where
  ppPrec _ (WithNames s mp)
    | null els  = text "(empty substitution)"
    | otherwise = text "Substitution:" $$ nest 2 (vcat (map pp1 els))
    where pp1 (x,t) = ppWithNames mp x <+> text "=" <+> ppWithNames mp t
          els       = assocsSubst s

instance PP Subst where
  ppPrec n = ppWithNamesPrec IntMap.empty n





-- | Apply a substitution.  Returns `Nothing` if nothing changed.
apSubstMaybe :: Subst -> Type -> Maybe Type
apSubstMaybe su ty =
  case ty of
    TCon t ts ->
      do ss <- anyJust (apSubstMaybe su) ts
         case t of
           TF _ -> Just $! Simp.tCon t ss
           PC _ -> Just $! Simp.simplify Map.empty (TCon t ss)
           _    -> Just (TCon t ss)

    TUser f ts t  -> do t1 <- apSubstMaybe su t
                        return (TUser f (map (apSubst su) ts) t1)
    TRec fs       -> TRec `fmap` anyJust fld fs
      where fld (x,t) = do t1 <- apSubstMaybe su t
                           return (x,t1)
    TVar x -> applySubstToVar su x

lookupSubst :: TVar -> Subst -> Maybe Type
lookupSubst x su =
  fmap snd $
  case x of
    TVFree i _ _ _ -> IntMap.lookup i (suFreeMap su)
    TVBound tp -> IntMap.lookup (tpUnique tp) (suBoundMap su)

applySubstToVar :: Subst -> TVar -> Maybe Type
applySubstToVar su x =
  case lookupSubst x su of
    -- For a defaulting substitution, we must recurse in order to
    -- replace unmapped free vars with default types.
    Just t  -> Just (if suDefaulting su then apSubst su t else t)
    Nothing
      | suDefaulting su -> Just $! defaultFreeVar x
      | otherwise       -> Nothing

class TVars t where
  apSubst :: Subst -> t -> t      -- ^ replaces free vars

instance TVars t => TVars (Maybe t) where
  apSubst s       = fmap (apSubst s)

instance TVars t => TVars [t] where
  apSubst s       = map (apSubst s)

instance (TVars s, TVars t) => TVars (s,t) where
  apSubst s (x,y)       = (apSubst s x, apSubst s y)

instance TVars Type where
  apSubst su ty = fromMaybe ty (apSubstMaybe su ty)

-- | Pick types for unconstrained unification variables.
defaultFreeVar :: TVar -> Type
defaultFreeVar x@(TVBound {}) = TVar x
defaultFreeVar (TVFree _ k _ d) =
  case k of
    KType -> tBit
    KNum  -> tNum (0 :: Int)
    _     -> panic "Cryptol.TypeCheck.Subst.defaultFreeVar"
                  [ "Free variable of unexpected kind."
                  , "Source: " ++ show d
                  , "Kind: " ++ show (pp k) ]

instance (Functor m, TVars a) => TVars (List m a) where
  apSubst su = fmap (apSubst su)

instance TVars a => TVars (TypeMap a) where
  apSubst su = fmap (apSubst su)


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


{- | This instance does not need to worry about bound variable
capture, because we rely on the 'Subst' datatype invariant to ensure
that variable scopes will be properly preserved. -}

instance TVars Schema where
  apSubst su (Forall xs ps t) = Forall xs (concatMap pSplitAnd (apSubst su ps))
                                          (apSubst su t)

instance TVars Expr where
  apSubst su = go
    where
    go expr =
      case expr of
        EApp e1 e2    -> EApp (go e1) (go e2)
        EAbs x t e1   -> EAbs x (apSubst su t) (go e1)
        ETAbs a e     -> ETAbs a (go e)
        ETApp e t     -> ETApp (go e) (apSubst su t)
        EProofAbs p e -> EProofAbs hmm (go e)
          where hmm = case pSplitAnd (apSubst su p) of
                        [p1] -> p1
                        res -> panic "apSubst@EProofAbs"
                                [ "Predicate split or disappeared after"
                                , "we applied a substitution."
                                , "Predicate:"
                                , show (pp p)
                                , "Became:"
                                , show (map pp res)
                                , "subst:"
                                , show (pp su)
                                ]

        EProofApp e   -> EProofApp (go e)

        EVar {}       -> expr

        ETuple es     -> ETuple (map go es)
        ERec fs       -> ERec [ (f, go e) | (f,e) <- fs ]
        ESet e x v    -> ESet (go e) x (go v)
        EList es t    -> EList (map go es) (apSubst su t)
        ESel e s      -> ESel (go e) s
        EComp len t e mss -> EComp (apSubst su len) (apSubst su t) (go e) (apSubst su mss)
        EIf e1 e2 e3  -> EIf (go e1) (go e2) (go e3)

        EWhere e ds   -> EWhere (go e) (apSubst su ds)

instance TVars Match where
  apSubst su (From x len t e) = From x (apSubst su len) (apSubst su t) (apSubst su e)
  apSubst su (Let b)      = Let (apSubst su b)

instance TVars DeclGroup where
  apSubst su (NonRecursive d) = NonRecursive (apSubst su d)
  apSubst su (Recursive ds)   = Recursive (apSubst su ds)

instance TVars Decl where
  apSubst su d          = d { dSignature  = apSubst su (dSignature d)
                            , dDefinition = apSubst su (dDefinition d)
                            }

instance TVars DeclDef where
  apSubst su (DExpr e) = DExpr (apSubst su e)
  apSubst _  DPrim     = DPrim

instance TVars Module where
  apSubst su m = m { mDecls = apSubst su (mDecls m) }

