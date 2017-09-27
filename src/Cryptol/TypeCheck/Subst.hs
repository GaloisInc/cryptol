-- |
-- Module      :  $Header$
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

data Subst = S { suMap :: !(Map.Map TVar Type)
               , suDefaulting :: !Bool
               }
                  deriving Show

emptySubst :: Subst
emptySubst = S { suMap = Map.empty, suDefaulting = False }

singleSubst :: TVar -> Type -> Subst
singleSubst x t = S { suMap = Map.singleton x t, suDefaulting = False }

(@@) :: Subst -> Subst -> Subst
s2 @@ s1
  | Map.null (suMap s2) =
    if suDefaulting s1 || not (suDefaulting s2) then
      s1
    else
      s1{ suDefaulting = True }

s2 @@ s1 = S { suMap = Map.map (apSubst s2) (suMap s1) `Map.union` suMap s2
             , suDefaulting = suDefaulting s1 || suDefaulting s2
             }


defaultingSubst :: Subst -> Subst
defaultingSubst s = s { suDefaulting = True }

-- | Makes a substitution out of a list.
-- WARNING: We do not validate the list in any way, so the caller should
-- ensure that we end up with a valid (e.g., idempotent) substitution.
listSubst :: [(TVar,Type)] -> Subst
listSubst xs
  | null xs   = emptySubst
  | otherwise = S { suMap = Map.fromList xs, suDefaulting = False }

isEmptySubst :: Subst -> Bool
isEmptySubst su = Map.null $ suMap su

-- Returns the empty set if this is a deaulting substitution
substBinds :: Subst -> Set TVar
substBinds su
  | suDefaulting su = Set.empty
  | otherwise       = Map.keysSet $ suMap su

substToList :: Subst -> [(TVar,Type)]
substToList s
  | suDefaulting s = panic "substToList" ["Defaulting substitution."]
  | otherwise = Map.toList (suMap s)

instance PP (WithNames Subst) where
  ppPrec _ (WithNames s mp)
    | null els  = text "(empty substitution)"
    | otherwise = text "Substitution:" $$ nest 2 (vcat (map pp1 els))
    where pp1 (x,t) = ppWithNames mp x <+> text "=" <+> ppWithNames mp t
          els       = Map.toList (suMap s)

instance PP Subst where
  ppPrec n = ppWithNamesPrec IntMap.empty n





-- | Apply a substitution.  Returns `Nothing` if nothing changed.
apSubstMaybe :: Subst -> Type -> Maybe Type
apSubstMaybe su ty =
  case ty of
    TCon t ts ->
      do ss <- anyJust (apSubstMaybe su) ts
         case t of

           TF f ->
             Just $!
             case (f,ss) of
               (TCAdd,[t1,t2])               -> Simp.tAdd t1 t2
               (TCSub,[t1,t2])               -> Simp.tSub t1 t2
               (TCMul,[t1,t2])               -> Simp.tMul t1 t2
               (TCDiv,[t1,t2])               -> Simp.tDiv t1 t2
               (TCMod,[t1,t2])               -> Simp.tMod t1 t2
               (TCExp,[t1,t2])               -> Simp.tExp t1 t2
               (TCMin,[t1,t2])               -> Simp.tMin t1 t2
               (TCMax,[t1,t2])               -> Simp.tMax t1 t2
               (TCWidth,[t1])                -> Simp.tWidth t1
               (TCBlocks,[t1,t2])            -> Simp.tBlocks t1 t2
               (TCPadding,[t1,t2])           -> Simp.tPadding t1 t2
               (TCLenFromThen,[t1,t2,t3])    -> Simp.tLenFromThen t1 t2 t3
               (TCLenFromThenTo,[t1,t2,t3])  -> Simp.tLenFromThenTo t1 t2 t3
               _ -> panic "apSubstMaybe" ["Unexpected type function", show t]

           PC _ ->Just $! Simp.simplify Map.empty (TCon t ss)

           _ -> return (TCon t ss)

    TUser f ts t  -> do t1 <- apSubstMaybe su t
                        return (TUser f (map (apSubst su) ts) t1)
    TRec fs       -> TRec `fmap` anyJust fld fs
      where fld (x,t) = do t1 <- apSubstMaybe su t
                           return (x,t1)
    TVar x -> applySubstToVar su x


applySubstToVar :: Subst -> TVar -> Maybe Type
applySubstToVar su x =
  case Map.lookup x (suMap su) of
    Just t  -> Just t
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


{- | WARNING: This instance assumes that the quantified variables in the
types in the substitution will not get captured by the quantified variables.
This is reasonable because there should be no shadowing of quantified
variables but, just in case, we make a sanity check and panic if somehow
capture did occur. -}

instance TVars Schema where
  apSubst su sch@(Forall xs ps t)
    | Set.null captured = Forall xs (apSubst su ps) (apSubst su t)
    | otherwise = panic "Cryptol.TypeCheck.Subst.apSubst (Schema)"
                    [ "Captured quantified variables:"
                    , "Substitution: " ++ show (brackets (commaSep (map ppBinding su_binds)))
                    , "Schema:       " ++ show (pp sch)
                    , "Variables:    " ++ show (commaSep (map pp (Set.toList captured)))
                    ]
    where
    ppBinding (v,x) = pp v <+> text ":=" <+> pp x
    captured = Set.fromList (map tpVar xs)
               `Set.intersection`
               subVars
    su_binds = Map.toList $ suMap su
    used = fvs sch
    subVars = Set.unions
                $ map (fvs . applySubstToVar su)
                $ Set.toList used


instance TVars Expr where
  apSubst su = go
    where
    go expr =
      case expr of
        EApp e1 e2    -> EApp (go e1) (go e2)
        EAbs x t e1   -> EAbs x (apSubst su t) (go e1)
        ETAbs a e     -> ETAbs a (go e)
        ETApp e t     -> ETApp (go e) (apSubst su t)
        EProofAbs p e -> EProofAbs (apSubst su p) (go e)
        EProofApp e   -> EProofApp (go e)

        EVar {}       -> expr

        ETuple es     -> ETuple (map go es)
        ERec fs       -> ERec [ (f, go e) | (f,e) <- fs ]
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

