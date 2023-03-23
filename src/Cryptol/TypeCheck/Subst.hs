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
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
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
import           Data.Set (Set)
import qualified Data.Set as Set

import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.PP
import Cryptol.TypeCheck.TypeMap
import qualified Cryptol.TypeCheck.SimpType as Simp
import qualified Cryptol.TypeCheck.SimpleSolver as Simp
import Cryptol.Utils.Panic(panic)
import Cryptol.Utils.Misc (anyJust, anyJust2)

-- | A 'Subst' value represents a substitution that maps each 'TVar'
-- to a 'Type'.
--
-- Invariant 1: If there is a mapping from @TVFree _ _ tps _@ to a
-- type @t@, then @t@ must not mention (directly or indirectly) any
-- type parameter that is not in @tps@. In particular, if @t@ contains
-- a variable @TVFree _ _ tps2 _@, then @tps2@ must be a subset of
-- @tps@. This ensures that applying the substitution will not permit
-- any type parameter to escape from its scope.
--
-- Invariant 2: The substitution must be idempotent, in that applying
-- a substitution to any 'Type' in the map should leave that 'Type'
-- unchanged. In other words, 'Type' values in the range of a 'Subst'
-- should not mention any 'TVar' in the domain of the 'Subst'. In
-- particular, this implies that a substitution must not contain any
-- recursive variable mappings.
--
-- Invariant 3: The substitution must be kind correct: Each 'TVar' in
-- the substitution must map to a 'Type' of the same kind.

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

mergeDistinctSubst :: [Subst] -> Subst
mergeDistinctSubst sus =
  case sus of
    [] -> emptySubst
    _  -> foldr1 merge sus

  where
  merge s1 s2 = S { suFreeMap     = jn suFreeMap s1 s2
                  , suBoundMap    = jn suBoundMap s1 s2
                  , suDefaulting  = if suDefaulting s1 || suDefaulting s2
                                      then err
                                      else False
                  }

  err       = panic "mergeDistinctSubst" [ "Not distinct" ]
  bad _ _   = err
  jn f x y  = IntMap.unionWith bad (f x) (f y)






-- | Reasons to reject a single-variable substitution.
data SubstError
  = SubstRecursive
  -- ^ 'TVar' maps to a type containing the same variable.
  | SubstEscaped [TParam]
  -- ^ 'TVar' maps to a type containing one or more out-of-scope bound variables.
  | SubstKindMismatch Kind Kind
  -- ^ 'TVar' maps to a type with a different kind.

singleSubst :: TVar -> Type -> Either SubstError Subst
singleSubst x t
  | kindOf x /= kindOf t   = Left (SubstKindMismatch (kindOf x) (kindOf t))
  | x `Set.member` fvs t   = Left SubstRecursive
  | not (Set.null escaped) = Left (SubstEscaped (Set.toList escaped))
  | otherwise              = Right (uncheckedSingleSubst x t)
  where
    escaped =
      case x of
        TVBound _ -> Set.empty
        TVFree _ _ scope _ -> freeParams t `Set.difference` scope

uncheckedSingleSubst :: TVar -> Type -> Subst
uncheckedSingleSubst v@(TVFree i _ _tps _) t =
  S { suFreeMap = IntMap.singleton i (v, t)
    , suBoundMap = IntMap.empty
    , suDefaulting = False
    }
uncheckedSingleSubst v@(TVBound tp) t =
  S { suFreeMap = IntMap.empty
    , suBoundMap = IntMap.singleton (tpUnique tp) (v, t)
    , suDefaulting = False
    }

singleTParamSubst :: TParam -> Type -> Subst
singleTParamSubst tp t = uncheckedSingleSubst (TVBound tp) t

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
apSubstMaybe :: Subst -> Type -> Maybe Type
apSubstMaybe su ty =
  case ty of
    TCon t ts ->
      do ss <- anyJust (apSubstMaybe su) ts
         case t of
           TF _ -> Just $! Simp.tCon t ss
           PC _ -> Just $! Simp.simplify mempty (TCon t ss)
           _    -> Just (TCon t ss)

    TUser f ts t ->
      do (ts1, t1) <- anyJust2 (anyJust (apSubstMaybe su)) (apSubstMaybe su) (ts, t)
         Just (TUser f ts1 t1)

    TRec fs -> TRec `fmap` (anyJust (apSubstMaybe su) fs)
    TNewtype nt ts -> TNewtype nt `fmap` anyJust (apSubstMaybe su) ts
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
    Just t
      | suDefaulting su -> Just $! apSubst su t
      | otherwise       -> Just t
    Nothing
      | suDefaulting su -> Just $! defaultFreeVar x
      | otherwise       -> Nothing

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
             , tnewtype = fmap (lgo merge atNode) tnewtype
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
  apSubst su m = Map.map (apSubst su) m

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

        EWhere e ds   -> EWhere !$ (go e) !$ (apSubst su ds)

        EPropGuards guards ty -> EPropGuards !$ (\(props, e) -> (apSubst su `fmap'` props, apSubst su e)) `fmap'` guards .$ ty

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
  apSubst su (DExpr e)    = DExpr !$ (apSubst su e)
  apSubst _  DPrim        = DPrim
  apSubst _  (DForeign t) = DForeign t

-- WARNING: This applies the substitution only to the declarations.
instance TVars Module where
  apSubst su m =
    let !decls' = apSubst su (mDecls m)
    in m { mDecls = decls' }

-- WARNING: This applies the substitution only to the declarations in modules.
instance TVars TCTopEntity where
  apSubst su ent =
    case ent of
      TCTopModule m -> TCTopModule (apSubst su m)
      TCTopSignature {} -> ent
