{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
module Cryptol.TypeCheck.Subst.Type
  ( Subst(..)
  , emptySubst
  , SubstError(..)
  , singleSubst
  , singleTParamSubst
  , uncheckedSingleSubst
  , defaultingSubst
  , listSubst
  , listParamSubst
  , isEmptySubst
  , substBinds
  , substToList
  , mergeDistinctSubst
  , apSubstMaybe'
  , applySubstToVar'
  , apSubstNoSimp
  ) where

import           Data.Maybe
import           Data.Either (partitionEithers)
import qualified Data.IntMap as IntMap
import           Data.Set (Set)
import qualified Data.Set as Set

import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.PP
import qualified Cryptol.TypeCheck.SimpType as Simp
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.Misc (anyJust, anyJust2, anyJust3)

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
-- The @Prop -> Prop@ function is how to simplify the result if it is a
-- predicate.
apSubstMaybe' :: (Prop -> Prop) -> Subst -> Type -> Maybe Type
apSubstMaybe' simpProp su ty =
  case ty of
    TCon t ts ->
      do ss <- anyJust (apSubstMaybe' simpProp su) ts
         case t of
           TF _ -> Just $! Simp.tCon t ss
           PC _ -> Just $! simpProp (TCon t ss)
           _    -> Just (TCon t ss)

    TUser f ts t ->
      do (ts1, t1) <- anyJust2 (anyJust (apSubstMaybe' simpProp su))
                               (apSubstMaybe' simpProp su)
                               (ts, t)
         Just (TUser f ts1 t1)

    TRec fs -> TRec `fmap` (anyJust (apSubstMaybe' simpProp su) fs)

    {- We apply the substitution to nominal types as well, because it might
    contain module parameters, which need to be substituted when
    instantiating a functor. -}
    TNominal nt ts ->
      uncurry TNominal <$> anyJust2 (applySubstToNominalType' simpProp su)
                                    (anyJust (apSubstMaybe' simpProp su))
                                    (nt,ts)

    TVar x -> applySubstToVar' (apSubstMaybe' simpProp) su x

-- | Apply a substitution without simplifying the result when it is a predicate.
apSubstNoSimp :: Subst -> Type -> Type
apSubstNoSimp su ty = fromMaybe ty (apSubstMaybe' id su ty)

lookupSubst :: TVar -> Subst -> Maybe Type
lookupSubst x su =
  fmap snd $
  case x of
    TVFree i _ _ _ -> IntMap.lookup i (suFreeMap su)
    TVBound tp -> IntMap.lookup (tpUnique tp) (suBoundMap su)

applySubstToVar' :: (Subst -> Type -> Maybe Type) -> Subst -> TVar -> Maybe Type
applySubstToVar' substType su x =
  case lookupSubst x su of
    -- For a defaulting substitution, we must recurse in order to
    -- replace unmapped free vars with default types.
    Just t
      | suDefaulting su -> Just $! fromMaybe t (substType su t)
      | otherwise       -> Just t
    Nothing
      | suDefaulting su -> Just $! defaultFreeVar x
      | otherwise       -> Nothing

applySubstToNominalType' :: (Prop -> Prop)
                         -> Subst -> NominalType -> Maybe NominalType
applySubstToNominalType' simpProp su nt =
 do (cs,def,der) <- anyJust3 (anyJust (apSubstMaybe' simpProp su))
                             apSubstDef
                             (anyJust (anyJust (apSubstMaybe' simpProp su)))
                             (ntConstraints nt, ntDef nt, ntDeriving nt)
    pure nt { ntConstraints = cs, ntDef = def, ntDeriving = der }
  where
  apSubstDef d =
    case d of
      Struct c ->
        do fs <- anyJust (apSubstMaybe' simpProp su) (ntFields c)
           pure (Struct c { ntFields = fs })
      Enum cs -> Enum <$> anyJust apSubstCon cs
      Abstract -> pure Abstract

  apSubstCon c =
    do fs <- anyJust (apSubstMaybe' simpProp su) (ecFields c)
       pure c { ecFields = fs }

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
