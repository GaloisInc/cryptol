-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RecordWildCards #-}
module Cryptol.ModuleSystem.NamingEnv where

import Cryptol.ModuleSystem.Interface
import Cryptol.ModuleSystem.Name
import Cryptol.Parser.AST
import Cryptol.Parser.Position
import Cryptol.Utils.PP
import Cryptol.Utils.Panic (panic)

import Data.List (nub)
import Data.Maybe (catMaybes,fromMaybe)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import MonadLib (runId,Id)

import GHC.Generics (Generic)
import Control.DeepSeq

import Prelude ()
import Prelude.Compat


-- Naming Environment ----------------------------------------------------------

-- XXX The fixity environment should be removed, and Name should include fixity
-- information.
data NamingEnv = NamingEnv { neExprs :: !(Map.Map PName [Name])
                             -- ^ Expr renaming environment
                           , neTypes :: !(Map.Map PName [Name])
                             -- ^ Type renaming environment
                           , neFixity:: !(Map.Map Name Fixity)
                             -- ^ Expression-level fixity environment
                           } deriving (Show, Generic, NFData)

instance Monoid NamingEnv where
  mempty        =
    NamingEnv { neExprs  = Map.empty
              , neTypes  = Map.empty
              , neFixity = Map.empty }

  -- NOTE: merging the fixity maps is a special case that just prefers the left
  -- entry, as they're already keyed by a name with a unique
  mappend l r   =
    NamingEnv { neExprs  = Map.unionWith merge (neExprs  l) (neExprs  r)
              , neTypes  = Map.unionWith merge (neTypes  l) (neTypes  r)
              , neFixity = Map.union           (neFixity l) (neFixity r) }

  mconcat envs  =
    NamingEnv { neExprs  = Map.unionsWith merge (map neExprs  envs)
              , neTypes  = Map.unionsWith merge (map neTypes  envs)
              , neFixity = Map.unions           (map neFixity envs) }

  {-# INLINE mempty #-}
  {-# INLINE mappend #-}
  {-# INLINE mconcat #-}


-- | Merge two name maps, collapsing cases where the entries are the same, and
-- producing conflicts otherwise.
merge :: [Name] -> [Name] -> [Name]
merge xs ys | xs == ys  = xs
            | otherwise = nub (xs ++ ys)

-- | Generate a mapping from 'Ident' to 'Name' for a given naming environment.
toPrimMap :: NamingEnv -> PrimMap
toPrimMap NamingEnv { .. } = PrimMap { .. }
  where
  primDecls = Map.fromList [ (nameIdent n,n) | ns <- Map.elems neExprs
                                             , n  <- ns ]
  primTypes = Map.fromList [ (nameIdent n,n) | ns <- Map.elems neTypes
                                             , n  <- ns ]

-- | Generate a display format based on a naming environment.
toNameDisp :: NamingEnv -> NameDisp
toNameDisp NamingEnv { .. } = NameDisp display
  where
  display mn ident = Map.lookup (mn,ident) names

  -- only format declared names, as parameters don't need any special
  -- formatting.
  names = Map.fromList
     $ [ mkEntry pn mn (nameIdent n) | (pn,ns)     <- Map.toList neExprs
                                     , n           <- ns
                                     , Declared mn <- [nameInfo n] ]

    ++ [ mkEntry pn mn (nameIdent n) | (pn,ns)     <- Map.toList neTypes
                                     , n           <- ns
                                     , Declared mn <- [nameInfo n] ]

  mkEntry pn mn i = ((mn,i),fmt)
    where
    fmt = case getModName pn of
            Just ns -> Qualified ns
            Nothing -> UnQualified


-- | Produce sets of visible names for types and declarations.
--
-- NOTE: if entries in the NamingEnv would have produced a name clash, they will
-- be omitted from the resulting sets.
visibleNames :: NamingEnv -> ({- types -} Set.Set Name
                             ,{- decls -} Set.Set Name)

visibleNames NamingEnv { .. } = (types,decls)
  where
  types = Set.fromList [ n | [n] <- Map.elems neTypes ]
  decls = Set.fromList [ n | [n] <- Map.elems neExprs ]

-- | Qualify all symbols in a 'NamingEnv' with the given prefix.
qualify :: ModName -> NamingEnv -> NamingEnv
qualify pfx NamingEnv { .. } =
  NamingEnv { neExprs = Map.mapKeys toQual neExprs
            , neTypes = Map.mapKeys toQual neTypes
            , .. }

  where
  -- XXX we don't currently qualify fresh names
  toQual (Qual _ n)  = Qual pfx n
  toQual (UnQual n)  = Qual pfx n
  toQual n@NewName{} = n

filterNames :: (PName -> Bool) -> NamingEnv -> NamingEnv
filterNames p NamingEnv { .. } =
  NamingEnv { neExprs = Map.filterWithKey check neExprs
            , neTypes = Map.filterWithKey check neTypes
            , .. }
  where
  check :: PName -> a -> Bool
  check n _ = p n


-- | Singleton type renaming environment.
singletonT :: PName -> Name -> NamingEnv
singletonT qn tn = mempty { neTypes = Map.singleton qn [tn] }

-- | Singleton expression renaming environment.
singletonE :: PName -> Name -> NamingEnv
singletonE qn en = mempty { neExprs = Map.singleton qn [en] }

-- | Like mappend, but when merging, prefer values on the lhs.
shadowing :: NamingEnv -> NamingEnv -> NamingEnv
shadowing l r = NamingEnv
  { neExprs  = Map.union (neExprs  l) (neExprs  r)
  , neTypes  = Map.union (neTypes  l) (neTypes  r)
  , neFixity = Map.union (neFixity l) (neFixity r) }

travNamingEnv :: Applicative f => (Name -> f Name) -> NamingEnv -> f NamingEnv
travNamingEnv f ne = NamingEnv <$> neExprs' <*> neTypes' <*> pure (neFixity ne)
  where
    neExprs' = traverse (traverse f) (neExprs ne)
    neTypes' = traverse (traverse f) (neTypes ne)


data InModule a = InModule !ModName a
                  deriving (Functor,Traversable,Foldable,Show)


-- | Generate a 'NamingEnv' using an explicit supply.
namingEnv' :: BindsNames a => a -> Supply -> (NamingEnv,Supply)
namingEnv' a supply = runId (runSupplyT supply (runBuild (namingEnv a)))


newtype BuildNamingEnv = BuildNamingEnv { runBuild :: SupplyT Id NamingEnv }

instance Monoid BuildNamingEnv where
  mempty = BuildNamingEnv (pure mempty)

  mappend (BuildNamingEnv a) (BuildNamingEnv b) = BuildNamingEnv $
    do x <- a
       y <- b
       return (mappend x y)

  mconcat bs = BuildNamingEnv $
    do ns <- sequence (map runBuild bs)
       return (mconcat ns)

-- | Things that define exported names.
class BindsNames a where
  namingEnv :: a -> BuildNamingEnv

instance BindsNames NamingEnv where
  namingEnv env = BuildNamingEnv (return env)
  {-# INLINE namingEnv #-}

instance BindsNames a => BindsNames (Maybe a) where
  namingEnv = foldMap namingEnv
  {-# INLINE namingEnv #-}

instance BindsNames a => BindsNames [a] where
  namingEnv = foldMap namingEnv
  {-# INLINE namingEnv #-}

-- | Generate a type renaming environment from the parameters that are bound by
-- this schema.
instance BindsNames (Schema PName) where
  namingEnv (Forall ps _ _ _) = foldMap namingEnv ps
  {-# INLINE namingEnv #-}


-- | Interpret an import in the context of an interface, to produce a name
-- environment for the renamer, and a 'NameDisp' for pretty-printing.
interpImport :: Import -> IfaceDecls -> NamingEnv
interpImport imp publicDecls = qualified
  where

  -- optionally qualify names based on the import
  qualified | Just pfx <- iAs imp = qualify pfx restricted
            | otherwise           =             restricted

  -- restrict or hide imported symbols
  restricted
    | Just (Hiding ns) <- iSpec imp =
       filterNames (\qn -> not (getIdent qn `elem` ns)) public

    | Just (Only ns) <- iSpec imp =
       filterNames (\qn -> getIdent qn `elem` ns) public

    | otherwise = public

  -- generate the initial environment from the public interface, where no names
  -- are qualified
  public = unqualifiedEnv publicDecls


-- | Generate a naming environment from a declaration interface, where none of
-- the names are qualified.
unqualifiedEnv :: IfaceDecls -> NamingEnv
unqualifiedEnv IfaceDecls { .. } =
  mconcat [ exprs, tySyns, ntTypes, ntExprs
          , mempty { neFixity = Map.fromList fixity } ]
  where
  toPName n = mkUnqual (nameIdent n)

  exprs   = mconcat [ singletonE (toPName n) n | n <- Map.keys ifDecls ]
  tySyns  = mconcat [ singletonT (toPName n) n | n <- Map.keys ifTySyns ]
  ntTypes = mconcat [ singletonT (toPName n) n | n <- Map.keys ifNewtypes ]
  ntExprs = mconcat [ singletonE (toPName n) n | n <- Map.keys ifNewtypes ]

  fixity =
    catMaybes [ do f <- ifDeclFixity d; return (ifDeclName d,f)
              | d    <- Map.elems ifDecls ]


data ImportIface = ImportIface Import Iface

-- | Produce a naming environment from an interface file, that contains a
-- mapping only from unqualified names to qualified ones.
instance BindsNames ImportIface where
  namingEnv (ImportIface imp Iface { .. }) = BuildNamingEnv $
    return (interpImport imp ifPublic)
  {-# INLINE namingEnv #-}

-- | Introduce the name
instance BindsNames (InModule (Bind PName)) where
  namingEnv (InModule ns b) = BuildNamingEnv $
    do let Located { .. } = bName b
       n <- liftSupply (mkDeclared ns (getIdent thing) (bFixity b) srcRange)

       let fixity = case bFixity b of
             Just f  -> mempty { neFixity = Map.singleton n f }
             Nothing -> mempty

       return (singletonE thing n `mappend` fixity)

-- | Generate the naming environment for a type parameter.
instance BindsNames (TParam PName) where
  namingEnv TParam { .. } = BuildNamingEnv $
    do let range = fromMaybe emptyRange tpRange
       n <- liftSupply (mkParameter (getIdent tpName) range)
       return (singletonT tpName n)

-- | The naming environment for a single module.  This is the mapping from
-- unqualified names to fully qualified names with uniques.
instance BindsNames (Module PName) where
  namingEnv Module { .. } = foldMap (namingEnv . InModule ns) mDecls
    where
    ns = thing mName

instance BindsNames (InModule (TopDecl PName)) where
  namingEnv (InModule ns td) =
    case td of
      Decl d           -> namingEnv (InModule ns (tlValue d))
      TDNewtype d      -> namingEnv (InModule ns (tlValue d))
      DParameterType d -> namingEnv (InModule ns d)
      DParameterFun  d -> namingEnv (InModule ns d)
      Include _   -> mempty

instance BindsNames (InModule (ParameterFun PName)) where
  namingEnv (InModule ns ParameterFun { .. }) = BuildNamingEnv $
    do let Located { .. } = pfName
       ntName <- liftSupply (mkDeclared ns (getIdent thing) pfFixity srcRange)
       return (singletonE thing ntName)

instance BindsNames (InModule (ParameterType PName)) where
  namingEnv (InModule ns ParameterType { .. }) = BuildNamingEnv $
    -- XXX: we don't seem to have a fixity environment at the type level
    do let Located { .. } = ptName
       ntName <- liftSupply (mkDeclared ns (getIdent thing) Nothing srcRange)
       return (singletonT thing ntName)

-- NOTE: we use the same name at the type and expression level, as there's only
-- ever one name introduced in the declaration. The names are only ever used in
-- different namespaces, so there's no ambiguity.
instance BindsNames (InModule (Newtype PName)) where
  namingEnv (InModule ns Newtype { .. }) = BuildNamingEnv $
    do let Located { .. } = nName
       ntName <- liftSupply (mkDeclared ns (getIdent thing) Nothing srcRange)
       return (singletonT thing ntName `mappend` singletonE thing ntName)

-- | The naming environment for a single declaration.
instance BindsNames (InModule (Decl PName)) where
  namingEnv (InModule pfx d) = case d of
    DBind b -> BuildNamingEnv $
      do n <- mkName (bName b) (bFixity b)
         return (singletonE (thing (bName b)) n `mappend` fixity n b)

    DSignature ns _sig    -> foldMap qualBind ns
    DPragma ns _p         -> foldMap qualBind ns
    DType (TySyn lqn _ _) -> qualType lqn
    DLocated d' _         -> namingEnv (InModule pfx d')
    DPatBind _pat _e      -> panic "ModuleSystem" ["Unexpected pattern binding"]
    DFixity{}             -> panic "ModuleSystem" ["Unexpected fixity declaration"]

    where

    mkName ln fx =
      liftSupply (mkDeclared pfx (getIdent (thing ln)) fx (srcRange ln))

    qualBind ln = BuildNamingEnv $
      do n <- mkName ln Nothing
         return (singletonE (thing ln) n)

    qualType ln = BuildNamingEnv $
      do n <- mkName ln Nothing
         return (singletonT (thing ln) n)

    fixity n b =
      case bFixity b of
        Just f  -> mempty { neFixity = Map.singleton n f }
        Nothing -> mempty
