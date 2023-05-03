-- |
-- Module      :  Cryptol.ModuleSystem.NamingEnv
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
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE OverloadedStrings #-}
-- See Note [-Wincomplete-uni-patterns and irrefutable patterns] in Cryptol.TypeCheck.TypePat
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Cryptol.ModuleSystem.NamingEnv where

import Data.List (nub)
import Data.Maybe (fromMaybe,mapMaybe,maybeToList)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import Data.Semigroup
import MonadLib (runId,Id,StateT,runStateT,lift,sets_,forM_)

import GHC.Generics (Generic)
import Control.DeepSeq

import Prelude ()
import Prelude.Compat

import Cryptol.Utils.PP
import Cryptol.Utils.Panic (panic)
import Cryptol.Parser.AST
import Cryptol.Parser.Name(isGeneratedName)
import Cryptol.Parser.Position
import qualified Cryptol.TypeCheck.AST as T
import Cryptol.ModuleSystem.Interface
import Cryptol.ModuleSystem.Name


-- Naming Environment ----------------------------------------------------------

-- | The 'NamingEnv' is used by the renamer to determine what
-- identifiers refer to.
newtype NamingEnv = NamingEnv (Map Namespace (Map PName [Name]))
  deriving (Show,Generic,NFData)

-- | All names mentioned in the environment
namingEnvNames :: NamingEnv -> Set Name
namingEnvNames (NamingEnv xs) =
  Set.fromList $ concatMap (concat . Map.elems) $ Map.elems xs


-- | Get the names in a given namespace
namespaceMap :: Namespace -> NamingEnv -> Map PName [Name]
namespaceMap ns (NamingEnv env) = Map.findWithDefault Map.empty ns env

-- | Resolve a name in the given namespace.
lookupNS :: Namespace -> PName -> NamingEnv -> [Name]
lookupNS ns x = Map.findWithDefault [] x . namespaceMap ns

-- | Return a list of value-level names to which this parsed name may refer.
lookupValNames :: PName -> NamingEnv -> [Name]
lookupValNames = lookupNS NSValue

-- | Return a list of type-level names to which this parsed name may refer.
lookupTypeNames :: PName -> NamingEnv -> [Name]
lookupTypeNames = lookupNS NSType

-- | Singleton renaming environment for the given namespace.
singletonNS :: Namespace -> PName -> Name -> NamingEnv
singletonNS ns pn n = NamingEnv (Map.singleton ns (Map.singleton pn [n]))

-- | Singleton expression renaming environment.
singletonE :: PName -> Name -> NamingEnv
singletonE = singletonNS NSValue

-- | Singleton type renaming environment.
singletonT :: PName -> Name -> NamingEnv
singletonT = singletonNS NSType


namingEnvRename :: (Name -> Name) -> NamingEnv -> NamingEnv
namingEnvRename f (NamingEnv mp) = NamingEnv (ren <$> mp)
  where
  ren nsm = map f <$> nsm


instance Semigroup NamingEnv where
  NamingEnv l <> NamingEnv r =
      NamingEnv (Map.unionWith (Map.unionWith merge) l r)

instance Monoid NamingEnv where
  mempty = NamingEnv Map.empty
  {-# INLINE mempty #-}


-- | Merge two name maps, collapsing cases where the entries are the same, and
-- producing conflicts otherwise.
merge :: [Name] -> [Name] -> [Name]
merge xs ys | xs == ys  = xs
            | otherwise = nub (xs ++ ys)

instance PP NamingEnv where
  ppPrec _ (NamingEnv mps)   = vcat $ map ppNS $ Map.toList mps
    where ppNS (ns,xs) = pp ns $$ nest 2 (vcat (map ppNm (Map.toList xs)))
          ppNm (x,as)  = pp x <+> "->" <+> commaSep (map pp as)

-- | Generate a mapping from 'PrimIdent' to 'Name' for a
-- given naming environment.
toPrimMap :: NamingEnv -> PrimMap
toPrimMap env =
  PrimMap
    { primDecls = fromNS NSValue
    , primTypes = fromNS NSType
    }
  where
  fromNS ns = Map.fromList
                [ entry x | xs <- Map.elems (namespaceMap ns env), x <- xs ]

  entry n = case asPrim n of
              Just p  -> (p,n)
              Nothing -> panic "toPrimMap" [ "Not a declared name?"
                                           , show n
                                           ]


-- | Generate a display format based on a naming environment.
toNameDisp :: NamingEnv -> NameDisp
toNameDisp env = NameDisp (`Map.lookup` names)
  where
  names = Map.fromList
            [ (og, qn)
              | ns            <- [ NSValue, NSType, NSModule ]
              , (pn,xs)       <- Map.toList (namespaceMap ns env)
              , x             <- xs
              , og            <- maybeToList (asOrigName x)
              , let qn = case getModName pn of
                          Just q  -> Qualified q
                          Nothing -> UnQualified
            ]


-- | Produce sets of visible names for types and declarations.
--
-- NOTE: if entries in the NamingEnv would have produced a name clash,
-- they will be omitted from the resulting sets.
visibleNames :: NamingEnv -> Map Namespace (Set Name)
visibleNames (NamingEnv env) = Set.fromList . mapMaybe check . Map.elems <$> env
  where
  check names =
    case names of
      [name] -> Just name
      _      -> Nothing

-- | Qualify all symbols in a 'NamingEnv' with the given prefix.
qualify :: ModName -> NamingEnv -> NamingEnv
qualify pfx (NamingEnv env) = NamingEnv (Map.mapKeys toQual <$> env)
  where
  -- XXX we don't currently qualify fresh names
  toQual (Qual _ n)  = Qual pfx n
  toQual (UnQual n)  = Qual pfx n
  toQual n@NewName{} = n

filterNames :: (PName -> Bool) -> NamingEnv -> NamingEnv
filterNames p (NamingEnv env) = NamingEnv (Map.filterWithKey check <$> env)
  where check n _ = p n


-- | Like mappend, but when merging, prefer values on the lhs.
shadowing :: NamingEnv -> NamingEnv -> NamingEnv
shadowing (NamingEnv l) (NamingEnv r) = NamingEnv (Map.unionWith Map.union l r)

travNamingEnv :: Applicative f => (Name -> f Name) -> NamingEnv -> f NamingEnv
travNamingEnv f (NamingEnv mp) =
  NamingEnv <$> traverse (traverse (traverse f)) mp


{- | Do something in context.  If `Nothing` than we are working with
a local declaration. Otherwise we are at the top-level of the
given module. -}
data InModule a = InModule (Maybe ModPath) a
                  deriving (Functor,Traversable,Foldable,Show)


newTop ::
  FreshM m => Namespace -> ModPath -> PName -> Maybe Fixity -> Range -> m Name
newTop ns m thing fx rng =
  liftSupply (mkDeclared ns m src (getIdent thing) fx rng)
  where src = if isGeneratedName thing then SystemName else UserName

newLocal :: FreshM m => Namespace -> PName -> Range -> m Name
newLocal ns thing rng = liftSupply (mkParameter ns (getIdent thing) rng)

newtype BuildNamingEnv = BuildNamingEnv { runBuild :: SupplyT Id NamingEnv }


buildNamingEnv :: BuildNamingEnv -> Supply -> (NamingEnv,Supply)
buildNamingEnv b supply = runId $ runSupplyT supply $ runBuild b

-- | Generate a 'NamingEnv' using an explicit supply.
defsOf :: BindsNames a => a -> Supply -> (NamingEnv,Supply)
defsOf = buildNamingEnv . namingEnv


--------------------------------------------------------------------------------
-- Collect definitions of nested modules

type NestedMods = Map Name NamingEnv
type CollectM   = StateT NestedMods (SupplyT Id)

collectNestedModules ::
  NamingEnv -> Module PName -> Supply -> (NestedMods, Supply)
collectNestedModules env m =
  collectNestedModulesDecls env (thing (mName m)) (mDecls m)

collectNestedModulesDecls ::
  NamingEnv -> ModName -> [TopDecl PName] -> Supply -> (NestedMods, Supply)
collectNestedModulesDecls env m ds sup = (mp,newS)
  where
  s0            = Map.empty
  mpath         = TopModule m
  ((_,mp),newS) = runId $ runSupplyT sup $ runStateT s0 $
                  collectNestedModulesDs mpath env ds

collectNestedModulesDs :: ModPath -> NamingEnv -> [TopDecl PName] -> CollectM ()
collectNestedModulesDs mpath env ds =
  forM_ [ tlValue nm | DModule nm <- ds ] \(NestedModule nested) ->
    do let pname = thing (mName nested)
           name  = case lookupNS NSModule pname env of
                     n : _ -> n -- if a name is ambiguous we may get
                                -- multiple answers, but we just pick one.
                                -- This should be OK, as the error should be
                                -- caught during actual renaming.
                     _   -> panic "collectedNestedModulesDs"
                             [ "Missing definition for " ++ show pname ]
       newEnv <- lift (runBuild (moduleDefs (Nested mpath (nameIdent name)) nested))
       sets_ (Map.insert name newEnv)
       let newMPath = Nested mpath (nameIdent name)
       collectNestedModulesDs newMPath newEnv (mDecls nested)

--------------------------------------------------------------------------------




instance Semigroup BuildNamingEnv where
  BuildNamingEnv a <> BuildNamingEnv b = BuildNamingEnv $
    do x <- a
       y <- b
       return (mappend x y)

instance Monoid BuildNamingEnv where
  mempty = BuildNamingEnv (pure mempty)

  mappend = (<>)

  mconcat bs = BuildNamingEnv $
    do ns <- sequence (map runBuild bs)
       return (mconcat ns)

--------------------------------------------------------------------------------



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



-- | Adapt the things exported by something to the specific import/open.
interpImportEnv :: ImportG name  {- ^ The import declarations -} ->
                NamingEnv     {- ^ All public things coming in -} ->
                NamingEnv
interpImportEnv imp public = qualified
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



-- | Interpret an import in the context of an interface, to produce a name
-- environment for the renamer, and a 'NameDisp' for pretty-printing.
interpImportIface :: Import     {- ^ The import declarations -} ->
                IfaceDecls {- ^ Declarations of imported module -} ->
                NamingEnv
interpImportIface imp = interpImportEnv imp . unqualifiedEnv


-- | Generate a naming environment from a declaration interface, where none of
-- the names are qualified.
unqualifiedEnv :: IfaceDecls -> NamingEnv
unqualifiedEnv IfaceDecls { .. } =
  mconcat [ exprs, tySyns, ntTypes, absTys, ntExprs, mods ]
  where
  toPName n = mkUnqual (nameIdent n)

  exprs   = mconcat [ singletonE (toPName n) n | n <- Map.keys ifDecls ]
  tySyns  = mconcat [ singletonT (toPName n) n | n <- Map.keys ifTySyns ]
  ntTypes = mconcat [ singletonT (toPName n) n | n <- Map.keys ifNewtypes ]
  absTys  = mconcat [ singletonT (toPName n) n | n <- Map.keys ifAbstractTypes ]
  ntExprs = mconcat [ singletonE (toPName n) n | n <- Map.keys ifNewtypes ]
  mods    = mconcat [ singletonNS NSModule (toPName n) n
                                                | n <- Map.keys ifModules ]

-- | Compute an unqualified naming environment, containing the various module
-- parameters.
modParamsNamingEnv :: IfaceParams -> NamingEnv
modParamsNamingEnv IfaceParams { .. } =
  NamingEnv $ Map.fromList
    [ (NSValue, Map.fromList $ map fromFu $ Map.keys ifParamFuns)
    , (NSType,  Map.fromList $ map fromTy $ Map.elems ifParamTypes)
    ]
  where
  toPName n = mkUnqual (nameIdent n)

  fromTy tp = let nm = T.mtpName tp
              in (toPName nm, [nm])

  fromFu f  = (toPName f, [f])



data ImportIface = ImportIface Import Iface

-- | Produce a naming environment from an interface file, that contains a
-- mapping only from unqualified names to qualified ones.
instance BindsNames ImportIface where
  namingEnv (ImportIface imp Iface { .. }) = BuildNamingEnv $
    return (interpImportIface imp ifPublic)
  {-# INLINE namingEnv #-}

-- | Introduce the name
instance BindsNames (InModule (Bind PName)) where
  namingEnv (InModule mb b) = BuildNamingEnv $
    do let Located { .. } = bName b
       n <- case mb of
              Just m  -> newTop NSValue m thing (bFixity b) srcRange
              Nothing -> newLocal NSValue thing srcRange -- local fixitiies?

       return (singletonE thing n)

-- | Generate the naming environment for a type parameter.
instance BindsNames (TParam PName) where
  namingEnv TParam { .. } = BuildNamingEnv $
    do let range = fromMaybe emptyRange tpRange
       n <- newLocal NSType tpName range
       return (singletonT tpName n)

-- | The naming environment for a single module.  This is the mapping from
-- unqualified names to fully qualified names with uniques.
instance BindsNames (Module PName) where
  namingEnv m = moduleDefs (TopModule (thing (mName m))) m


moduleDefs :: ModPath -> ModuleG mname PName -> BuildNamingEnv
moduleDefs m Module { .. } = foldMap (namingEnv . InModule (Just m)) mDecls


instance BindsNames (InModule (TopDecl PName)) where
  namingEnv (InModule ns td) =
    case td of
      Decl d           -> namingEnv (InModule ns (tlValue d))
      DPrimType d      -> namingEnv (InModule ns (tlValue d))
      TDNewtype d      -> namingEnv (InModule ns (tlValue d))
      DParameterType d -> namingEnv (InModule ns d)
      DParameterConstraint {} -> mempty
      DParameterFun  d -> namingEnv (InModule ns d)
      Include _        -> mempty
      DImport {}       -> mempty -- see 'openLoop' in the renamer
      DModule m        -> namingEnv (InModule ns (tlValue m))


instance BindsNames (InModule (NestedModule PName)) where
  namingEnv (InModule ~(Just m) (NestedModule mdef)) = BuildNamingEnv $
    do let pnmame = mName mdef
       nm   <- newTop NSModule m (thing pnmame) Nothing (srcRange pnmame)
       pure (singletonNS NSModule (thing pnmame) nm)

instance BindsNames (InModule (PrimType PName)) where
  namingEnv (InModule ~(Just m) PrimType { .. }) =
    BuildNamingEnv $
      do let Located { .. } = primTName
         nm <- newTop NSType m thing primTFixity srcRange
         pure (singletonT thing nm)

instance BindsNames (InModule (ParameterFun PName)) where
  namingEnv (InModule ~(Just ns) ParameterFun { .. }) = BuildNamingEnv $
    do let Located { .. } = pfName
       ntName <- newTop NSValue ns thing pfFixity srcRange
       return (singletonE thing ntName)

instance BindsNames (InModule (ParameterType PName)) where
  namingEnv (InModule ~(Just ns) ParameterType { .. }) = BuildNamingEnv $
    -- XXX: we don't seem to have a fixity environment at the type level
    do let Located { .. } = ptName
       ntName <- newTop NSType ns thing Nothing srcRange
       return (singletonT thing ntName)

-- NOTE: we use the same name at the type and expression level, as there's only
-- ever one name introduced in the declaration. The names are only ever used in
-- different namespaces, so there's no ambiguity.
instance BindsNames (InModule (Newtype PName)) where
  namingEnv (InModule ~(Just ns) Newtype { .. }) = BuildNamingEnv $
    do let Located { .. } = nName
       ntName <- newTop NSType ns thing Nothing srcRange
       -- XXX: the name reuse here is sketchy
       return (singletonT thing ntName `mappend` singletonE thing ntName)

-- | The naming environment for a single declaration.
instance BindsNames (InModule (Decl PName)) where
  namingEnv (InModule pfx d) = case d of
    DBind b                 -> namingEnv (InModule pfx b)
    DSignature ns _sig      -> foldMap qualBind ns
    DPragma ns _p           -> foldMap qualBind ns
    DType syn               -> qualType (tsName syn) (tsFixity syn)
    DProp syn               -> qualType (psName syn) (psFixity syn)
    DLocated d' _           -> namingEnv (InModule pfx d')
    DRec {}                 -> panic "namingEnv" [ "DRec" ]
    DPatBind _pat _e        -> panic "namingEnv" ["Unexpected pattern binding"]
    DFixity{}               -> panic "namingEnv" ["Unexpected fixity declaration"]

    where

    mkName ns ln fx = case pfx of
                        Just m  -> newTop ns m (thing ln) fx (srcRange ln)
                        Nothing -> newLocal ns (thing ln) (srcRange ln)

    qualBind ln = BuildNamingEnv $
      do n <- mkName NSValue ln Nothing
         return (singletonE (thing ln) n)

    qualType ln f = BuildNamingEnv $
      do n <- mkName NSType ln f
         return (singletonT (thing ln) n)
