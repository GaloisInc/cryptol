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
module Cryptol.ModuleSystem.NamingEnv where

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
import Cryptol.Utils.Ident(allNamespaces)
import Cryptol.Parser.AST
import Cryptol.Parser.Name(isGeneratedName)
import Cryptol.Parser.Position
import qualified Cryptol.TypeCheck.AST as T
import Cryptol.ModuleSystem.Interface
import Cryptol.ModuleSystem.Name


-- Naming Environment ----------------------------------------------------------

-- | The 'NamingEnv' is used by the renamer to determine what
-- identifiers refer to.
newtype NamingEnv = NamingEnv (Map Namespace (Map PName Names))
  deriving (Show,Generic,NFData)

--------------------------------------------------------------------------------
data Names = One Name | Ambig (Set Name) -- ^ Non-empty
  deriving (Show,Generic,NFData)

namesToList :: Names -> [Name]
namesToList xs =
  case xs of
    One x -> [x]
    Ambig ns -> Set.toList ns

anyOne :: Names -> Name
anyOne = head . namesToList

unionNames :: Names -> Names -> Names
unionNames xs ys =
  case (xs,ys) of
    (One x, One y) | x == y -> One x
                   | otherwise -> Ambig $! Set.fromList [x,y]
    (One x, Ambig as) -> Ambig $! Set.insert x as
    (Ambig as, One x) -> Ambig $! Set.insert x as
    (Ambig as, Ambig bs) -> Ambig $! Set.union as bs

namesFromSet :: Set Name {- ^ Non-empty -} -> Names
namesFromSet xs =
  case Set.minView xs of
    Just (a,ys) -> if Set.null ys then One a else Ambig xs
    Nothing     -> panic "namesFromSet" ["empty set"]

unionManyNames :: [Names] -> Maybe Names
unionManyNames xs =
  case xs of
    [] -> Nothing
    _  -> Just (foldr1 unionNames xs)

mapNames :: (Name -> Name) -> Names -> Names
mapNames f xs =
  case xs of
    One x -> One (f x)
    Ambig as -> namesFromSet (Set.map f as)

travNames :: Applicative f => (Name -> f Name) -> Names -> f Names
travNames f xs =
  case xs of
    One x -> One <$> f x
    Ambig as -> namesFromSet . Set.fromList <$> traverse f (Set.toList as)
--------------------------------------------------------------------------------


-- | All names mentioned in the environment
namingEnvNames :: NamingEnv -> Set Name
namingEnvNames (NamingEnv xs) =
  case unionManyNames (mapMaybe (unionManyNames . Map.elems) (Map.elems xs)) of
    Nothing -> Set.empty
    Just (One x) -> Set.singleton x
    Just (Ambig as) -> as

-- | Get the names in a given namespace
namespaceMap :: Namespace -> NamingEnv -> Map PName Names
namespaceMap ns (NamingEnv env) = Map.findWithDefault Map.empty ns env

-- | Resolve a name in the given namespace.
lookupNS :: Namespace -> PName -> NamingEnv -> Maybe Names
lookupNS ns x env = Map.lookup x (namespaceMap ns env)

-- | Resolve a name in the given namespace.
lookupListNS :: Namespace -> PName -> NamingEnv -> [Name]
lookupListNS ns x env =
  case lookupNS ns x env of
    Nothing -> []
    Just as -> namesToList as

-- | Singleton renaming environment for the given namespace.
singletonNS :: Namespace -> PName -> Name -> NamingEnv
singletonNS ns pn n =
  NamingEnv (Map.singleton ns (Map.singleton pn (One n)))


instance Semigroup NamingEnv where
  NamingEnv l <> NamingEnv r =
      NamingEnv (Map.unionWith (Map.unionWith unionNames) l r)

instance Monoid NamingEnv where
  mempty = NamingEnv Map.empty
  {-# INLINE mempty #-}


instance PP NamingEnv where
  ppPrec _ (NamingEnv mps)   = vcat $ map ppNS $ Map.toList mps
    where ppNS (ns,xs) = pp ns $$ nest 2 (vcat (map ppNm (Map.toList xs)))
          ppNm (x,as)  = pp x <+> "->" <+> commaSep (map pp (namesToList as))

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
                [ entry x | xs <- Map.elems (namespaceMap ns env)
                          , x <- namesToList xs ]

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
              | ns            <- allNamespaces
              , (pn,xs)       <- Map.toList (namespaceMap ns env)
              , x             <- namesToList xs
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
visibleNames (NamingEnv env) = check <$> env
  where check mp = Set.fromList [ a | One a <- Map.elems mp ]

-- | Qualify all symbols in a 'NamingEnv' with the given prefix.
qualify :: ModName -> NamingEnv -> NamingEnv
qualify pfx (NamingEnv env) = NamingEnv (Map.mapKeys toQual <$> env)
  where
  -- We don't qualify fresh names, because they should not be directly
  -- visible to the end users (i.e., they shouldn't really be exported)
  toQual (Qual _ n)  = Qual pfx n
  toQual (UnQual n)  = Qual pfx n
  toQual n@NewName{} = n

filterNames :: (PName -> Bool) -> NamingEnv -> NamingEnv
filterNames p (NamingEnv env) = NamingEnv (Map.filterWithKey check <$> env)
  where check n _ = p n

-- | Like mappend, but when merging, prefer values on the lhs.
shadowing :: NamingEnv -> NamingEnv -> NamingEnv
shadowing (NamingEnv l) (NamingEnv r) = NamingEnv (Map.unionWith Map.union l r)

mapNamingEnv :: (Name -> Name) -> NamingEnv -> NamingEnv
mapNamingEnv f (NamingEnv mp) = NamingEnv (fmap (mapNames f) <$> mp)

travNamingEnv :: Applicative f => (Name -> f Name) -> NamingEnv -> f NamingEnv
travNamingEnv f (NamingEnv mp) =
  NamingEnv <$> traverse (traverse (travNames f)) mp



{- | Do something in the context of a module.
If `Nothing` than we are working with a local declaration.
Otherwise we are at the top-level of the given module.

By wrapping types with this, we can pass the module path
to methdods that need the extra information. -}
data InModule a = InModule (Maybe ModPath) a
                  deriving (Functor,Traversable,Foldable,Show)


newTop ::
  FreshM m => Namespace -> ModPath -> PName -> Maybe Fixity -> Range -> m Name
newTop ns m thing fx rng =
  liftSupply (mkDeclared ns m src (getIdent thing) fx rng)
  where src = if isGeneratedName thing then SystemName else UserName

newLocal :: FreshM m => Namespace -> PName -> Range -> m Name
newLocal ns thing rng = liftSupply (mkParameter ns (getIdent thing) rng)

-- | Given a name in a signature, make a name for the parameter corresponding
-- to the signature.
newModParam :: FreshM m => Name -> m Name
newModParam n = liftSupply (mkModParam n)

newtype BuildNamingEnv = BuildNamingEnv { runBuild :: SupplyT Id NamingEnv }

buildNamingEnv :: BuildNamingEnv -> Supply -> (NamingEnv,Supply)
buildNamingEnv b supply = runId $ runSupplyT supply $ runBuild b

-- | Generate a 'NamingEnv' using an explicit supply.
defsOf :: BindsNames a => a -> Supply -> (NamingEnv,Supply)
defsOf = buildNamingEnv . namingEnv


--------------------------------------------------------------------------------
{- Collect definitions of entities that may contains other entities.
For example, submodules and signatures, when treated as declarations
only introduce a single name (e.g., the name of the submodule or signature)
but when used can introduce additional names (e.g., in an import or
a submodule declaration).  The code in the following section computes the
names that are "owned" by all the entities, when "used".
-}


data OwnedEntities = OwnedEntities
  { ownSubmodules :: Map Name NamingEnv
  , ownSignatures :: Map Name NamingEnv
  }

instance Semigroup OwnedEntities where
  x <> y = OwnedEntities { ownSubmodules = ownSubmodules x <> ownSubmodules y
                         , ownSignatures = ownSignatures x <> ownSignatures y
                         }

instance Monoid OwnedEntities where
  mempty = OwnedEntities { ownSubmodules = mempty
                         , ownSignatures = mempty
                         }

type CollectM   = StateT OwnedEntities (SupplyT Id)

-- | Collect things nested in a module
collectNestedInModule ::
  NamingEnv -> Module PName -> Supply -> (OwnedEntities, Supply)
collectNestedInModule env m =
  collectNestedInDecls env (thing (mName m)) (mDecls m)

-- | Collect things nested in a list of declarations
collectNestedInDecls ::
  NamingEnv -> ModName -> [TopDecl PName] -> Supply -> (OwnedEntities, Supply)
collectNestedInDecls env m ds sup = (mp,newS)
  where
  s0            = mempty
  mpath         = TopModule m
  ((_,mp),newS) = runId $ runSupplyT sup $ runStateT s0 $
                  collectNestedDeclsM mpath env ds

collectNestedDeclsM :: ModPath -> NamingEnv -> [TopDecl PName] -> CollectM ()
collectNestedDeclsM mpath env ds =

  do forM_ [ tlValue s | DModSig s <- ds ] \s ->
        do let pname = thing (sigName s)
               name  = case lookupNS NSSignature pname env of
                        Just ns -> anyOne ns
                        Nothing -> panic "collectNestedDeclsM"
                                    [ "Missing definition for " ++ show pname ]
                        -- See comment below.

           newEnv <- lift $ runBuild $
                    signatureDefs (Nested mpath (nameIdent name)) s
           sets_ \o -> o { ownSignatures = Map.insert name newEnv
                                                        (ownSignatures o)}

     forM_ [ tlValue nm | DModule nm <- ds ] \(NestedModule nested) ->
       do let pname = thing (mName nested)
              name  = case lookupNS NSModule pname env of
                        Just ns -> anyOne ns
                        Nothing -> panic "collectNestedDeclsM"
                                    [ "Missing definition for " ++ show pname ]
              -- if a name is ambiguous we may get
              -- multiple answers, but we just pick one.
              -- This should be OK, as the error should be
              -- caught during actual renaming.

          newEnv <- lift $ runBuild $
                    moduleDefs (Nested mpath (nameIdent name)) nested
          sets_ \o -> o { ownSubmodules =
                                  Map.insert name newEnv (ownSubmodules o) }
          let newMPath = Nested mpath (nameIdent name)
          collectNestedDeclsM newMPath newEnv (mDecls nested)

--------------------------------------------------------------------------------




--------------------------------------------------------------------------------
-- Computes the names introduced by various declarations.

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
  mconcat [ exprs, tySyns, ntTypes, absTys, ntExprs, mods, sigs ]
  where
  toPName n = mkUnqual (nameIdent n)

  exprs   = mconcat [ singletonNS NSValue (toPName n) n
                    | n <- Map.keys ifDecls ]

  tySyns  = mconcat [ singletonNS NSType (toPName n) n
                    | n <- Map.keys ifTySyns ]

  ntTypes = mconcat [ singletonNS NSType (toPName n) n
                    | n <- Map.keys ifNewtypes ]

  absTys  = mconcat [ singletonNS NSType (toPName n) n
                    | n <- Map.keys ifAbstractTypes ]

  ntExprs = mconcat [ singletonNS NSValue (toPName n) n
                    | n <- Map.keys ifNewtypes ]

  mods    = mconcat [ singletonNS NSModule (toPName n) n
                    | n <- Map.keys ifModules ]

  sigs    = mconcat [ singletonNS NSSignature (toPName n) n
                    | n <- Map.keys ifSignatures ]


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
              in (toPName nm, One nm)

  fromFu f  = (toPName f, One f)



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

       return (singletonNS NSValue thing n)

-- | Generate the naming environment for a type parameter.
instance BindsNames (TParam PName) where
  namingEnv TParam { .. } = BuildNamingEnv $
    do let range = fromMaybe emptyRange tpRange
       n <- newLocal NSType tpName range
       return (singletonNS NSType tpName n)

-- | The naming environment for a single module.  This is the mapping from
-- unqualified names to fully qualified names with uniques.
instance BindsNames (Module PName) where
  namingEnv m = moduleDefs (TopModule (thing (mName m))) m


-- | These are the names "owned" by the module.  These names are used
-- when resolving the module itself, and also when the module is imported.
moduleDefs :: ModPath -> ModuleG mname PName -> BuildNamingEnv
moduleDefs m Module { .. } = foldMap (namingEnv . InModule (Just m)) mDecls

-- | These are the names "owned" by the signature.  These names are
-- used when resolving the signature.  They are also used to figure out what
-- names to instantuate when the signature is used.
signatureDefs :: ModPath -> Signature PName -> BuildNamingEnv
signatureDefs m sig =
     mconcat [ namingEnv (InModule loc p) | p <- sigTypeParams sig ]
  <> mconcat [ namingEnv (InModule loc p) | p <- sigFunParams sig ]
  where
  loc = Just m

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

      DModSig s        -> namingEnv (InModule ns (tlValue s))
      DModParam {}     -> mempty-- handled in the renamer as we need to resolve
                                 -- the signature name first (similar to import)

instance BindsNames (InModule (NestedModule PName)) where
  namingEnv (InModule ~(Just m) (NestedModule mdef)) = BuildNamingEnv $
    do let pnmame = mName mdef
       nm   <- newTop NSModule m (thing pnmame) Nothing (srcRange pnmame)
       pure (singletonNS NSModule (thing pnmame) nm)

instance BindsNames (InModule (Signature PName)) where
  namingEnv (InModule ~(Just m) sig) = BuildNamingEnv
    do let pname = sigName sig
       nm <- newTop NSSignature m (thing pname) Nothing (srcRange pname)
       pure (singletonNS NSSignature (thing pname) nm)



instance BindsNames (InModule (PrimType PName)) where
  namingEnv (InModule ~(Just m) PrimType { .. }) =
    BuildNamingEnv $
      do let Located { .. } = primTName
         nm <- newTop NSType m thing primTFixity srcRange
         pure (singletonNS NSType thing nm)

instance BindsNames (InModule (ParameterFun PName)) where
  namingEnv (InModule ~(Just ns) ParameterFun { .. }) = BuildNamingEnv $
    do let Located { .. } = pfName
       ntName <- newTop NSValue ns thing pfFixity srcRange
       return (singletonNS NSValue thing ntName)

instance BindsNames (InModule (ParameterType PName)) where
  namingEnv (InModule ~(Just ns) ParameterType { .. }) = BuildNamingEnv $
    -- XXX: we don't seem to have a fixity environment at the type level
    do let Located { .. } = ptName
       ntName <- newTop NSType ns thing Nothing srcRange
       return (singletonNS NSType thing ntName)

-- NOTE: we use the same name at the type and expression level, as there's only
-- ever one name introduced in the declaration. The names are only ever used in
-- different namespaces, so there's no ambiguity.
instance BindsNames (InModule (Newtype PName)) where
  namingEnv (InModule ~(Just ns) Newtype { .. }) = BuildNamingEnv $
    do let Located { .. } = nName
       ntName <- newTop NSType ns thing Nothing srcRange
       -- XXX: the name reuse here is sketchy
       return (singletonNS NSType thing ntName `mappend` singletonNS NSValue thing ntName)

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
         return (singletonNS NSValue (thing ln) n)

    qualType ln f = BuildNamingEnv $
      do n <- mkName NSType ln f
         return (singletonNS NSType (thing ln) n)
