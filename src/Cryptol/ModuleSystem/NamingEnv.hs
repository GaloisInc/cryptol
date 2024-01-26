-- |
-- Module      :  Cryptol.ModuleSystem.NamingEnv
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE RecordWildCards #-}
-- See Note [-Wincomplete-uni-patterns and irrefutable patterns] in Cryptol.TypeCheck.TypePat
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Cryptol.ModuleSystem.NamingEnv
  ( module Cryptol.ModuleSystem.NamingEnv.Types
  , module Cryptol.ModuleSystem.NamingEnv
  ) where

import Data.Maybe (mapMaybe,maybeToList)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Foldable(foldl')

import Cryptol.Utils.PP
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.Ident(allNamespaces)
import Cryptol.Parser.AST
import qualified Cryptol.TypeCheck.AST as T
import Cryptol.ModuleSystem.Name
import Cryptol.ModuleSystem.Names
import Cryptol.ModuleSystem.Interface

import Cryptol.ModuleSystem.NamingEnv.Types


{- | This "joins" two naming environments by matching the text name.
The result maps the unique names from the first environment with the
matching names in the second.  This is used to compute the naming for
an instantiated functor:
  * if the left environment has the defined names of the functor, and
  * the right one has the defined names of the instantiation, then
  * the result maps functor names to instance names.
-}
zipByTextName :: NamingEnv -> NamingEnv -> Map Name Name
zipByTextName (NamingEnv k) (NamingEnv v) = Map.fromList $ doInter doNS k v
  where
  doInter :: Ord k => (a -> b -> [c]) -> Map k a -> Map k b -> [c]
  doInter f a b = concat (Map.elems (Map.intersectionWith f a b))

  doNS :: Map PName Names -> Map PName Names -> [(Name,Name)]
  doNS as bs = doInter doPName as bs

  doPName :: Names -> Names -> [(Name,Name)]
  doPName xs ys = [ (x,y) | x <- namesToList xs, y <- namesToList ys ]
  -- NOTE: we'd exepct that there are no ambiguities in the environments.

-- | Keep only the bindings in the 1st environment that are *NOT* in the second.
without :: NamingEnv -> NamingEnv -> NamingEnv
NamingEnv keep `without` NamingEnv remove = NamingEnv result
  where
  result     = Map.differenceWith rmInNS keep remove
  rmInNS a b = let c = Map.differenceWith diffNames a b
               in if Map.null c then Nothing else Just c

-- | All names mentioned in the environment
namingEnvNames :: NamingEnv -> Set Name
namingEnvNames (NamingEnv xs) =
  case unionManyNames (mapMaybe (unionManyNames . Map.elems) (Map.elems xs)) of
    Nothing -> Set.empty
    Just (One x) -> Set.singleton x
    Just (Ambig as) -> as

-- | Get a naming environment for the given names.  The `PName`s correspond
-- to the definition sites of the corresponding `Name`s, so typically they
-- will be unqualified.  The exception is for names that comre from parameters,
-- which are qualified with the relevant parameter.
namingEnvFromNames :: Set Name -> NamingEnv
namingEnvFromNames xs = NamingEnv (foldl' add mempty xs)
  where
  add mp x = let ns = nameNamespace x
             in Map.insertWith (Map.unionWith (<>))
                               ns (Map.singleton (nameToDefPName x) (One x))
                               mp


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
singletonNS ns pn n = NamingEnv (Map.singleton ns (Map.singleton pn (One n)))

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

filterPNames :: (PName -> Bool) -> NamingEnv -> NamingEnv
filterPNames p (NamingEnv env) = NamingEnv (Map.mapMaybe checkNS env)
  where
  checkNS nsMap = let new = Map.filterWithKey (\n _ -> p n) nsMap
                  in if Map.null new then Nothing else Just new

filterUNames :: (Name -> Bool) -> NamingEnv -> NamingEnv
filterUNames p (NamingEnv env) = NamingEnv (Map.mapMaybe check env)
  where
  check nsMap = let new = Map.mapMaybe (filterNames p) nsMap
                in if Map.null new then Nothing else Just new


-- | Find the ambiguous entries in an environmet.
-- A name is ambiguous if it might refer to multiple entities.
findAmbig :: NamingEnv -> [ [Name] ]
findAmbig (NamingEnv ns) =
  [ Set.toList xs
  | mp <- Map.elems ns
  , Ambig xs <- Map.elems mp
  ]

-- | Get the subset of the first environment that shadows something
-- in the second one.
findShadowing :: NamingEnv -> NamingEnv -> [ (PName,Name,[Name]) ]
findShadowing (NamingEnv lhs) rhs =
  [ (p, anyOne xs, namesToList ys)
  | (ns,mp) <- Map.toList lhs
  , (p,xs) <- Map.toList mp
  , Just ys <- [ lookupNS ns p rhs ]
  ]

-- | Do an arbitrary choice for ambiguous names.
-- We do this to continue checking afetr we've reported an ambiguity error.
forceUnambig :: NamingEnv -> NamingEnv
forceUnambig (NamingEnv mp) = NamingEnv (fmap (One . anyOne) <$> mp)

-- | Like mappend, but when merging, prefer values on the lhs.
shadowing :: NamingEnv -> NamingEnv -> NamingEnv
shadowing (NamingEnv l) (NamingEnv r) = NamingEnv (Map.unionWith Map.union l r)

mapNamingEnv :: (Name -> Name) -> NamingEnv -> NamingEnv
mapNamingEnv f (NamingEnv mp) = NamingEnv (fmap (mapNames f) <$> mp)

travNamingEnv :: Applicative f => (Name -> f Name) -> NamingEnv -> f NamingEnv
travNamingEnv f (NamingEnv mp) =
  NamingEnv <$> traverse (traverse (travNames f)) mp

isEmptyNamingEnv :: NamingEnv -> Bool
isEmptyNamingEnv (NamingEnv mp) = Map.null mp
-- This assumes that we've been normalizing away empty maps, hopefully
-- we've been doing it everywhere.


-- | Compute an unqualified naming environment, containing the various module
-- parameters.
modParamNamesNamingEnv :: T.ModParamNames -> NamingEnv
modParamNamesNamingEnv T.ModParamNames { .. } =
  NamingEnv $ Map.fromList
    [ (NSValue, Map.fromList $ map fromFu $ Map.keys mpnFuns)
    , (NSType,  Map.fromList $ map fromTS (Map.elems mpnTySyn) ++
                               map fromTy (Map.elems mpnTypes))
    ]
  where
  toPName n = mkUnqual (nameIdent n)

  fromTy tp = let nm = T.mtpName tp
              in (toPName nm, One nm)

  fromFu f  = (toPName f, One f)

  fromTS ts = (toPName (T.tsName ts), One (T.tsName ts))

-- | Compute a naming environment from a module parameter, qualifying it
-- according to 'mpQual'.
modParamNamingEnv :: T.ModParam -> NamingEnv
modParamNamingEnv mp = maybe id qualify (T.mpQual mp) $
  modParamNamesNamingEnv (T.mpParameters mp)

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

  ntTypes = mconcat [ n
                    | nt <- Map.elems ifNominalTypes
                    , let tname  = T.ntName nt
                    , n  <- singletonNS NSType (toPName tname) tname
                          : [ singletonNS NSValue (toPName cname) cname
                            | cname <-map fst (T.nominalTypeConTypes nt)
                            ]
                    ]

  absTys  = mconcat [ singletonNS NSType (toPName n) n
                    | n <- Map.keys ifAbstractTypes ]

  ntExprs = mconcat [ singletonNS NSValue (toPName n) n
                    | n <- Map.keys ifNominalTypes ]

  mods    = mconcat [ singletonNS NSModule (toPName n) n
                    | n <- Map.keys ifModules ]

  sigs    = mconcat [ singletonNS NSModule (toPName n) n
                    | n <- Map.keys ifSignatures ]


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
       filterPNames (\qn -> not (getIdent qn `elem` ns)) public

    | Just (Only ns) <- iSpec imp =
       filterPNames (\qn -> getIdent qn `elem` ns) public

    | otherwise = public



