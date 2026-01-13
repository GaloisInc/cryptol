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
import           Data.Text (Text)
                  
import Cryptol.Utils.PP
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.Ident(allNamespaces,packModName,modNameChunksText)
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
-- will be unqualified.  The exception is for names that come from parameters,
-- which are qualified with the relevant parameter.
namingEnvFromNames :: Set Name -> NamingEnv
namingEnvFromNames = namingEnvFromNames' nameToDefPName

-- | Create a naming environment from a @Set Name@, given a mapping from
--   @Name -> PName@.
namingEnvFromNames' :: (Name -> PName) -> Set Name -> NamingEnv
namingEnvFromNames' nameToPName xs =
  NamingEnv (foldl' add mempty xs)
  where
  add mp x = let ns = nameNamespace x
             in Map.insertWith (Map.unionWith (<>))
                               ns (Map.singleton (nameToPName x) (One x))
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
              , let qn = maybe UnQualified Qualified (getModName pn)
              , x             <- namesToList xs
              , og            <- maybeToList (asOrigName x)
             
            ]


-- | Produce sets of visible names for types and declarations.
--
-- NOTE: if entries in the NamingEnv would have produced a name clash,
-- they will be omitted from the resulting sets.
visibleNames :: NamingEnv -> Map Namespace (Set Name)
visibleNames (NamingEnv env) = check <$> env
  where check mp = Set.fromList [ a | One a <- Map.elems mp ]


-- | qualify pfx env - Qualify all symbols in `env :: NamingEnv` with
--   the 'pfx' prefix.
-- 
--   NOTE
--    - pfx can have multiple chunks (as Cryptol allows in qualified imports).
--    - Names in 'env' can be qualified names referencing submodule elements.
--
--   We don't qualify fresh names, because they should not be directly
--   visible to the end users (i.e., they shouldn't really be exported)
--
--   NOTE re the calls to `qualify`:
--     - used in modParamNamingEnv for module parameters, in this use all names are
--       `Unqual`
--     - used by interpImportEnv used by tryImport:
--       - here also, all names are `Unqual`.
--     - used by interpImportEnv and called from saw-script code:
--       - here, some names are inside submodules and thus qualified, thus
--         the need for the `appendChunk` machinery.
--     
qualify :: ModName -> NamingEnv -> NamingEnv
qualify pfx (NamingEnv env) = NamingEnv (Map.mapKeys toQual <$> env)
  where
  toQual (Qual mn n) = Qual (prependChunks pfx' mn) n
  toQual (UnQual' n _ns)  = Qual pfx n
  toQual n@NewName{} = n

  -- | prependChunks - add ChunksText to start of ModName
  prependChunks :: [Text] -> ModName -> ModName
  prependChunks ts modNm = packModName (ts ++ modNameChunksText modNm)

  -- | pfx' = pfx as ChunksText
  pfx' :: [Text]
  pfx' = case modNameChunksText pfx of
           [] -> panic "qualify" ["pfx must have at least one chunk: " ++ show pfx]
           xs -> xs
  
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
findAmbig env =
  [ Set.toList xs
  | mp <- Map.elems ns
  , Ambig xs <- Map.elems mp
  ]
  where
  NamingEnv ns = consToValues env

-- | Get the subset of the first environment that shadows something
-- in the second one.
findShadowing :: NamingEnv -> NamingEnv -> [(PName, Name, [Name])]
findShadowing (NamingEnv lhs) rhs = res
  where
    res =
      [ (p, anyOneUserName xs, namesToList ys)
        | (ns, mp) <- Map.toList lhs,
          (p, xs) <- Map.toList mp,
          Just ys <- [lookupNS ns p rhs]
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
  toPName n = UnQual' (nameIdent n) (nameSrc n)

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
  mconcat [ exprs, tySyns, ntTypes, ntExprs, mods, sigs ]
  where
  toPName n = UnQual' (nameIdent n) (nameSrc n)

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

  ntExprs = mconcat [ singletonNS NSValue (toPName n) n
                    | n <- Map.keys ifNominalTypes ]

  mods    = mconcat [ singletonNS NSModule (toPName n) n
                    | n <- Map.keys ifModules ]

  sigs    = mconcat [ singletonNS NSModule (toPName n) n
                    | n <- Map.keys ifSignatures ]


-- | Adapt the things exported by a module to the specific import/open.
interpImportEnv :: ImportG name  {- ^ The import declaration -} ->
                   NamingEnv     {- ^ All public things coming in -} ->
                   NamingEnv
interpImportEnv imp = interpImportEnv' (iAs imp) (iSpec imp)

-- | A more general version of `interpImportEnv`
interpImportEnv' :: Maybe ModName    {- ^ prefix with this qualifier -} ->
                    Maybe ImportSpec {- ^ restrict per ImportSpec    -} ->
                    NamingEnv        {- ^ All public things coming in -} ->
                    NamingEnv
interpImportEnv' iAs' iSpec' public = qualified
  where

  -- optionally qualify names in NamingEnv if the import is "qualified",
  --   i.e., if `isJust iAs'`
  qualified | Just pfx <- iAs' = qualify pfx restricted
            | otherwise        =             restricted

  -- restrict or hide imported symbols
  restricted
    | Just (Hiding ns) <- iSpec' =
       filterPNames (\qn -> not (getIdent qn `elem` ns)) public

    | Just (Only ns) <- iSpec' =
       filterPNames (\qn -> getIdent qn `elem` ns) public

    | otherwise = public