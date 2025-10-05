-- |
-- Module      :  Cryptol.ModuleSystem.Interface
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE Safe #-}
module Cryptol.ModuleSystem.Interface (
    Iface
  , IfaceG(..)
  , IfaceDecls(..)
  , IfaceDecl(..)
  , IfaceNames(..)
  , ifModName

  , emptyIface
  , ifacePrimMap
  , ifaceForgetName
  , ifaceIsFunctor
  , filterIfaceDecls
  , ifaceDeclsNames
  , ifaceOrigNameMap
  , ifaceNameToModuleMap
  ) where

import           Data.Set(Set)
import qualified Data.Set as Set
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Semigroup
import           Data.Text (Text)

import GHC.Generics (Generic)
import Control.DeepSeq

import Prelude ()
import Prelude.Compat

import Cryptol.ModuleSystem.Name
import Cryptol.Utils.Ident (ModName, OrigName(..))
import Cryptol.Utils.Panic(panic)
import Cryptol.Utils.Fixity(Fixity)
import Cryptol.Parser.AST(Pragma, ImpName(..))
import Cryptol.TypeCheck.Type
import Data.Maybe (maybeToList)

type Iface = IfaceG ModName

-- | The interface representing a typechecked top-level module.
data IfaceG name = Iface
  { ifNames     :: IfaceNames name    -- ^ Info about names in this module
  , ifParams    :: FunctorParams      -- ^ Module parameters, if any
  , ifDefines   :: IfaceDecls         -- ^ All things defined in the module
                                      -- (includes nested definitions)
  } deriving (Show, Generic, NFData, Functor)

-- | Remove the name of a module.  This is useful for dealing with collections
-- of modules, as in `Map (ImpName Name) (IfaceG ())`.
ifaceForgetName :: IfaceG name -> IfaceG ()
ifaceForgetName i = i { ifNames = newNames }
  where newNames = (ifNames i) { ifsName = () }

-- | Access the name of a module.
ifModName :: IfaceG name -> name
ifModName = ifsName . ifNames

-- | Information about the names in a module.
data IfaceNames name = IfaceNames
  { ifsName     :: name       -- ^ Name of this submodule
  , ifsNested   :: Set Name   -- ^ Things nested in this module
  , ifsDefines  :: Set Name   -- ^ Things defined in this module
  , ifsPublic   :: Set Name   -- ^ Subset of `ifsDefines` that is public
  , ifsDoc      :: ![Text]    -- ^ Documentation: more specific to least specific
  } deriving (Show, Generic, NFData, Functor)

-- | Is this interface for a functor.
ifaceIsFunctor :: IfaceG name -> Bool
ifaceIsFunctor = not . Map.null . ifParams

emptyIface :: ModName -> Iface
emptyIface nm = Iface
  { ifNames   = IfaceNames { ifsName    = nm
                           , ifsDefines = mempty
                           , ifsPublic  = mempty
                           , ifsNested  = mempty
                           , ifsDoc     = mempty
                           }
  , ifParams  = mempty
  , ifDefines = mempty
  }

-- | Declarations in a module.  Note that this includes things from nested
-- modules, but not things from nested functors, which are in `ifFunctors`.
data IfaceDecls = IfaceDecls
  { ifTySyns        :: Map.Map Name TySyn
  , ifNominalTypes  :: Map.Map Name NominalType
  , ifDecls         :: Map.Map Name IfaceDecl
  , ifModules       :: !(Map.Map Name (IfaceNames Name))
  , ifSignatures    :: !(Map.Map Name ModParamNames)
  , ifFunctors      :: !(Map.Map Name (IfaceG Name))
    {- ^ XXX: Maybe arg info?
    Also, with the current implementation we aim to completely remove functors
    by essentially inlining them.  To achieve this with just interfaces
    we'd have to store here the entire module, not just its interface.
    At the moment we work around this by passing all loaded modules to the
    type checker, so it looks up functors there, instead of in the interfaces,
    but we'd need to change this if we want better support for separate
    compilation. -}

  } deriving (Show, Generic, NFData)

filterIfaceDecls :: (Name -> Bool) -> IfaceDecls -> IfaceDecls
filterIfaceDecls p ifs = IfaceDecls
  { ifTySyns        = filterMap (ifTySyns ifs)
  , ifNominalTypes  = filterMap (ifNominalTypes ifs)
  , ifDecls         = filterMap (ifDecls ifs)
  , ifModules       = filterMap (ifModules ifs)
  , ifFunctors      = filterMap (ifFunctors ifs)
  , ifSignatures    = filterMap (ifSignatures ifs)
  }
  where
  filterMap :: Map.Map Name a -> Map.Map Name a
  filterMap = Map.filterWithKey (\k _ -> p k)

ifaceDeclsNames :: IfaceDecls -> Set Name
ifaceDeclsNames i = Set.unions [ Map.keysSet (ifTySyns i)
                               , Map.keysSet (ifNominalTypes i)
                               , Map.keysSet (ifDecls i)
                               , Map.keysSet (ifModules i)
                               , Map.keysSet (ifFunctors i)
                               , Map.keysSet (ifSignatures i)
                               ]


instance Semigroup IfaceDecls where
  l <> r = IfaceDecls
    { ifTySyns   = Map.union (ifTySyns l)   (ifTySyns r)
    , ifNominalTypes = Map.union (ifNominalTypes l) (ifNominalTypes r)
    , ifDecls    = Map.union (ifDecls l)    (ifDecls r)
    , ifModules  = Map.union (ifModules l)  (ifModules r)
    , ifFunctors = Map.union (ifFunctors l) (ifFunctors r)
    , ifSignatures = ifSignatures l <> ifSignatures r
    }

instance Monoid IfaceDecls where
  mempty      = IfaceDecls
                  { ifTySyns = mempty
                  , ifNominalTypes = mempty
                  , ifDecls = mempty
                  , ifModules = mempty
                  , ifFunctors = mempty
                  , ifSignatures = mempty
                  }
  mappend = (<>)
  mconcat ds  = IfaceDecls
    { ifTySyns   = Map.unions (map ifTySyns   ds)
    , ifNominalTypes = Map.unions (map ifNominalTypes ds)
    , ifDecls    = Map.unions (map ifDecls    ds)
    , ifModules  = Map.unions (map ifModules ds)
    , ifFunctors = Map.unions (map ifFunctors ds)
    , ifSignatures = Map.unions (map ifSignatures ds)
    }

data IfaceDecl = IfaceDecl
  { ifDeclName    :: !Name          -- ^ Name of thing
  , ifDeclSig     :: Schema         -- ^ Type
  , ifDeclIsPrim   :: !Bool
  , ifDeclPragmas :: [Pragma]       -- ^ Pragmas
  , ifDeclInfix   :: Bool           -- ^ Is this an infix thing
  , ifDeclFixity  :: Maybe Fixity   -- ^ Fixity information
  , ifDeclDoc     :: Maybe Text     -- ^ Documentation
  } deriving (Show, Generic, NFData)


-- | Produce a PrimMap from an interface.
--
-- NOTE: the map will expose /both/ public and private names.
-- NOTE: this is a bit misnamed, as it is used to resolve known names
-- that Cryptol introduces (e.g., during type checking).  These
-- names need not be primitives.   A better way to do this in the future
-- might be to use original names instead (see #1522).
ifacePrimMap :: Iface -> PrimMap
ifacePrimMap = ifaceDeclsPrimMap . ifDefines

ifaceDeclsPrimMap :: IfaceDecls -> PrimMap
ifaceDeclsPrimMap IfaceDecls { .. } =
  PrimMap { primDecls = Map.fromList (nominalVs ++ exprs)
          , primTypes = Map.fromList (nominalTs ++ types)
          }
  where
  entry n = case asPrim n of
              Just pid -> (pid,n)
              Nothing ->
                panic "ifaceDeclsPrimMap"
                          [ "Top level name not declared in a module?"
                          , show n ]

  nominalTs = map entry (Map.keys ifNominalTypes)
  nominalVs = [ entry n
              | nt <- Map.elems ifNominalTypes
              , (n,_) <- nominalTypeConTypes nt
              ]
  exprs     = map entry (Map.keys ifDecls)
  types     = map entry (Map.keys ifTySyns)


-- | Given an interface, compute a map from original names to actual names,
-- grouped by namespace.
ifaceOrigNameMap :: IfaceG name -> Map Namespace (Map OrigName Name)
ifaceOrigNameMap ifa = Map.unionsWith Map.union (here : nested)
  where
  here        = Map.fromList $
                  [ (NSValue, toMap vaNames) | not (Set.null vaNames) ] ++
                  [ (NSType,  toMap tyNames) | not (Set.null tyNames) ] ++
                  [ (NSValue, toMap moNames) | not (Set.null moNames) ]

  nested      = map ifaceOrigNameMap (Map.elems (ifFunctors decls))

  toMap names = Map.fromList
                  [ (og,x) | x <- Set.toList names, Just og <- [ asOrigName x ] ]

  decls       = ifDefines ifa
  from f      = Map.keysSet (f decls)
  tyNames     = Set.unions [ from ifTySyns, from ifNominalTypes ]
  moNames     = Set.unions [ from ifModules, from ifSignatures, from ifFunctors ]
  vaNames     = Set.unions [ newtypeCons, from ifDecls ]
  newtypeCons = Set.fromList
                  (concatMap conNames (Map.elems (ifNominalTypes decls)))
    where conNames = map fst . nominalTypeConTypes

-- | For every name in the interface compute the direct module that defines it.
-- This does not traverse into functors or interfaces.
ifaceNameToModuleMap :: Iface -> Map Name (ImpName Name)
ifaceNameToModuleMap iface = go (ImpTop <$> ifNames iface)
  where
    theModules = ifModules (ifDefines iface)

    go :: IfaceNames (ImpName Name) -> Map Name (ImpName Name)
    go names =
      Map.fromSet (\_ -> ifsName names) (ifsDefines names) <>
      Map.unions
        [ go (ImpNested <$> modu)
        | childName <- Set.toList (ifsNested names)
        , modu <- maybeToList (Map.lookup childName theModules)
        ]
