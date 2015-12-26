-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RecordWildCards #-}

module Cryptol.ModuleSystem.Env where

#ifndef RELOCATABLE
import Paths_cryptol (getDataDir)
#endif

import Cryptol.Eval (EvalEnv)
import Cryptol.ModuleSystem.Interface
import Cryptol.ModuleSystem.Name (Supply,emptySupply)
import qualified Cryptol.ModuleSystem.NamingEnv as R
import Cryptol.Parser.AST
import qualified Cryptol.TypeCheck as T
import qualified Cryptol.TypeCheck.AST as T
import Cryptol.Utils.PP (NameDisp)

import Control.Monad (guard)
import qualified Control.Exception as X
import Data.Foldable (fold)
import Data.Function (on)
import qualified Data.Map as Map
import Data.Monoid ((<>))
import System.Directory (getAppUserDataDirectory, getCurrentDirectory)
import System.Environment(getExecutablePath)
import System.FilePath ((</>), normalise, joinPath, splitPath, takeDirectory)
import qualified Data.List as List

import GHC.Generics (Generic)
import Control.DeepSeq.Generics

import Prelude ()
import Prelude.Compat

-- Module Environment ----------------------------------------------------------

data ModuleEnv = ModuleEnv
  { meLoadedModules :: LoadedModules
  , meNameSeeds     :: T.NameSeeds
  , meEvalEnv       :: EvalEnv
  , meFocusedModule :: Maybe ModName
  , meSearchPath    :: [FilePath]
  , meDynEnv        :: DynamicEnv
  , meMonoBinds     :: !Bool
  , meSolverConfig  :: T.SolverConfig
  , meCoreLint      :: CoreLint
  , meSupply        :: !Supply
  } deriving (Generic)

instance NFData ModuleEnv where rnf = genericRnf

data CoreLint = NoCoreLint        -- ^ Don't run core lint
              | CoreLint          -- ^ Run core lint
  deriving (Generic)

instance NFData CoreLint where rnf = genericRnf

resetModuleEnv :: ModuleEnv -> ModuleEnv
resetModuleEnv env = env
  { meLoadedModules = mempty
  , meNameSeeds     = T.nameSeeds
  , meEvalEnv       = mempty
  , meFocusedModule = Nothing
  , meDynEnv        = mempty
  }

initialModuleEnv :: IO ModuleEnv
initialModuleEnv  = do
  curDir <- getCurrentDirectory
#ifndef RELOCATABLE
  dataDir <- getDataDir
#endif
  binDir <- takeDirectory `fmap` getExecutablePath
  let instDir = normalise . joinPath . init . splitPath $ binDir
  -- looking up this directory can fail if no HOME is set, as in some
  -- CI settings
  let handle :: X.IOException -> IO String
      handle _e = return ""
  userDir <- X.catch (getAppUserDataDirectory "cryptol") handle
  return ModuleEnv
    { meLoadedModules = mempty
    , meNameSeeds     = T.nameSeeds
    , meEvalEnv       = mempty
    , meFocusedModule = Nothing
      -- we search these in order, taking the first match
    , meSearchPath    = [ curDir
                          -- something like $HOME/.cryptol
                        , userDir
#if defined(mingw32_HOST_OS) || defined(__MINGW32__)
                          -- ../cryptol on win32
                        , instDir </> "cryptol"
#else
                          -- ../share/cryptol on others
                        , instDir </> "share" </> "cryptol"
#endif

#ifndef RELOCATABLE
                          -- Cabal-defined data directory. Since this
                          -- is usually a global location like
                          -- /usr/local, search this one last in case
                          -- someone has multiple Cryptols
                        , dataDir
#endif
                        ]
    , meDynEnv        = mempty
    , meMonoBinds     = True
    , meSolverConfig  = T.SolverConfig
                          { T.solverPath = "z3"
                          , T.solverArgs = [ "-smt2", "-in" ]
                          , T.solverVerbose = 0
                          }
    , meCoreLint      = NoCoreLint
    , meSupply        = emptySupply
    }

-- | Try to focus a loaded module in the module environment.
focusModule :: ModName -> ModuleEnv -> Maybe ModuleEnv
focusModule n me = do
  guard (isLoaded n (meLoadedModules me))
  return me { meFocusedModule = Just n }

-- | Get a list of all the loaded modules. Each module in the
-- resulting list depends only on other modules that precede it.
loadedModules :: ModuleEnv -> [T.Module]
loadedModules = map lmModule . getLoadedModules . meLoadedModules

-- | Produce an ifaceDecls that represents the focused environment of the module
-- system, as well as a 'NameDisp' for pretty-printing names according to the
-- imports.
--
-- XXX This could really do with some better error handling, just returning
-- mempty when one of the imports fails isn't really desirable.
focusedEnv :: ModuleEnv -> (IfaceDecls,R.NamingEnv,NameDisp)
focusedEnv me = fold $
  do fm   <- meFocusedModule me
     lm   <- lookupModule fm me
     deps <- mapM loadImport (T.mImports (lmModule lm))
     let (ifaces,names) = unzip deps
         Iface { .. }   = lmInterface lm
         localDecls     = ifPublic `mappend` ifPrivate
         localNames     = R.unqualifiedEnv localDecls
         namingEnv      = localNames `R.shadowing` mconcat names

     return (mconcat (localDecls:ifaces), namingEnv, R.toNameDisp namingEnv)
  where
  loadImport imp =
    do lm <- lookupModule (iModule imp) me
       let decls = ifPublic (lmInterface lm)
       return (decls,R.interpImport imp decls)

-- | The unqualified declarations and name environment for the dynamic
-- environment.
dynamicEnv :: ModuleEnv -> (IfaceDecls,R.NamingEnv,NameDisp)
dynamicEnv me = (decls,names,R.toNameDisp names)
  where
  decls = deIfaceDecls (meDynEnv me)
  names = R.unqualifiedEnv decls

-- | Retrieve all 'IfaceDecls' referenced by a module, as well as all of its
-- public and private declarations, checking expressions
qualifiedEnv :: ModuleEnv -> IfaceDecls
qualifiedEnv me = fold $
  do fm   <- meFocusedModule me
     lm   <- lookupModule fm me
     deps <- mapM loadImport (T.mImports (lmModule lm))
     let Iface { .. } = lmInterface lm
     return (mconcat (ifPublic : ifPrivate : deps))
  where
  loadImport imp =
    do lm <- lookupModule (iModule imp) me
       return (ifPublic (lmInterface lm))


-- Loaded Modules --------------------------------------------------------------

newtype LoadedModules = LoadedModules
  { getLoadedModules :: [LoadedModule]
  } deriving (Show, Generic)
-- ^ Invariant: All the dependencies of any module `m` must precede `m` in the list.

instance NFData LoadedModules where rnf = genericRnf

instance Monoid LoadedModules where
  mempty        = LoadedModules []
  mappend l r   = LoadedModules
                $ List.unionBy ((==) `on` lmName) (getLoadedModules l) (getLoadedModules r)

data LoadedModule = LoadedModule
  { lmName      :: ModName
  , lmFilePath  :: FilePath
  , lmInterface :: Iface
  , lmModule    :: T.Module
  } deriving (Show, Generic)

instance NFData LoadedModule where rnf = genericRnf

isLoaded :: ModName -> LoadedModules -> Bool
isLoaded mn lm = any ((mn ==) . lmName) (getLoadedModules lm)

lookupModule :: ModName -> ModuleEnv -> Maybe LoadedModule
lookupModule mn env = List.find ((mn ==) . lmName) (getLoadedModules (meLoadedModules env))

addLoadedModule :: FilePath -> T.Module -> LoadedModules -> LoadedModules
addLoadedModule path tm lm
  | isLoaded (T.mName tm) lm = lm
  | otherwise                = LoadedModules (getLoadedModules lm ++ [loaded])
  where
  loaded = LoadedModule
    { lmName      = T.mName tm
    , lmFilePath  = path
    , lmInterface = genIface tm
    , lmModule    = tm
    }

removeLoadedModule :: FilePath -> LoadedModules -> LoadedModules
removeLoadedModule path (LoadedModules ms) = LoadedModules (remove ms)
  where

  remove (lm:rest)
    | lmFilePath lm == path = rest
    | otherwise             = lm : remove rest

  remove [] = []

-- Dynamic Environments --------------------------------------------------------

-- | Extra information we need to carry around to dynamically extend
-- an environment outside the context of a single module. Particularly
-- useful when dealing with interactive declarations as in @:let@ or
-- @it@.

data DynamicEnv = DEnv
  { deNames :: R.NamingEnv
  , deDecls :: [T.DeclGroup]
  , deEnv   :: EvalEnv
  } deriving (Generic)

instance NFData DynamicEnv where rnf = genericRnf

instance Monoid DynamicEnv where
  mempty = DEnv
    { deNames = mempty
    , deDecls = mempty
    , deEnv   = mempty
    }
  mappend de1 de2 = DEnv
    { deNames = deNames de1 <> deNames de2
    , deDecls = deDecls de1 <> deDecls de2
    , deEnv   = deEnv   de1 <> deEnv   de2
    }

-- | Build 'IfaceDecls' that correspond to all of the bindings in the
-- dynamic environment.
--
-- XXX: if we ever add type synonyms or newtypes at the REPL, revisit
-- this.
deIfaceDecls :: DynamicEnv -> IfaceDecls
deIfaceDecls DEnv { deDecls = dgs } =
  mconcat [ IfaceDecls
            { ifTySyns   = Map.empty
            , ifNewtypes = Map.empty
            , ifDecls    = Map.singleton (ifDeclName ifd) ifd
            }
          | decl <- concatMap T.groupDecls dgs
          , let ifd = mkIfaceDecl decl
          ]
