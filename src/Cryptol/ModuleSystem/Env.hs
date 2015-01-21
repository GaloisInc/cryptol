-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards #-}

module Cryptol.ModuleSystem.Env where

import Paths_cryptol (getDataDir)

import Cryptol.Eval (EvalEnv)
import Cryptol.ModuleSystem.Interface
import qualified Cryptol.ModuleSystem.NamingEnv as R
import Cryptol.Parser.AST
import qualified Cryptol.TypeCheck as T
import qualified Cryptol.TypeCheck.AST as T

import Control.Monad (guard)
import Data.Foldable (fold)
import Data.Function (on)
import qualified Data.Map as Map
import Data.Monoid ((<>), Monoid(..))
import System.Directory (getAppUserDataDirectory, getCurrentDirectory)
import System.Environment.Executable(splitExecutablePath)
import System.FilePath ((</>), normalise, joinPath, splitPath)
import qualified Data.List as List

-- Module Environment ----------------------------------------------------------

data ModuleEnv = ModuleEnv
  { meLoadedModules :: LoadedModules
  , meNameSeeds     :: T.NameSeeds
  , meEvalEnv       :: EvalEnv
  , meFocusedModule :: Maybe ModName
  , meSearchPath    :: [FilePath]
  , meDynEnv        :: DynamicEnv
  , meMonoBinds     :: !Bool
  }

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
  dataDir <- getDataDir
  (binDir, _) <- splitExecutablePath
  let instDir = normalise . joinPath . init . splitPath $ binDir
  userDir <- getAppUserDataDirectory "cryptol"
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
                          -- Cabal-defined data directory. Since this
                          -- is usually a global location like
                          -- /usr/local, search this one last in case
                          -- someone has multiple Cryptols
                        , dataDir
                        ]
    , meDynEnv        = mempty
    , meMonoBinds     = True
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
-- system.
--
-- This could really do with some better error handling, just returning mempty
-- when one of the imports fails isn't really desirable.
focusedEnv :: ModuleEnv -> IfaceDecls
focusedEnv me = fold $ do
  (iface,imports) <- loadModuleEnv interpImport me
  let local = unqualified (ifPublic iface `mappend` ifPrivate iface)
  return (local `shadowing` imports)

-- | Produce an ifaceDecls that represents the internal environment of the
-- module, used for typechecking.
qualifiedEnv :: ModuleEnv -> IfaceDecls
qualifiedEnv me = fold $ do
  (iface,imports) <- loadModuleEnv (\ _ iface -> iface) me
  return (mconcat [ ifPublic iface, ifPrivate iface, imports ])

loadModuleEnv :: (Import -> Iface -> Iface) -> ModuleEnv
              -> Maybe (Iface,IfaceDecls)
loadModuleEnv processIface me = do
  fm      <- meFocusedModule me
  lm      <- lookupModule fm me
  imports <- mapM loadImport (T.mImports (lmModule lm))
  return (lmInterface lm, mconcat imports)
  where
  loadImport i = do
    lm <- lookupModule (iModule i) me
    return (ifPublic (processIface i (lmInterface lm)))


-- Loaded Modules --------------------------------------------------------------

newtype LoadedModules = LoadedModules
  { getLoadedModules :: [LoadedModule]
  } deriving (Show)
-- ^ Invariant: All the dependencies of any module `m` must precede `m` in the list.

instance Monoid LoadedModules where
  mempty        = LoadedModules []
  mappend l r   = LoadedModules
                $ List.unionBy ((==) `on` lmName) (getLoadedModules l) (getLoadedModules r)

data LoadedModule = LoadedModule
  { lmName      :: ModName
  , lmFilePath  :: FilePath
  , lmInterface :: Iface
  , lmModule    :: T.Module
  } deriving (Show)

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

-- Dynamic Environments --------------------------------------------------------

-- | Extra information we need to carry around to dynamically extend
-- an environment outside the context of a single module. Particularly
-- useful when dealing with interactive declarations as in @:let@ or
-- @it@.

data DynamicEnv = DEnv
  { deNames :: R.NamingEnv
  , deDecls :: [T.DeclGroup]
  , deEnv   :: EvalEnv
  }

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
            , ifDecls    = Map.singleton (ifDeclName ifd) [ifd]
            }
          | decl <- concatMap T.groupDecls dgs
          , let ifd = mkIfaceDecl decl
          ]
