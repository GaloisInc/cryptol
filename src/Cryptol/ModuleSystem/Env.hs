-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE PatternGuards #-}

module Cryptol.ModuleSystem.Env where

import Paths_cryptol (getDataDir)

import Cryptol.Eval (EvalEnv)
import Cryptol.ModuleSystem.Interface
import Cryptol.Parser.AST
import qualified Cryptol.TypeCheck as T
import qualified Cryptol.TypeCheck.AST as T

import Control.Monad (guard)
import Data.Foldable (fold)
import Data.Function (on)
import Data.Monoid (Monoid(..))
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
  }

initialModuleEnv :: IO ModuleEnv
initialModuleEnv  = do
  dataDir <- getDataDir
  (binDir, _) <- splitExecutablePath
  let instDir = normalise . joinPath . init . splitPath $ binDir
  return ModuleEnv
    { meLoadedModules = mempty
    , meNameSeeds     = T.nameSeeds
    , meEvalEnv       = mempty
    , meFocusedModule = Nothing
    , meSearchPath    = [dataDir </> "lib", instDir </> "lib", "."]
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
  , lmInterface :: Iface
  , lmModule    :: T.Module
  } deriving (Show)

isLoaded :: ModName -> LoadedModules -> Bool
isLoaded mn lm = any ((mn ==) . lmName) (getLoadedModules lm)

lookupModule :: ModName -> ModuleEnv -> Maybe LoadedModule
lookupModule mn env = List.find ((mn ==) . lmName) (getLoadedModules (meLoadedModules env))

addLoadedModule :: T.Module -> LoadedModules -> LoadedModules
addLoadedModule tm lm
  | isLoaded (T.mName tm) lm = lm
  | otherwise                = LoadedModules (getLoadedModules lm ++ [loaded])
  where
  loaded = LoadedModule
    { lmName      = T.mName tm
    , lmInterface = genIface tm
    , lmModule    = tm
    }
