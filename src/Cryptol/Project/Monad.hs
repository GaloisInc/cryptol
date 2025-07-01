{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Cryptol.Project.Monad
  ( LoadM, Err, NoErr
  , ScanStatus(..), ChangeStatus(..), InvalidStatus(..), Parsed
  , LoadProjectMode(..)
  , runLoadM
  , doModule
  , doModuleNonFail
  , doIO
  , tryLoadM
  , liftCallback
  , addFingerprint
  , addScanned
  , getModulePathLabel
  , getCachedFingerprint
  , findModule'
  , getStatus
  , getFingerprint
  , lPutStrLn
  , getOldDocstringResults
  , getRootPath
  ) where

import           Data.Map.Strict                  (Map)
import qualified Data.Map.Strict                  as Map
import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Monad.Except hiding (tryError)
import           System.Directory
import           System.FilePath                  (makeRelative)

import           Cryptol.Utils.Ident
import           Cryptol.Parser.AST               (Module,PName)
import           Cryptol.ModuleSystem.Base        as M
import           Cryptol.ModuleSystem.Monad       as M
import           Cryptol.ModuleSystem.Env
import           Cryptol.Utils.Logger             (logPutStrLn)

import           Cryptol.Project.Config
import           Cryptol.Project.Cache

newtype LoadM err a =
  LoadM (ReaderT LoadConfig (ExceptT ModuleError (StateT LoadState ModuleM)) a)
  deriving (Functor,Applicative,Monad)

-- | Computations may raise an error
data Err

-- | Computations may not raise errors
data NoErr

type Parsed = [ (Module PName, [(ImportSource, ModulePath)]) ]

data ScanStatus =
    Scanned ChangeStatus FullFingerprint Parsed
  | Invalid InvalidStatus
  deriving Show

data ChangeStatus =
    Changed       -- ^ The module, or one of its dependencies changed.
  | Unchanged     -- ^ The module did not change.
  deriving (Eq, Show)

data InvalidStatus =
    InvalidModule ModuleError
    -- ^ Error in one of the modules in this file

  | InvalidDep ImportSource ModulePath
    -- ^ Error in one of our dependencies
  deriving Show


data LoadState = LoadState
  { findModuleCache :: Map (ModName, [FilePath]) ModulePath
    -- ^ Map (module name, search path) -> module path

  , fingerprints    :: Map CacheModulePath FullFingerprint
    -- ^ Hashes of known things.

  , scanned         :: Map ModulePath ScanStatus
    -- ^ Information about the proccessed top-level modules.
  }


-- | Information about the current project.
data LoadConfig = LoadConfig
  { canonRoot :: FilePath
    -- ^ Path to the project root, cannoicalized.

  , loadCache :: LoadCache
    -- ^ The state of the cache before we started loading the project.

  , loadCacheId :: !CacheId
    -- ^ An id for the cache when it was first loaded.
  }


-- | Do an operation in the module monad.
doModuleNonFail :: M.ModuleM a -> LoadM any a
doModuleNonFail m =
  do mb <- LoadM (lift (lift (lift (M.tryModule m))))
     case mb of
       Left err -> LoadM (throwError err)
       Right a  -> pure a

-- | Do an operation in the module monad.
doModule :: M.ModuleM a -> LoadM Err a
doModule = doModuleNonFail

-- | Do an operation in the IO monad
doIO :: IO a -> LoadM Err a
doIO m = doModule (M.io m)

tryLoadM :: LoadM Err a -> LoadM any (Either M.ModuleError a)
tryLoadM (LoadM m) = LoadM (tryError m)

-- Introduced in mtl-2.3.1 which we can't rely upon yet
tryError :: MonadError e m => m a -> m (Either e a)
tryError action = (Right <$> action) `catchError` (pure . Left)

-- | Print a line
lPutStrLn :: String -> LoadM any ()
lPutStrLn msg = doModuleNonFail (withLogger logPutStrLn msg)

-- | Lift a module level operation to the LoadM monad.
liftCallback :: (forall a. ModuleM a -> ModuleM a) -> LoadM any b -> LoadM Err b
liftCallback f (LoadM m) =
  do r <- LoadM ask
     s <- LoadM get
     (mb,s1) <- doModule (f (runStateT (runExceptT (runReaderT m r)) s))
     LoadM (put s1)
     case mb of
       Left err -> LoadM (throwError err)
       Right a  -> pure a

-- | Run a LoadM computation using the given configuration.
runLoadM ::
  LoadProjectMode {- ^ force a refresh -} ->
  Config ->
  LoadM NoErr a ->
  M.ModuleM (Map CacheModulePath FullFingerprint, Map ModulePath ScanStatus, Either ModuleError a)
runLoadM mode cfg (LoadM m) =
  do loadCfg <-
       M.io
         do path  <- canonicalizePath (root cfg)
            (cache,cacheId) <-
              case mode of
                RefreshMode  -> pure (emptyLoadCache, emptyCacheId)
                UntestedMode -> loadLoadCache
                ModifiedMode -> loadLoadCache
            pure LoadConfig { canonRoot = path
                            , loadCache = cache
                            , loadCacheId = cacheId
                            }
     let loadState = LoadState { findModuleCache = mempty
                               , fingerprints = mempty
                               , scanned = mempty
                               }
     (result, s) <- runStateT (runExceptT (runReaderT m loadCfg)) loadState
     pure (fingerprints s, scanned s, result)

addFingerprint :: ModulePath -> FullFingerprint -> LoadM any ()
addFingerprint mpath fp =
  LoadM
    (modify' \ls -> ls { fingerprints = Map.insert (toCacheModulePath mpath) fp (fingerprints ls) })


-- | Add information about the status of a module path.
addScanned :: ModulePath -> ScanStatus -> LoadM any ScanStatus
addScanned mpath status =
  do LoadM
       (modify' \ls -> ls { scanned = Map.insert mpath status (scanned ls) })
     pure status


-- | Get a label for the given module path.
-- Typically used for output.
getModulePathLabel :: ModulePath -> LoadM any String
getModulePathLabel mpath =
  case mpath of
    InFile p  -> LoadM (asks ((`makeRelative` p) . canonRoot))
    InMem l _ -> pure l

-- | Get the root of the project
getRootPath :: LoadM any FilePath
getRootPath = LoadM (asks canonRoot)

-- | Get the fingerprint for the given module path.
getCachedFingerprint :: ModulePath -> LoadM any (Maybe FullFingerprint)
getCachedFingerprint mpath =
  LoadM (asks (fmap cacheFingerprint . Map.lookup (toCacheModulePath mpath) . cacheModules . loadCache))


-- | Module path for the given import
findModule' :: ImportSource -> LoadM Err ModulePath
findModule' isrc =
  do ls <- LoadM get
     let mname = modNameToNormalModName (importedModule isrc)
     searchPath <- doModule M.getSearchPath
     case Map.lookup (mname, searchPath) (findModuleCache ls) of
       Just mpath -> pure mpath
       Nothing ->
         do modLoc <- doModule (findModule isrc mname)
            mpath  <- case modLoc of
                        InFile path -> InFile <$> doIO (canonicalizePath path)
                        InMem l c   -> pure (InMem l c)
            LoadM $ put ls { findModuleCache = Map.insert (mname, searchPath)
                                                  mpath (findModuleCache ls) }
            pure mpath

-- | Check if the given file has beein processed.
getStatus :: ModulePath -> LoadM any (Maybe ScanStatus)
getStatus mpath = LoadM (gets (Map.lookup mpath . scanned))

-- | Get the fingerpint for the ginve path, if any.
getFingerprint :: ModulePath -> LoadM any (Maybe FullFingerprint)
getFingerprint mpath = LoadM (gets (Map.lookup (toCacheModulePath mpath) . fingerprints))

getOldDocstringResults :: LoadM any (Map CacheModulePath (Maybe Bool))
getOldDocstringResults =
  LoadM (asks (fmap cacheDocstringResult . cacheModules . loadCache))
