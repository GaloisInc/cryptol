{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Cryptol.Project.Monad
  ( LoadM
  , ScanStatus(..)
  , runLoadM
  , doModule
  , doIO
  , liftCallback
  , insertScanned
  , getModulePathLabel
  , getCachedFingerprint
  , findModule'
  , getStatus
  ) where

import           Data.Map.Strict                  (Map)
import qualified Data.Map.Strict                  as Map
import           Control.Monad.Reader
import           Control.Monad.State
import           System.Directory
import           System.FilePath                  (makeRelative)

import           Cryptol.Utils.Ident
import           Cryptol.ModuleSystem.Base        as M
import           Cryptol.ModuleSystem.Monad       as M
import           Cryptol.ModuleSystem.Env

import           Cryptol.Project.Config
import           Cryptol.Project.Cache

newtype LoadM a = LoadM (ReaderT LoadConfig (StateT LoadState ModuleM) a)
  deriving (Functor,Applicative,Monad)

data ScanStatus
  = LoadedChanged
    -- ^ The module is loaded and has changed

  | LoadedNotChanged
    -- ^ The module is loaded but did not change
    -- This may happen because it is a dependency of something the did change

  | NotLoadedNotChanged
    -- ^ The module is not loaded and did not change
  deriving Eq

data LoadState = LoadState
  { findModuleCache :: Map (ModName, [FilePath]) ModulePath
    -- ^ Map (module name, search path) -> module path

  , scanned         :: Map ModulePath (FullFingerprint, ScanStatus)
    -- ^ Information about the proccessed modules.
  }

-- | Information about the current project.
data LoadConfig = LoadConfig
  { canonRoot :: FilePath
    -- ^ Path to the project root, cannoicalized.

  , loadCache :: LoadCache
    -- ^ The state of the cache before we started loading the project.

  }


-- | Do an operation in the module monad.
doModule :: M.ModuleM a ->  LoadM a
doModule m = LoadM (lift (lift m))

-- | Do an operation in the IO monad
doIO :: IO a -> LoadM a
doIO m = doModule (M.io m)

-- | Lift a module level operation to the LoadM monad.
liftCallback :: (forall a. ModuleM a -> ModuleM a) -> LoadM b -> LoadM b
liftCallback f (LoadM m) =
  do r <- LoadM ask
     s <- LoadM get
     (a,s1) <- doModule (f (runStateT (runReaderT m r) s))
     LoadM (put s1)
     pure a

-- | Run a LoadM computation using the given configuration.
runLoadM ::
  Config -> LoadM () -> M.ModuleM (Map ModulePath (FullFingerprint, ScanStatus))
runLoadM cfg (LoadM m) =
  do loadCfg <-
       M.io
         do path  <- canonicalizePath (root cfg)
            cache <- loadLoadCache
            pure LoadConfig { canonRoot = path, loadCache = cache }
     let loadState = LoadState { findModuleCache = Map.empty
                               , scanned = Map.empty
                               }
     scanned <$> execStateT (runReaderT m loadCfg) loadState

-- | Add information about the status of a module path.
insertScanned :: ModulePath -> FullFingerprint -> ScanStatus -> LoadM ()
insertScanned mpath fp status =
  LoadM
    (modify' \ls -> ls { scanned = Map.insert mpath (fp, status) (scanned ls) })


-- | Get a lab for the given module path.
-- Typically used for output.
getModulePathLabel :: ModulePath -> LoadM String
getModulePathLabel mpath =
  case mpath of
    InFile p  -> LoadM (asks ((`makeRelative` p) . canonRoot))
    InMem l _ -> pure l


-- | Get the fingerprint for the given module path.
getCachedFingerprint :: ModulePath -> LoadM (Maybe FullFingerprint)
getCachedFingerprint mpath =
  LoadM (asks (Map.lookup mpath . cacheFingerprints . loadCache))


-- | Module path for the given import
findModule' :: ImportSource -> LoadM ModulePath
findModule' isrc =
  do ls <- LoadM get
     let mname = modNameToNormalModName (importedModule isrc)
     searchPath <- doModule M.getSearchPath
     case Map.lookup (mname, searchPath) (findModuleCache ls) of
       Just mpath -> pure mpath
       Nothing ->
         do modLoc <- doModule (findModule mname)
            mpath  <- case modLoc of
                        InFile path -> InFile <$> doIO (canonicalizePath path)
                        InMem l c   -> pure (InMem l c)
            LoadM $ put ls { findModuleCache = Map.insert (mname, searchPath)
                                                  mpath (findModuleCache ls) }
            pure mpath

-- | Check if the given file has beein processed.
getStatus :: ModulePath -> LoadM (Maybe (FullFingerprint, ScanStatus))
getStatus mpath = LoadM (gets (Map.lookup mpath . scanned))
