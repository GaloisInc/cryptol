{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE LambdaCase        #-}
module Cryptol.Project
  ( Config(..)
  , loadConfig
  , ScanStatus(..)
  , loadProject
  , loadProjectREPL
  ) where

import           Control.Monad                    (void)
import           Data.Foldable
import           Data.Map.Strict                  (Map)
import qualified Data.Map.Strict                  as Map
import           Data.Set                         (Set)
import qualified Data.Set                         as Set
import           Data.Traversable
import           System.Directory
import           System.FilePath                  as FP

import           Cryptol.ModuleSystem.Base        as M
import           Cryptol.ModuleSystem.Env
import           Cryptol.ModuleSystem.Fingerprint
import           Cryptol.ModuleSystem.Monad       as M
import           Cryptol.REPL.Command
import           Cryptol.REPL.Monad               as REPL
import           Cryptol.Utils.PP                 as PP
import           Cryptol.Project.Config
import           Cryptol.Project.Cache
import           Cryptol.Project.Monad


-- | Load a project.
-- Note that this does not update the Cryptol environment, it only updates
-- the project cache.
-- XXX: Probably should move this in REPL
loadProjectREPL :: Config -> REPL CommandResult
loadProjectREPL cfg =
  do minp <- getModuleInput
     (res, warnings) <- REPL.io $ runModuleM minp $ loadProject cfg
     printModuleWarnings warnings
     case res of
       Left err ->
         do names <- mctxNameDisp <$> REPL.getFocusedEnv
            rPrint (pp (ModuleSystemError names err))
            pure emptyCommandResult { crSuccess = False }

       Right (mp,_) -> do
         -- rPutStrLn "all loaded!"
        rPutStrLn $ unlines
          [ ppScanStatus v ++ " " ++ show (pp k)
          | (k,v) <- Map.toList mp
          ]
        pure emptyCommandResult

-- | Load a project.
-- Returns information about the modules that are part of the project.
loadProject :: Config -> M.ModuleM (Map ModulePath ScanStatus)
loadProject cfg =
   do (fps, status) <- runLoadM cfg (for_ (modules cfg) scanPath)
      let cache = LoadCache { cacheFingerprints = fps }
      M.io (saveLoadCache cache)
      pure status


--------------------------------------------------------------------------------

-- | Process all .cry files in the given path.
scanPath :: FilePath -> LoadM any ()
scanPath path =
  tryLoadM (doIO (doesDirectoryExist path)) >>=
  \case
    Left {} -> pure ()

    Right True ->
      tryLoadM (doIO (listDirectory path)) >>=
        \case
           Left {} -> pure ()
           Right entries ->
             for_ entries \entry -> scanPath (path FP.</> entry)

    Right False ->
      -- XXX: This should probably handle other extenions
      -- (literate Cryptol)
      case takeExtension path of
        ".cry" -> void (tryLoadM (scanFromPath path))
                  -- XXX: failure: file disappeared.
        _      -> pure ()


-- | Process a particular file path.
-- Fails if we can't find the module at this path.
scanFromPath :: FilePath -> LoadM Err ScanStatus
scanFromPath fpath =
  liftCallback (withPrependedSearchPath [takeDirectory fpath])
  do foundFPath <- doModule (M.findFile fpath)
     mpath      <- doIO (InFile <$> canonicalizePath foundFPath)
     scan mpath


-- | Process the given module, and return information about what happened.
-- Also, saves the status of the module path.
scan :: ModulePath -> LoadM any ScanStatus
scan mpath =

  tryIt $
  do mbStat <- getStatus mpath
     case mbStat of
       Just status -> pure status

       Nothing ->
         do (newFp,parsed) <- doParse mpath
            mbOldFP <- getCachedFingerprint mpath
            let needLoad = mbOldFP /= Just newFp
            let deps     = [ dep
                           | (_,ds) <- parsed
                           , dep@(_,otherPath) <- ds
                           , mpath /= otherPath
                           ]
            mb <- checkDeps False deps
            case mb of
              Left (a,b) -> addScanned mpath (Invalid (InvalidDep a b))
              Right depChanges ->
                do let ch = if needLoad || depChanges
                            then Changed else Unchanged
                   addScanned mpath (Scanned ch newFp parsed)
  where
  tryIt m =
    do mb <- tryLoadM m
       case mb of
         Left err -> addScanned mpath (Invalid (InvalidModule err))
         Right a  -> pure a


-- | Parse a module.
doParse :: ModulePath -> LoadM Err (FullFingerprint, Parsed)
doParse mpath =
  do lab <- getModulePathLabel mpath
     lPutStrLn ("Scanning " ++ lab)

     (parsed, newFp) <-
        doModule
        do (fi, parsed) <- parseWithDeps mpath
           foreignFps   <- getForeignFps (fiForeignDeps fi)
           pure ( parsed
                , FullFingerprint
                    { moduleFingerprint   = fiFingerprint fi
                    , includeFingerprints = fiIncludeDeps fi
                    , foreignFingerprints = foreignFps
                    }
                 )
     addFingerprint mpath newFp
     ps <- forM parsed \(m,ds) ->
             do paths <- mapM findModule' ds
                pure (m, zip ds paths)
     pure (newFp, ps)

-- | Get the fingerprints for external libraries.
getForeignFps :: Map FilePath Bool -> ModuleM (Set Fingerprint)
getForeignFps fsrcPaths =
  Set.fromList <$>
    for (Map.keys fsrcPaths) \fsrcPath ->
      M.io (fingerprintFile fsrcPath) >>=
        \case
           Left ioe -> otherIOError fsrcPath ioe
           Right fp -> pure fp

-- | Scan the dependencies of a module.
checkDeps ::
  Bool {- ^ Should we load the dependencies -} ->
  [(ImportSource,ModulePath)] {- ^ The dependencies -} ->
  LoadM err (Either (ImportSource,ModulePath) Bool)
  -- ^ Returns `Left bad_dep` if one of the dependencies fails to load.
  -- Returns `Right changes` if all dependencies were validated correctly.
  -- The boolean flag `changes` indicates if any of the dependencies contain
  -- changes and so we should also load the main module.
checkDeps shouldLoad ds =
  case ds of
    [] -> pure (Right shouldLoad)
    (imp, mpath) : more ->
      do status <- scan mpath
         case status of
           Invalid {} -> pure (Left (imp,mpath))
           Scanned ch _ _ ->
             case ch of
               Changed   -> checkDeps True more
               Unchanged -> checkDeps shouldLoad more

