{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE LambdaCase        #-}
module Cryptol.Project
  ( Config(..)
  , loadConfig
  , ScanStatus(..)
  , loadProject
  , loadProjectREPL
  ) where

import           Control.Monad                    (void,unless)
import           Data.Foldable
import           Data.Map.Strict                  (Map)
import qualified Data.Map.Strict                  as Map
import           Data.Maybe
import           Data.Set                         (Set)
import qualified Data.Set                         as Set
import           Data.Traversable
import           System.Directory
import           System.FilePath                  as FP
import           System.IO.Error

import           Cryptol.ModuleSystem.Base        as M
import           Cryptol.ModuleSystem.Env
import           Cryptol.ModuleSystem.Fingerprint
import           Cryptol.ModuleSystem.Monad       as M
import           Cryptol.Parser.AST
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

       Right _ ->
        do rPutStrLn "all loaded!"
           pure emptyCommandResult


-- | Load a project.
-- Returns information about the modules that are part of the project.
loadProject :: Config -> M.ModuleM (Map ModulePath ScanStatus)
loadProject cfg =
   do info <- runLoadM cfg (for_ (modules cfg) scanPath)
      let cache = LoadCache { cacheFingerprints = fst <$> info }
      M.io (saveLoadCache cache)
      pure (snd <$> info)


--------------------------------------------------------------------------------

{- NOTE:
In the functions below:
  * "scan" refers to processing a module, but not necesserily loading it,
  * "load" means that we are actually loading the module.
-}



-- | Process all .cry files in the given path.
scanPath :: FilePath -> LoadM ()
scanPath path =
  do isDir <- doIO (doesDirectoryExist path)
     if isDir
       then
         doIO (tryIOError (listDirectory path)) >>=
         \case
           Left err      -> doModule (otherIOError path err)
           Right entries -> for_ entries \entry -> scanPath (path FP.</> entry)
       else
         -- XXX: This should probably handle other extenions
         -- (literate Cryptol)
         case takeExtension path of
           ".cry" -> scanFromPath path
           _      -> pure ()


-- | Process a particular file path.
scanFromPath :: FilePath -> LoadM ()
scanFromPath fpath =
  liftCallback (withPrependedSearchPath [takeDirectory fpath])
  do foundFPath <- doModule (M.findFile fpath)
     mpath      <- doIO (InFile <$> canonicalizePath foundFPath)
     void (scan Nothing mpath)


-- | Process a particular import source.
scanFromImportSource :: ImportSource -> LoadM ScanStatus
scanFromImportSource isrc =
  do mpath <- findModule' isrc
     scan (Just isrc) mpath


-- | Process the given module, and return information about what happened.
scan :: Maybe ImportSource -> ModulePath -> LoadM ScanStatus
scan mbIsrc mpath =
  do mbStat <- getStatus mpath
     case mbStat of
       Just (_, status) -> pure status
       Nothing ->
         liftCallback (errorInFile mpath)
         do lab <- getModulePathLabel mpath
            lPutStrLn ("Scanning " ++ lab)

            (fi, parsed, foreignFps) <-
               doModule
               do (fi, parsed) <- parseWithDeps mpath
                  foreignFps   <- getForeignFps (fiForeignDeps fi)
                  pure (fi, parsed, foreignFps)

            let newFp =
                  FullFingerprint
                    { moduleFingerprint   = fiFingerprint fi
                    , includeFingerprints = fiIncludeDeps fi
                    , foreignFingerprints = foreignFps
                    }

                loadChanged =
                  LoadedChanged <$
                    load mbIsrc mpath
                                  (fiFingerprint fi) (fiIncludeDeps fi) parsed

            mbOldFP <- getCachedFingerprint mpath
            status <-
              case mbOldFP of
                Just oldFp | oldFp == newFp ->
                  do let currentModNames = map (thing . mName . fst) parsed
                     depStatuses <-
                        traverse scanFromImportSource
                          [ dep
                          | (_,deps) <- parsed
                          , dep      <- deps
                          , importedModule dep `notElem` currentModNames
                          ]

                     if LoadedChanged `elem` depStatuses
                       then loadChanged
                       else pure NotLoadedNotChanged
                _ -> loadChanged

            insertScanned mpath newFp status
            pure status



-- | Load a module that we have not yet parsed.
parseAndLoad ::
  ImportSource ->
  ModulePath ->
  LoadM (Fingerprint, Map FilePath Fingerprint, [FileInfo])
parseAndLoad isrc mpath =
  do (newModFp, newIncFps, pms) <- doModule (parseModule mpath)
     fis <- load (Just isrc) mpath newModFp newIncFps
              [ (pm', findDeps pm')
              | pm <- pms
              , let pm' = addPrelude pm
              ]
     pure (newModFp, newIncFps, fis)



-- | Load a bunch of parsed modules.
load ::
  Maybe ImportSource ->
  ModulePath ->
  Fingerprint ->
  Map FilePath Fingerprint ->
  [(ModuleG ModName PName, [ImportSource])] ->
  LoadM [FileInfo]
load mbIsrc mpath newModFp newIncFps mods =
  for mods \(pm, deps) ->
    do let isrc = fromMaybe (FromModule (thing (mName pm))) mbIsrc
       liftCallback (loading isrc)
        do traverse_ loadFromImportSource deps
           doModule $ fmap snd $
             doLoadModule True False isrc mpath newModFp newIncFps pm $
               Set.fromList (map importedModule deps)


-- | This does the actual loading of the module (unless it is already loaded).
loadFromImportSource :: ImportSource -> LoadM ()
loadFromImportSource isrc =
  do mpath <- findModule' isrc
     let unlessLoaded k =
           do loaded <- doModule (M.isLoadedStrict (importedModule isrc) mpath)
              unless loaded k

     liftCallback (errorInFile mpath)
       do mbScanned <- getStatus mpath
          case mbScanned of
            Just (fp, status) ->
              case status of
                LoadedChanged -> pure ()
                LoadedNotChanged -> pure ()
                NotLoadedNotChanged ->
                  unlessLoaded
                    do _ <- parseAndLoad isrc mpath
                       insertScanned mpath fp LoadedNotChanged

             -- The file has not been fully loaded yet, but the individual
             -- module within the file might
            Nothing ->
              unlessLoaded
              do (newModFp, newIncFps, fis) <- parseAndLoad isrc mpath
                 foreignFps <-
                   doModule $ getForeignFps $
                      Map.unionsWith (||) (map fiForeignDeps fis)
                 let newFp = FullFingerprint
                       { moduleFingerprint = newModFp
                       , includeFingerprints = newIncFps
                       , foreignFingerprints = foreignFps
                       }
                 mbOldFP <- getCachedFingerprint mpath
                 insertScanned mpath newFp
                   case mbOldFP of
                     Just oldFp | oldFp == newFp -> LoadedNotChanged
                     _                           -> LoadedChanged


-- | Get the fingerprints for external libraries.
getForeignFps :: Map FilePath Bool -> ModuleM (Set Fingerprint)
getForeignFps fsrcPaths =
  Set.fromList <$>
    for (Map.keys fsrcPaths) \fsrcPath ->
      M.io (fingerprintFile fsrcPath) >>=
        \case
           Left ioe -> otherIOError fsrcPath ioe
           Right fp -> pure fp



