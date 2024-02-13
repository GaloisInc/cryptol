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
import           Cryptol.Utils.Logger
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
   do info <- runLoadM cfg (for_ (modules cfg) loadPath)
      let cache = LoadCache { cacheFingerprints = fst <$> info }
      M.io (saveLoadCache cache)
      pure (snd <$> info)

-- | Search for .cry files in the given path.
loadPath :: FilePath -> LoadM ()
loadPath path =
  do isDir <- doIO (doesDirectoryExist path)
     if isDir
       then
         doIO (tryIOError (getDirectoryContents path)) >>=
         \case
           Left err      -> doModule (otherIOError path err)
           Right entries -> for_ entries \entry -> loadPath (path FP.</> entry)
       else
         case takeExtension path of
           ".cry" -> scanFromPath path
           _      -> pure ()


-- | Load a particular file path.
scanFromPath :: FilePath -> LoadM ()
scanFromPath fpath =
  liftCallback (withPrependedSearchPath [takeDirectory fpath])
  do foundFPath <- doModule (M.findFile fpath)
     mpath      <- doIO (InFile <$> canonicalizePath foundFPath)
     void (scan Nothing mpath)


-- | Scan from a particular import source.
scanFromImportSource :: ImportSource -> LoadM ScanStatus
scanFromImportSource isrc =
  do mpath <- findModule' isrc
     scan (Just isrc) mpath


-- | This does the actual scanning work.
scan :: Maybe ImportSource -> ModulePath -> LoadM ScanStatus
scan mbIsrc mpath =
  do mbStat <- getStatus mpath
     case mbStat of
       Just (_, status) -> pure status
       Nothing ->
         liftCallback (errorInFile mpath)
         do lab <- getModulePathLabel mpath

           -- XXX: Use the logger from REPL?
            doModule (withLogger logPutStrLn ("Scanning " ++ lab))

            (fi, pmDeps) <- doModule (findDepsOf' mpath)
            foreignFps <- doModule (getForeignFps (fiForeignDeps fi))

            let newFp =
                  FullFingerprint
                    { moduleFingerprint   = fiFingerprint fi
                    , includeFingerprints = fiIncludeDeps fi
                    , foreignFingerprints = foreignFps
                    }

                loadChanged =
                  LoadedChanged <$
                    load mbIsrc mpath
                                  (fiFingerprint fi) (fiIncludeDeps fi) pmDeps

            mbOldFP <- getCachedFingerprint mpath
            status <-
              case mbOldFP of
                Just oldFp | oldFp == newFp ->
                  do let currentModNames = map (thing . mName . fst) pmDeps
                     depStatuses <-
                        traverse scanFromImportSource
                          [ src
                          | (_,srcs) <- pmDeps
                          , src      <- srcs
                          , importedModule src `notElem` currentModNames
                          ]

                     if LoadedChanged `elem` depStatuses
                       then loadChanged
                       else pure NotLoadedNotChanged
                _ -> loadChanged

            insertScanned mpath newFp status
            pure status



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



{- | Process stuff we parsed from a file.
The reason we have a list of modules here, rather than just one,
is that a single file may contain multiple modules, due to to desugaring
of various things in the module system. -}
load ::
  Maybe ImportSource ->
  ModulePath ->
  Fingerprint ->
  Map FilePath Fingerprint ->
  [(ModuleG ModName PName, [ImportSource])] ->
  LoadM [FileInfo]
load mbIsrc mpath newModFp newIncFps pmDeps =
  for pmDeps \(pm, deps) ->
    do let isrc = fromMaybe (FromModule (thing (mName pm))) mbIsrc
       liftCallback (loading isrc)
        do traverse_ loadFromImportSource deps
           doModule $ fmap snd $
             doLoadModule True False isrc mpath newModFp newIncFps pm $
               Set.fromList (map importedModule deps)

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
                 foreignFps <- doModule $ getForeignFps $
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

-- | Fingerprints of foreign declarations
getForeignFps :: Map FilePath Bool -> M.ModuleM (Set Fingerprint)
getForeignFps fsrcPaths =
  Set.fromList <$>
    for (Map.keys fsrcPaths) \fsrcPath ->
      M.io (fingerprintFile fsrcPath) >>=
        \case
           Left ioe -> otherIOError fsrcPath ioe
           Right fp -> pure fp



