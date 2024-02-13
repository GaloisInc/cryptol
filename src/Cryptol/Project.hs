{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE NamedFieldPuns   #-}

module Cryptol.Project
  ( Config
  , loadConfig
  , loadProject
  ) where

import           Control.Monad                    (unless, void)
import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Bifunctor
import qualified Data.ByteString                  as BS.Strict
import qualified Data.ByteString.Lazy             as BS.Lazy
import           Data.Foldable
import           Data.Map.Strict                  (Map)
import qualified Data.Map.Strict                  as Map
import           Data.Maybe
import           Data.Set                         (Set)
import qualified Data.Set                         as Set
import qualified Data.Text                        as Text
import           Data.Traversable
import           Data.YAML
import           System.Directory
import           System.FilePath                  as FP
import           System.IO.Error
import           Text.Read                        (readMaybe)

import           Cryptol.ModuleSystem.Base        as M
import           Cryptol.ModuleSystem.Env
import           Cryptol.ModuleSystem.Fingerprint
import           Cryptol.ModuleSystem.Monad       as M
import           Cryptol.Parser.AST
import           Cryptol.REPL.Command
import           Cryptol.REPL.Monad               as REPL
import           Cryptol.Utils.Ident
import           Cryptol.Utils.Logger
import           Cryptol.Utils.PP                 as PP

--------------------------------------------------------------------------------
-- Project Configuration

data Config = Config
  { root    :: FilePath
  , modules :: [FilePath] }

instance FromYAML Config where
  parseYAML = withMap "Config" \m ->
    do root    <- Text.unpack <$> m .:? "root" .!= "."
       modules <- map Text.unpack <$> m .:? "modules" .!= ["."]
       pure Config { root, modules }

data ConfigLoadError = ConfigLoadError FilePath ConfigLoadErrorInfo

data ConfigLoadErrorInfo
  = ConfigParseError BS.Lazy.ByteString (Pos, String)
  | SetRootFailed IOError

instance PP ConfigLoadError where
  ppPrec _ (ConfigLoadError path info) =
    case info of
      ConfigParseError file (pos, err) -> text $
        show topMsg ++ prettyPosWithSource pos file "\nParse error:" ++ err
      SetRootFailed ioe ->
        hang topMsg
           4 (hang "Failed to set project root:"
                 4 (text (show ioe)))
    where
    topMsg = "Error loading project configuration" <+> text path PP.<.> ":"

-- | Parse project configuration.
loadConfig :: FilePath -> IO (Either ConfigLoadError Config)
loadConfig path = do
  isDir <- doesDirectoryExist path
  let filePath = if isDir then path FP.</> "cryproject.yaml" else path
  -- Use strict IO since we are writing to the same file later
  file <- BS.Lazy.fromStrict <$> BS.Strict.readFile filePath
  first (ConfigLoadError filePath) <$>
    case decode1 file of
      Left (pos, err) -> pure (Left (ConfigParseError file (pos, err)))
      Right config ->
        first SetRootFailed <$>
        tryIOError
          do setCurrentDirectory (takeDirectory filePath FP.</> root config)
             pure config


--------------------------------------------------------------------------------
-- The Loading Monad

type LoadM = ReaderT LoadConfig (StateT LoadState ModuleM)

data ScanStatus
  = LoadedChanged
  | LoadedNotChanged
  | NotLoadedNotChanged
  deriving Eq

data LoadState = LoadState
  { findModuleCache :: Map (ModName, [FilePath]) ModulePath
    -- ^ Map (module name, search path) -> module path

  , scanned         :: Map ModulePath (FullFingerprint, ScanStatus)
  }

data FullFingerprint = FullFingerprint
  { moduleFingerprint   :: Fingerprint
  , includeFingerprints :: Map FilePath Fingerprint
  , foreignFingerprints :: Set Fingerprint }
  deriving (Eq, Show, Read)


data LoadConfig = LoadConfig
  { canonRoot :: FilePath
  , loadCache :: LoadCache
  }

doModule :: M.ModuleM a ->  LoadM a
doModule m = lift (lift m)

doIO :: IO a -> LoadM a
doIO m = doModule (M.io m)

liftCallback :: (forall a. ModuleM a -> ModuleM a) -> LoadM b -> LoadM b
liftCallback f x =
  do r <- ask
     s <- get
     (a,s1) <- doModule (f (runStateT (runReaderT x r) s))
     put s1
     pure a

runLoadM :: Config -> LoadM () -> M.ModuleM LoadState
runLoadM cfg m =
  do loadCfg <-
       M.io
         do path  <- canonicalizePath (root cfg)
            cache <- loadLoadCache
            pure LoadConfig { canonRoot = path, loadCache = cache }
     let loadState = LoadState { findModuleCache = Map.empty
                               , scanned = Map.empty
                               }
     execStateT (runReaderT m loadCfg) loadState

insertScanned :: ModulePath -> FullFingerprint -> ScanStatus -> LoadM ()
insertScanned mpath fp status =
  modify' \ls -> ls { scanned = Map.insert mpath (fp, status) (scanned ls) }


--------------------------------------------------------------------------------
-- The load cache. This is what persists across invocations.

newtype LoadCache = LoadCache
  { cacheFingerprints :: Map ModulePath FullFingerprint
  }
  deriving (Show, Read)

metaDir, loadCachePath :: FilePath
metaDir = ".cryproject"
loadCachePath = metaDir FP.</> "loadcache"

emptyLoadCache :: LoadCache
emptyLoadCache = LoadCache { cacheFingerprints = Map.empty }

loadLoadCache :: IO LoadCache
loadLoadCache =
  do txt <- readFile loadCachePath
     pure (fromMaybe emptyLoadCache (readMaybe txt))
  `catchIOError` \_ -> pure emptyLoadCache

saveLoadCache :: LoadCache -> IO ()
saveLoadCache cache =
  do createDirectoryIfMissing False metaDir
     writeFile loadCachePath (show cache)


--------------------------------------------------------------------------------

-- | Load a project.
-- Note that this does not update the Cryptol environment, it only updates
-- the project cache.
-- XXX: we probably want more functionality later on.
loadProject :: Config -> REPL CommandResult
loadProject cfg =
  do minp <- getModuleInput

     (res, warnings) <-
       REPL.io $ runModuleM minp
       do ls <- runLoadM cfg (for_ (modules cfg) loadPath)
          M.io $
            saveLoadCache LoadCache { cacheFingerprints = fst <$> scanned ls }

     printModuleWarnings warnings

     case res of

       Left err ->
         do names <- mctxNameDisp <$> REPL.getFocusedEnv
            rPrint (pp (ModuleSystemError names err))
            pure emptyCommandResult { crSuccess = False }

       Right _ ->
        do rPutStrLn "all loaded!"
           pure emptyCommandResult


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
  do ls <- get
     case Map.lookup mpath (scanned ls) of
       Just (_, status) -> pure status
       Nothing ->
         liftCallback (errorInFile mpath)
         do root <- asks canonRoot

           -- XXX: Use the logger from REPL?
            doModule $ withLogger logPutStrLn $
               "Scanning " ++ case mpath of
                                InFile p  -> makeRelative root p
                                InMem l _ -> l

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

            fps <- asks (cacheFingerprints . loadCache)
            status <-
              case Map.lookup mpath fps of
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
       do ls' <- get
          case Map.lookup mpath (scanned ls') of
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
                 fps <- asks (cacheFingerprints . loadCache)
                 insertScanned mpath newFp
                   case Map.lookup mpath fps of
                     Just oldFp | oldFp == newFp -> LoadedNotChanged
                     _                           -> LoadedChanged


-- | Module path for the given import
findModule' :: ImportSource -> LoadM ModulePath
findModule' isrc =
  do let mname = modNameToNormalModName (importedModule isrc)
     searchPath <- doModule M.getSearchPath
     ls <- get
     case Map.lookup (mname, searchPath) (findModuleCache ls) of
       Just mpath -> pure mpath
       Nothing ->
         do modLoc <- doModule (findModule mname)
            mpath  <- case modLoc of
                        InFile path -> InFile <$> doIO (canonicalizePath path)
                        InMem l c   -> pure (InMem l c)
            put ls { findModuleCache = Map.insert (mname, searchPath)
                                                  mpath (findModuleCache ls) }
            pure mpath


-- | Fingerprints of foreign declarations
getForeignFps :: Map FilePath Bool -> M.ModuleM (Set Fingerprint)
getForeignFps fsrcPaths =
  Set.fromList <$>
    for (Map.keys fsrcPaths) \fsrcPath ->
      M.io (fingerprintFile fsrcPath) >>=
        \case
           Left ioe -> otherIOError fsrcPath ioe
           Right fp -> pure fp



