{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeFamilies      #-}

module Cryptol.Project
  ( Config
  , loadConfig
  , run
  ) where

import           Control.Monad (unless)
import           Control.Monad.Except
import           Control.Monad.State
import           Data.Aeson
import           Data.Foldable
import           Data.Functor
import           Data.Map.Strict                  (Map)
import qualified Data.Map.Strict                  as Map
import           Data.Maybe
import           Data.Set                         (Set)
import qualified Data.Set                         as Set
import           Data.Traversable
import           Data.Yaml
import           GHC.Generics
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

type family MaybeIf (opt :: Bool) t where
  MaybeIf 'True t = Maybe t
  MaybeIf 'False t = t

data GenericConfig (opt :: Bool) = Config
  { root    :: MaybeIf opt FilePath
  , modules :: MaybeIf opt [FilePath] }
  deriving Generic

type ParsedConfig = GenericConfig 'True
type Config = GenericConfig 'False

instance FromJSON ParsedConfig where
  parseJSON = genericParseJSON defaultOptions { rejectUnknownFields = True }

data ConfigLoadError = ConfigLoadError FilePath ConfigLoadErrorInfo

data ConfigLoadErrorInfo
  = ConfigParseError ParseException
  | SetRootFailed IOError

instance PP ConfigLoadError where
  ppPrec _ (ConfigLoadError path info) =
    hang ("Error loading project configuration" <+> text path PP.<.> ":")
       4 (pp info)

instance PP ConfigLoadErrorInfo where
  ppPrec _ (ConfigParseError exn) =
    text (prettyPrintParseException exn)
  ppPrec _ (SetRootFailed ioe) =
    hang "Failed to set project root:"
       4 (text (show ioe))

loadConfig :: FilePath -> IO (Either ConfigLoadError Config)
loadConfig path = do
  isDir <- doesDirectoryExist path
  let filePath = if isDir then path FP.</> "cryproject.yaml" else path
  runExceptT $ withExceptT (ConfigLoadError filePath) do
    Config {..} <- withExceptT ConfigParseError do
      ExceptT (decodeFileEither @ParsedConfig filePath)
        <&> \Config {..} -> Config
          { root = fromMaybe "." root
          , modules = fromMaybe ["."] modules } :: Config
    withExceptT SetRootFailed $ ExceptT $ tryIOError $
      setCurrentDirectory (takeDirectory filePath FP.</> root)
    pure Config {..}

data FullFingerprint = FullFingerprint
  { moduleFingerprint   :: Fingerprint
  , includeFingerprints :: Map FilePath Fingerprint
  , foreignFingerprints :: Set Fingerprint }
  deriving (Eq, Show, Read)

data ScanStatus
  = LoadedChanged
  | LoadedNotChanged
  | NotLoadedNotChanged
  deriving Eq

data LoadState = LoadState
  { findModuleCache :: Map (ModName, [FilePath]) ModulePath
  , scanned         :: Map ModulePath (FullFingerprint, ScanStatus) }

type LoadM = StateT LoadState ModuleM

liftCallback :: (forall a. ModuleM a -> ModuleM a) -> LoadM b -> LoadM b
liftCallback f x = StateT (f . runStateT x)

newtype LoadCache = LoadCache
  { cacheFingerprints :: Map ModulePath FullFingerprint }
  deriving (Show, Read)

metaDir, loadCachePath :: FilePath
metaDir = ".cryproject"
loadCachePath = metaDir FP.</> "loadcache"

emptyLoadCache :: LoadCache
emptyLoadCache = LoadCache { cacheFingerprints = Map.empty }

run :: Config -> REPL CommandResult
run Config {..} = do
  canonRoot <- REPL.io $ canonicalizePath root
  minp <- getModuleInput
  (res, warnings) <- REPL.io $ runModuleM minp do
    loadCache <- M.io $
      (fromMaybe emptyLoadCache . readMaybe <$> readFile loadCachePath)
      `catchIOError` \_ -> pure emptyLoadCache
    let scanFromPath :: FilePath -> LoadM ()
        scanFromPath fpath =
          liftCallback (withPrependedSearchPath [takeDirectory fpath]) do
            foundFPath <- lift $ M.findFile fpath
            mpath <- lift $ InFile <$> M.io (canonicalizePath foundFPath)
            void $ scan Nothing mpath
        scan :: Maybe ImportSource -> ModulePath -> LoadM ScanStatus
        scan mbIsrc mpath = do
          ls <- get
          case Map.lookup mpath (scanned ls) of
            Just (_, status) -> pure status
            Nothing -> liftCallback (errorInFile mpath) do
              lift $ withLogger logPutStrLn $
                "Scanning " ++ case mpath of
                  InFile p  -> makeRelative canonRoot p
                  InMem l _ -> l
              (fi, pmDeps) <- lift $ findDepsOf' mpath
              foreignFps <- getForeignFps $ Map.keysSet (fiForeignDeps fi)
              let newFp = FullFingerprint
                    { moduleFingerprint = fiFingerprint fi
                    , includeFingerprints = fiIncludeDeps fi
                    , foreignFingerprints = foreignFps }
                  loadChanged = LoadedChanged <$ load mbIsrc mpath
                    (fiFingerprint fi) (fiIncludeDeps fi) pmDeps
              status <- case Map.lookup mpath (cacheFingerprints loadCache) of
                Just oldFp
                  | oldFp == newFp -> do
                    let currentModNames = map (thing . mName . fst) pmDeps
                    depStatuses <- traverse scanFromImportSource $
                      filter ((`notElem` currentModNames) . importedModule) $
                        concatMap snd pmDeps
                    if LoadedChanged `elem` depStatuses
                      then loadChanged
                      else pure NotLoadedNotChanged
                _ -> loadChanged
              insertScanned mpath newFp status
              pure status
        scanFromImportSource :: ImportSource -> LoadM ScanStatus
        scanFromImportSource isrc = do
          mpath <- findModule' isrc
          scan (Just isrc) mpath
        parseAndLoad :: ImportSource -> ModulePath -> LoadM (Fingerprint, Map FilePath Fingerprint, [FileInfo])
        parseAndLoad isrc mpath = do
          (newModFp, newIncFps, pms) <- lift $ parseModule mpath
          fis <- load (Just isrc) mpath newModFp newIncFps $
            map (\pm -> let pm' = addPrelude pm in (pm', findDeps pm')) pms
          pure (newModFp, newIncFps, fis)
        load mbIsrc mpath newModFp newIncFps pmDeps =
          for pmDeps \(pm, deps) -> do
            let isrc = fromMaybe (FromModule (thing (mName pm))) mbIsrc
            liftCallback (loading isrc) do
              traverse_ loadFromImportSource deps
              lift $ fmap snd $
                doLoadModule True False isrc mpath newModFp newIncFps pm $
                  Set.fromList $ map importedModule deps
        getForeignFps :: Set FilePath -> LoadM (Set Fingerprint)
        getForeignFps fsrcPaths = lift $
          Set.fromList <$> for (Set.toList fsrcPaths) \fsrcPath ->
            M.io (fingerprintFile fsrcPath) >>= \case
              Left ioe -> otherIOError fsrcPath ioe
              Right fp -> pure fp
        insertScanned mpath fp status = modify' \ls -> ls
          { scanned = Map.insert mpath (fp, status) (scanned ls) }
        findModule' :: ImportSource -> LoadM ModulePath
        findModule' isrc = do
          let mname = modNameToNormalModName $ importedModule isrc
          searchPath <- lift M.getSearchPath
          ls <- get
          case Map.lookup (mname, searchPath) (findModuleCache ls) of
            Just mpath -> pure mpath
            Nothing -> do
              mpath <- lift $ findModule mname >>= \case
                InFile path -> InFile <$> M.io (canonicalizePath path)
                InMem l c -> pure $ InMem l c
              put ls
                { findModuleCache =
                    Map.insert (mname, searchPath) mpath (findModuleCache ls) }
              pure mpath
        loadFromImportSource :: ImportSource -> LoadM ()
        loadFromImportSource isrc = do
          mpath <- findModule' isrc
          liftCallback (errorInFile mpath) do
            ls' <- get
            case Map.lookup mpath (scanned ls') of
              Just (fp, status) ->
                case status of
                  LoadedChanged -> pure ()
                  LoadedNotChanged -> pure ()
                  NotLoadedNotChanged -> do
                    loaded <- lift $ M.isLoadedStrict (importedModule isrc) mpath
                    unless loaded do
                      _ <- parseAndLoad isrc mpath
                      insertScanned mpath fp LoadedNotChanged
              Nothing -> do
                -- The file has not been fully loaded yet, but the individual
                -- module within the file might
                loaded <- lift $ M.isLoadedStrict (importedModule isrc) mpath
                unless loaded do
                  (newModFp, newIncFps, fis) <- parseAndLoad isrc mpath
                  foreignFps <- getForeignFps $
                    Set.unions $ map (Map.keysSet . fiForeignDeps) fis
                  let newFp = FullFingerprint
                        { moduleFingerprint = newModFp
                        , includeFingerprints = newIncFps
                        , foreignFingerprints = foreignFps }
                  insertScanned mpath newFp
                    case Map.lookup mpath (cacheFingerprints loadCache) of
                      Just oldFp
                        | oldFp == newFp -> LoadedNotChanged
                      _ -> LoadedChanged
    ls <- flip execStateT
      LoadState { findModuleCache = Map.empty, scanned = Map.empty } $
      for_ modules \p -> do
        let loadPath path = do
              isDir <- lift $ M.io $ doesDirectoryExist path
              if isDir
                then lift (M.io (tryIOError (listDirectory path))) >>= \case
                  Left err -> lift $ otherIOError path err
                  Right entries -> for_ entries \case
                    '.':_ -> pure ()
                    entry -> loadPath (path FP.</> entry)
                else case takeExtension path of
                  ".cry" -> scanFromPath path
                  _      -> pure ()
        loadPath p
    let newLoadCache = LoadCache
          { cacheFingerprints = Map.map fst (scanned ls) }
    M.io do
      createDirectoryIfMissing False metaDir
      writeFile loadCachePath $ show newLoadCache
  printModuleWarnings warnings
  case res of
    Left err -> do
      names <- mctxNameDisp <$> REPL.getFocusedEnv
      rPrint $ pp $ ModuleSystemError names err
      pure emptyCommandResult { crSuccess = False }
    Right _ -> do
      rPutStrLn "all loaded!"
      pure emptyCommandResult
