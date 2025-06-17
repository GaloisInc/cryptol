module Load (reload) where

import Data.Set qualified as Set
import Data.Map(Map)
import Data.Map qualified as Map
import Data.Maybe(fromMaybe,mapMaybe)
import MonadLib

import Cryptol.Parser.Position(thing,srcRange,Range)
import Cryptol.ModuleSystem
import Cryptol.ModuleSystem.Env
import Cryptol.ModuleSystem.Base qualified as Base
import Cryptol.ModuleSystem.Monad
import Cryptol.Utils.PP
import Cryptol.Utils.Logger
import Cryptol.ModuleSystem.Fingerprint
import Cryptol.Parser.AST qualified as P
import Cryptol.TypeCheck.PP qualified as T
import Cryptol.TypeCheck.Error qualified as T

import Language.LSP.Server qualified as LSP
import Language.LSP.Protocol.Types qualified as LSP

import State
import Monad
import Index

-- | Reload all open modules
reload :: M ()
reload =
  LSP.withIndefiniteProgress "cryptol" Nothing LSP.NotCancellable \sendMsg ->
  do
    uris <- cryRoots <$> getState
    let paths = mapMaybe LSP.uriToFilePath (Set.toList uris)
        m = runLoadM emptyLoadS
              (updateLoadedFiles >> mapM_ (loadPath Nothing . InFile) paths)
    doModuleCmd' (\x -> lspLog Info x >> sendMsg x) (`runModuleM` m) \ws mb ->
      case mb of
        Left err -> sendDiagnostics ws [err]
        Right (_,loadS) ->
          do 
            sendDiagnostics ws (loadErrs loadS)
            let new = Map.keysSet (Map.filter (== Loaded) (loadStatus loadS))
                reindex ent = loadedEntPath ent `Set.member` new
            update_ \s ->
                let env  = minpModuleEnv (cryState s)
                    ents = filter reindex (Map.elems (getLoadedEntities (meLoadedModules env)))
                in s { cryIndex = updateIndexes ents (cryIndex s) }

dbg :: Doc -> LoadM ()
dbg x = when False (doLift (withLogger logPutStr (show x)))

-- | Load the modules from the given import source
doLoadFrom :: ImportSource -> LoadM Status
doLoadFrom isrc =
  do
    dbg ("Load from" <+> pp isrc)
    let n = importedModule isrc
    done <- getModStatus n
    case done of
      Just s -> pure s
      Nothing ->
        do
          mbPath <- liftMaybe (Base.findModule isrc n)
          case mbPath of
            Nothing   -> pure Errors
            Just path -> loadPath (Just isrc) path

-- | Load an already parsed module
loadParsed ::
  ModulePath                {- ^ Location of module -} ->
  Fingerprint               {- ^ Fingerprint for location -} ->
  Map FilePath Fingerprint  {- ^ Fingerprints for includes -} ->
  Bool                      {- ^ Did the fingerprints change -} ->
  Maybe ImportSource        {- ^ Why are we loading this -} ->
  P.Module P.PName          {- ^ The parsed module -} ->
  LoadM Status
loadParsed path fp deps weChanged mbisrc pm0 =
  nowLoading isrc
    do
      changes <- mapM doLoadFrom ds
      status <-
        case mconcat changes of
          Loaded -> load
          Unchanged
            | weChanged -> load
            | otherwise -> pure Unchanged 
          Errors -> badDep mbisrc >> pure Errors
      setModStatus mo status
      pure status
  >>= maybe (badDep (Just isrc) >> pure Errors) pure
  where
  pm    = Base.addPrelude pm0
  mo    = thing (P.mName pm)
  ds    = Base.findDeps pm
  imps  = Set.fromList (map importedModule ds)
  isrc  = fromMaybe (FromModule mo) mbisrc
  load  =
    do
      doLift (unloadModule (\lm -> lmName lm == thing (P.mName pm)))
      mb <- liftMaybe (Base.doLoadModule False False isrc path fp deps pm imps)
      case mb of
        Nothing -> badDep mbisrc >> pure Errors
        Just _  -> pure Loaded -- XXX: we could start indexing here

-- | Load the modules in the given path
loadPath ::
  Maybe ImportSource ->
  ModulePath -> LoadM Status
loadPath mbisrc path =
  do
    dbg ("Load path:" <+> pp path)
    mbParsed <- liftMaybe (errorInFile path (Base.parseModule path))
    case mbParsed of
      Nothing -> setLoadStatus path Errors >> badDep mbisrc >> pure Errors
      Just (fp,deps,pms) ->
        do
          mb <- getOldFile path
          let weChanged =
                case mb of
                  Just info -> fiFingerprint info /= fp || fiIncludeDeps info /= deps
                  _ -> True
          status <- mconcat <$> mapM (loadParsed path fp deps weChanged mbisrc) pms
          setLoadStatus path status
          pure status




--------------------------------------------------------------------------------  

newtype LoadM a = LoadM (StateT LoadS ModuleM a)
  deriving (Functor,Applicative,Monad)

data LoadS = LoadS {
  loadErrs        :: [ModuleError],
  -- ^ Errors we encounted

  oldLoadedFiles  :: Map ModulePath FileInfo,
  -- ^ Information about loaded files before we started loading

  loadStatus      :: Map ModulePath Status,
  -- ^ Information about files we've processed
  
  loadModStatus   :: Map P.ModName Status
  -- ^ Information about modules we've processed
}

emptyLoadS :: LoadS
emptyLoadS = LoadS {
  loadErrs = [],
  loadStatus = mempty,
  oldLoadedFiles = mempty,
  loadModStatus = mempty
}

-- | Status of a file or a module
data Status = Unchanged | Errors | Loaded
  deriving (Eq,Show)

instance Semigroup Status where
  x <> y =
    case x of
      Errors      -> Errors
      Unchanged   -> y
      Loaded ->
        case y of
          Errors -> Errors
          _      -> Loaded

instance Monoid Status where
  mempty = Unchanged


-- | Do some loading
runLoadM :: LoadS -> LoadM a -> ModuleM (a, LoadS)
runLoadM s (LoadM m) = runStateT s m

-- | Do a command that might fail
liftMaybe :: ModuleM a -> LoadM (Maybe a)
liftMaybe m =
  LoadM
  do
    mb <- lift (tryModule m)
    case mb of
      Left err -> sets \s -> (Nothing, s { loadErrs = err : loadErrs s })
      Right a  -> pure (Just a)

-- | Do a command that we are sure does not fail
doLift :: ModuleM a -> LoadM a
doLift m = LoadM (lift m)

-- | Mark a module as being loaded, to detect recursive modules
nowLoading :: ImportSource -> LoadM a -> LoadM (Maybe a)
nowLoading isrc m =
  do
    s <- LoadM get
    mb <- liftMaybe (loading isrc (runLoadM s m))
    case mb of
      Nothing -> pure Nothing
      Just (a,s1) -> LoadM (sets (const (Just a,s1)))
    
-- | Set information about loaded files.  Done once at the start of loading.
updateLoadedFiles :: LoadM ()
updateLoadedFiles =
  do
    env <- doLift getModuleEnv
    LoadM $ sets_ \s -> s { oldLoadedFiles = getLoadedFiles (meLoadedModules env) }

-- | Get info about previously loaded files
getOldFile :: ModulePath -> LoadM (Maybe FileInfo)
getOldFile path = LoadM (Map.lookup path . oldLoadedFiles <$> get)

-- | Set the status for a file
setLoadStatus :: ModulePath -> Status -> LoadM ()
setLoadStatus m sta = LoadM (sets_ \s -> s { loadStatus = Map.insert m sta (loadStatus s) })

-- | Set the status for a module
setModStatus :: P.ModName -> Status -> LoadM ()
setModStatus m sta = LoadM (sets_ \s -> s { loadModStatus = Map.insert m sta (loadModStatus s) })

-- | Get the status for a module
getModStatus :: P.ModName -> LoadM (Maybe Status)
getModStatus mo = LoadM (Map.lookup mo . loadModStatus <$> get)

-- | Get the path for a loaded entity
loadedEntPath :: LoadedEntity -> ModulePath
loadedEntPath ent =
  case ent of
    ALoadedModule lm -> lmFilePath lm
    ALoadedFunctor lm -> lmFilePath lm
    ALoadedInterface lm -> lmFilePath lm

-- | Get the location of an import
impSrcLoc :: ImportSource -> Maybe Range
impSrcLoc isrc =
  case isrc of
    FromModule {} -> Nothing
    FromImport l -> Just (srcRange l)
    FromSigImport l -> Just (srcRange l)
    FromModuleInstance l -> Just (srcRange l)

-- | Record an error at the given inmport
badDep :: Maybe ImportSource -> LoadM ()
badDep mbisrc =
  case mbisrc of
    Just isrc ->
      case impSrcLoc isrc of
        Just r ->
          LoadM (sets_ \s -> s { loadErrs = TypeCheckingFailed isrc T.emptyNameMap [(r,T.TemporaryError "Import contains errors")] : loadErrs s })
        Nothing -> pure ()
    Nothing -> pure ()