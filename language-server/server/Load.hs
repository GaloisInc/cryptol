module Load (reload) where

import Data.Set(Set)
import Data.Set qualified as Set
import Data.Map(Map)
import Data.Map qualified as Map
import Data.Maybe(fromMaybe,mapMaybe)
import MonadLib

import Cryptol.Utils.PP
import Cryptol.Utils.Logger
import Cryptol.Parser.Position(thing,srcRange,Range)
import Cryptol.ModuleSystem
import Cryptol.ModuleSystem.Env
import Cryptol.ModuleSystem.Base qualified as Base
import Cryptol.ModuleSystem.Monad
import Cryptol.Utils.Ident
import Cryptol.Parser.AST qualified as P
import Cryptol.TypeCheck.AST qualified as T
import Cryptol.TypeCheck.PP qualified as T
import Cryptol.TypeCheck.Error qualified as T

import Language.LSP.Server qualified as LSP
import Language.LSP.Protocol.Types qualified as LSP

import State
import Monad
import Index


data Status = Unchanged | Errors | Loaded
  deriving Eq

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



newtype LoadM a = LoadM (StateT LoadS ModuleM a)
  deriving (Functor,Applicative,Monad)

runLoadM :: LoadS -> LoadM a -> ModuleM (a, LoadS)
runLoadM s (LoadM m) = runStateT s m

data LoadS = LoadS {
  loadErrs   :: [ModuleError],
  loadStatus :: Map ModulePath Status
}

emptyLoadS :: LoadS
emptyLoadS = LoadS { loadErrs = [], loadStatus = mempty }

liftMaybe :: ModuleM a -> LoadM (Maybe a)
liftMaybe m =
  LoadM
  do
    mb <- lift (tryModule m)
    case mb of
      Left err -> sets \s -> (Nothing, s { loadErrs = err : loadErrs s })
      Right a  -> pure (Just a)

doLift :: ModuleM a -> LoadM a
doLift m = LoadM (lift m)

nowLoading :: ImportSource -> LoadM a -> LoadM a
nowLoading isrc m = LoadM
  do
    s <- get
    (a,s1) <- lift (loading isrc (runLoadM s m))
    set s1
    pure a

getLoadStatus :: LoadM (Map ModulePath Status)
getLoadStatus = LoadM (loadStatus <$> get)

setLoadStatus :: ModulePath -> Status -> LoadM ()
setLoadStatus m sta = LoadM (sets_ \s -> s { loadStatus = Map.insert m sta (loadStatus s) })

_doMsg :: Doc -> LoadM ()
_doMsg m =
  doLift (withLogger logPutStr (show m))


loadedEntPath :: LoadedEntity -> ModulePath
loadedEntPath ent =
  case ent of
    ALoadedModule lm -> lmFilePath lm
    ALoadedFunctor lm -> lmFilePath lm
    ALoadedInterface lm -> lmFilePath lm

impSrcLoc :: ImportSource -> Maybe Range
impSrcLoc isrc =
  case isrc of
    FromModule {} -> Nothing
    FromImport l -> Just (srcRange l)
    FromSigImport l -> Just (srcRange l)
    FromModuleInstance l -> Just (srcRange l)

badDep :: Maybe ImportSource -> LoadM ()
badDep mbisrc =
  case mbisrc of
    Just isrc ->
      case impSrcLoc isrc of
        Just r ->
          LoadM (sets_ \s -> s { loadErrs = TypeCheckingFailed isrc T.emptyNameMap [(r,T.TemporaryError "Import contains errors")] : loadErrs s })
        Nothing -> pure ()
    Nothing -> pure ()

doLoadFrom :: ImportSource -> LoadM Status
doLoadFrom isrc =
  do
    -- doMsg ("Considering " <+> pp isrc)
    let n = importedModule isrc
    mb   <- doLift (getLoadedMaybe n)
    done <- getLoadStatus

    case mb of

      -- We checked this already?
      Just m
        | let pa = lmFilePath m,
          Just s <- Map.lookup pa done ->
        do
          case s of
            Errors -> badDep (Just isrc)
            _ -> pure ()
          pure s
       
      _ ->
        do
          mbPath <- liftMaybe (Base.findModule isrc n)
          case mbPath of
            Nothing   -> pure Errors
            Just path -> doLoad' mb (Just isrc) path


doLoadDeps :: P.ModuleG mname name -> LoadM (Status, Set ModName)
doLoadDeps m0 =
  do
    let ds = Base.findDeps m0 
    changes <- mapM doLoadFrom ds -- XXX: if a depency fails, it'd be nice to report a diagnostic at the imports
    pure (mconcat changes, Set.fromList (map importedModule ds))


doLoad' ::
  Maybe (LoadedModuleG T.TCTopEntity) ->
  Maybe ImportSource ->
  ModulePath -> LoadM Status
doLoad' mb mbisrc path =
  do
    -- doMsg ("Parsging" <+> pp path)
    mbParsed <- liftMaybe $ errorInFile path $ Base.parseModule path
    case mbParsed of
      Nothing -> {-doMsg "Parse error" >>-} setLoadStatus path Errors >> badDep mbisrc >> pure Errors
      Just (fp,deps,pms) ->
        do
          let weChanged =
                case mb of
                  Just m -> fiFingerprint info /= fp || fiIncludeDeps info /= deps
                        where info = lmFileInfo m
                  _ -> True
          -- doMsg "Parsing OK"
          status <- mconcat <$> forM pms \pm0 ->
            let pm = Base.addPrelude pm0
                isrc = fromMaybe (FromModule (thing (P.mName pm))) mbisrc in
            nowLoading isrc
            do
                  
              (status,imps) <- doLoadDeps pm
              let 
                  load =
                    do
                      doLift $ unloadModule (\lm -> lmName lm == thing (P.mName pm))
                      -- doMsg ("Loading" <+> pp (P.mName pm))
                      mbOk <- liftMaybe (Base.doLoadModule False False isrc path fp deps pm imps)
                      case mbOk of
                        Nothing -> badDep mbisrc >> pure Errors
                        Just _  -> pure Loaded -- XXX: we could start indexing here
              case status of
                Loaded -> {-doMsg "Deps changes" >>-} load
                Unchanged
                  | weChanged -> {-doMsg ("Deps unchanged, we chanegd" <+> maybe "(not loaded)" (const "(loaded)") mb) >>-} load
                  | otherwise -> {-doMsg "Unchanged" >>-} pure Unchanged 
                Errors -> {-doMsg "Error in deps" >>-} badDep mbisrc >> pure Errors
          setLoadStatus path status
          pure status


doLoadEntry :: FilePath -> LoadM Status
doLoadEntry path =
  do
    env <- doLift getModuleEnv
    let ents = Map.toList (getLoadedEntities (meLoadedModules env))
        matches fp (m,ent) =
          case ent of
            ALoadedModule lm | lmFilePath lm == fp -> pure lm { lmData = T.TCTopModule (lmModule lm) }
            ALoadedFunctor lm | lmFilePath lm == fp -> pure lm { lmData = T.TCTopModule (lmModule lm) }
            ALoadedInterface lm | lmFilePath lm == fp -> pure lm { lmData = T.TCTopSignature m (lmData lm) }
            _ -> Nothing
        known = msum (map (matches (InFile path)) ents)
    doLoad' known Nothing (InFile path)


reload :: M ()
reload =
  LSP.withIndefiniteProgress "cryptol" Nothing LSP.NotCancellable \sendMsg ->
  do
    uris <- cryRoots <$> getState
    let paths = mapMaybe LSP.uriToFilePath (Set.toList uris)
        m = runLoadM emptyLoadS
                (mapM_ doLoadEntry paths)
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

  