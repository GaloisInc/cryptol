{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE LambdaCase        #-}
module Cryptol.Project
  ( Config(..)
  , loadConfig
  , ScanStatus(..)
  , ChangeStatus(..)
  , InvalidStatus(..)
  , LoadProjectMode(..)
  , Parsed
  , loadProject
  , depMap
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
import           Cryptol.Project.Config
import           Cryptol.Project.Cache
import           Cryptol.Project.Monad
import qualified Cryptol.Parser.AST as P
import Cryptol.Parser.Position (Located(..))

-- | Load a project.
-- Returns information about the modules that are part of the project.
loadProject :: LoadProjectMode -> Config -> M.ModuleM (Map CacheModulePath FullFingerprint, Map ModulePath ScanStatus, Map CacheModulePath (Maybe Bool))
loadProject mode cfg =
   do (fps, statuses, out) <- runLoadM mode cfg (for_ (modules cfg) scanPath >> getOldDocstringResults)
      let deps = depMap [p | Scanned _ _ ps <- Map.elems statuses, p <- ps]
      
      let untested (InMem{}) = False
          untested (InFile f) =
            case out of
              Left _ -> True
              Right m -> Map.lookup (CacheInFile f) m /= Just (Just True)

      let needLoad = case mode of
            RefreshMode  -> [thing (P.mName m) | Scanned _ _ ps <- Map.elems statuses, (m, _) <- ps]
            ModifiedMode -> [thing (P.mName m) | Scanned Changed _ ps <- Map.elems statuses, (m, _) <- ps]
            UntestedMode -> [thing (P.mName m) | (k, Scanned ch _ ps) <- Map.assocs statuses, ch == Changed || untested k,  (m, _) <- ps]
      let order = loadOrder deps needLoad

      let modDetails = Map.fromList [(thing (P.mName m), (m, mp, fp)) | (mp, Scanned _ fp ps) <- Map.assocs statuses, (m, _) <- ps]

      let fingerprints = Map.fromList [(path, moduleFingerprint ffp) | (CacheInFile path, ffp) <- Map.assocs fps]

      for_ order \name ->
        let (m, path, fp) = modDetails Map.! name in
        -- XXX: catch modules that don't load?
        doLoadModule
          True {- eval -}
          False {- quiet -}
          (FromModule name)
          path
          (moduleFingerprint fp)
          fingerprints
          m
          (Map.findWithDefault mempty name deps)

      let oldResults =
            case out of
              Left{} -> mempty
              Right x -> x
      pure (fps, statuses, oldResults)


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
    let foundFiles = Map.keys (Map.filter id fsrcPaths) in
    for foundFiles \fsrcPath ->
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


depMap :: Parsed -> Map P.ModName (Set P.ModName)
depMap xs = Map.fromList [(thing (P.mName k), Set.fromList [importedModule i | (i, _) <- v]) | (k, v) <- xs]

loadOrder :: Map P.ModName (Set P.ModName) -> [P.ModName] -> [P.ModName]
loadOrder deps roots0 = snd (go Set.empty roots0) []
  where
    go seen mms =
      case mms of
        [] -> (seen, id)
        m : ms
          | Set.member m seen -> go seen ms
          | (seen1, out1) <- go (Set.insert m seen) (Set.toList (Map.findWithDefault mempty m deps))
          , (seen2, out2) <- go seen1 ms
          -> (seen2, out1 . (m:) . out2)
