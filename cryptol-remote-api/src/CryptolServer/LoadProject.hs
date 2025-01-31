{-# LANGUAGE MultiParamTypeClasses, RecordWildCards, BlockArguments, LambdaCase, TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module CryptolServer.LoadProject
  ( loadProject
  , loadProjectDescr
  , LoadProjectParams(..)
  , LoadProjectResult(..)
  )
  where

import qualified Argo.Doc as Doc
import Control.Monad.IO.Class (MonadIO(liftIO))
import Data.Aeson ((.:), (.=),FromJSON, ToJSON)
import qualified Data.Aeson as Aeson
import qualified Data.Aeson as JSON
import CryptolServer
import CryptolServer.Exceptions (configLoadError)
import qualified Cryptol.Project as Proj
import qualified Cryptol.Project.Cache as Proj
import Cryptol.ModuleSystem.Monad (runModuleM)
import Data.Map (Map)
import Cryptol.ModuleSystem.Env (ModulePath(..))
import Cryptol.ModuleSystem.Fingerprint (fingerprintHexString)
import Cryptol.Project (ScanStatus)
import Cryptol.Project.Cache (FullFingerprint(..), CacheModulePath, LoadCache)
import Cryptol.Project.Monad (ChangeStatus(..), InvalidStatus(..), Parsed, ScanStatus(..), LoadProjectMode (..))
import Cryptol.Utils.PP (pp)
import Data.Aeson.Types (Pair)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Cryptol.Parser.AST (ModuleG(mName))
import Control.Monad (join)
import Data.Typeable (typeRep, Proxy (Proxy))

loadProjectDescr :: Doc.Block
loadProjectDescr =
  Doc.Paragraph
    [ Doc.Text "Load project returning a list of all the modules and whether they have changed since the last load" ]

loadProject :: LoadProjectParams -> CryptolCommand LoadProjectResult
loadProject params = do
  
  loadRes <- liftIO (Proj.loadConfig (paramConfig params))
  case loadRes of
    Left e -> raise (configLoadError e)
    Right cfg ->
     do (fingerprints, scanStatus, testResults) <-
          liftModuleCmd (\minp -> runModuleM minp (Proj.loadProject (paramRefresh params) cfg))
        let testResults' = validateTestResults scanStatus testResults
        liftIO (Proj.saveLoadCache (buildNewCache testResults' fingerprints))
        pure LoadProjectResult {
          resultScanStatus = scanStatus,
          cachedTestResults = Map.mapMaybe id testResults'
          }

data LoadProjectResult = LoadProjectResult {
  resultScanStatus :: Map ModulePath ScanStatus,
  cachedTestResults :: Map CacheModulePath Bool
}

validateTestResults :: Map ModulePath ScanStatus -> Map CacheModulePath (Maybe Bool) -> Map CacheModulePath (Maybe Bool)
validateTestResults scan = Map.filterWithKey p
  where
    p :: CacheModulePath -> a -> Bool
    p (Proj.CacheInFile path) _
      | Just (Scanned Unchanged _ _) <- Map.lookup (InFile path) scan = True
    p _ _ = False -- don't report on built-in memory modules

buildNewCache :: Map CacheModulePath (Maybe Bool) -> Map CacheModulePath FullFingerprint -> LoadCache
buildNewCache tests fps = Proj.LoadCache {
  cacheModules = Map.mapWithKey mkEntry fps
  }
  where
    mkEntry :: CacheModulePath -> FullFingerprint -> Proj.CacheEntry
    mkEntry Proj.CacheInMem{} fp = Proj.CacheEntry fp Nothing
    mkEntry (Proj.CacheInFile path) fp = Proj.CacheEntry
      { cacheFingerprint = fp
      , cacheDocstringResult = join (Map.lookup (Proj.CacheInFile path) tests)
      }

instance ToJSON LoadProjectResult where
  toJSON LoadProjectResult{..} = JSON.object
    [ "scan_status"  .= [encodeSSEntry k v | (k, v) <- Map.assocs resultScanStatus]
    , "test_results" .= [encodeTREntry k v | (k, v) <- Map.assocs cachedTestResults]
    ]

encodeTREntry :: CacheModulePath -> Bool -> JSON.Value
encodeTREntry cmp result = JSON.object (encodeCMP cmp : ["result" .= result])

encodeSSEntry :: ModulePath -> ScanStatus -> JSON.Value
encodeSSEntry mp status =
  JSON.object $
  encodeMP mp :
  [
  case status of
    Scanned changeStatus fullFingerprint parsed ->
      "scanned" .= JSON.object ([
        "changed" .= case changeStatus of
                       Changed -> True
                       Unchanged -> False,
        "parsed" .= encodeParsed parsed] ++ encodeFPfields fullFingerprint)
    Invalid (InvalidModule moduleError) ->
      "invalid_module" .= JSON.object [
        "error" .= show (pp moduleError)
      ]
    Invalid (InvalidDep importSource modulePath) ->
      "invalid_dep" .= JSON.object (encodeMP modulePath : ["source" .= show (pp importSource)])
  ]

encodeParsed :: Parsed -> [JSON.Value]
encodeParsed p = [
   JSON.object [
    "module" .= show (pp (mName k)),
    "deps" .= [
      JSON.object (encodeMP path : [ "source" .= show (pp src)])
      | (src, path) <- v
    ]
   ]
   | (k,v) <- p]

encodeFPfields :: FullFingerprint -> [Pair]
encodeFPfields FullFingerprint{..} =
  [ "fingerprint" .= fingerprintHexString moduleFingerprint
  , "includes" .= fmap fingerprintHexString includeFingerprints
  , "foreigns" .= map fingerprintHexString (Set.elems foreignFingerprints)
  ]

encodeMP :: ModulePath -> Pair
encodeMP (InFile f) = "file" .= f
encodeMP (InMem m _) = "memory" .= m

encodeCMP :: CacheModulePath -> Pair
encodeCMP (Proj.CacheInFile f) = "file" .= f
encodeCMP (Proj.CacheInMem m) = "memory" .= m

data LoadProjectParams = LoadProjectParams {
  paramConfig :: FilePath,
  paramRefresh :: LoadProjectMode
  }

instance FromJSON LoadProjectMode where
  parseJSON = JSON.withText "LoadProjectMode"
    \case
      "modified" -> pure ModifiedMode
      "untested" -> pure UntestedMode
      "refresh"  -> pure RefreshMode
      _ -> fail "expected: modified/untested/refresh"

instance Doc.Described LoadProjectMode where
  typeName = "LoadProjectMode"
  description =
    [ Doc.Paragraph [Doc.Text ""]
    , Doc.DescriptionList
        [ ( pure (Doc.Literal "modified")
          , Doc.Paragraph [Doc.Text "Load modified files and files that depend on modified files"]
          )
        , ( pure (Doc.Literal "untested")
          , Doc.Paragraph[Doc.Text "Load files that do not have a current test result"]
          )
        , ( pure (Doc.Literal "refresh")
          , Doc.Paragraph[Doc.Text "Reload all files in the project discarding the cache results"]
          )
        ]
    ]

instance FromJSON LoadProjectParams where
  parseJSON =
    JSON.withObject "load project parameters" $
    \o -> LoadProjectParams <$> o .: "path"
                            <*> o .: "mode"

instance Doc.DescribedMethod LoadProjectParams LoadProjectResult where
  parameterFieldDescription =
    [("path", Doc.Paragraph [Doc.Text "Path to directory containing the project"])
    ,("mode", Doc.Paragraph [ Doc.Text "One of the modes described at "
                            , Doc.Link (Doc.TypeDesc (typeRep (Proxy @LoadProjectMode))) "LoadProjectMode"
                            , Doc.Text "."
                            ])
    
    ]
  resultFieldDescription =
    [("scan_status",
      Doc.Paragraph [Doc.Text "List of module name and "
                    ,Doc.Link (Doc.TypeDesc (typeRep (Proxy @ScanStatus))) " scan status"
                    ,Doc.Text "."])
    ,("test_results",
      Doc.Paragraph [Doc.Text "List of module name and cached test result."])
    ]
instance Doc.Described ScanStatus where
  typeName = "ScanStatus"
  description =
    [ Doc.Paragraph [Doc.Text "List of module names and status of each."]
    , Doc.DescriptionList
        [ ( pure (Doc.Literal "scanned")
          , Doc.Paragraph [Doc.Text "This file was successfully parsed and contains a change status."]
          )
        , ( pure (Doc.Literal "invalid_module")
          , Doc.Paragraph[Doc.Text "This file could not be parsed an analyzed due to syntax issues."]
          )
        , ( pure (Doc.Literal "invalid_dep")
          , Doc.Paragraph[Doc.Text "This file depends on a module that was not able to be loaded."]
          )
        ]
    ]
