{-# Language OverloadedStrings, BlockArguments #-}
module Cryptol.Project.Cache where

import           Data.Map.Strict                  (Map)
import qualified Data.Map.Strict                  as Map
import qualified Data.Set                         as Set
import qualified Data.Text.IO                     as Text
import           Data.Set                         (Set)
import           System.Directory
import           System.FilePath                  as FP
import           System.IO.Error
import qualified Toml
import qualified Toml.Schema                      as Toml
import           Cryptol.ModuleSystem.Fingerprint ( Fingerprint )
import           Cryptol.ModuleSystem.Env

-- | The load cache. This is what persists across invocations.
newtype LoadCache = LoadCache
  { cacheModules :: Map CacheModulePath CacheEntry
  }
  deriving (Show, Read)

toCacheModulePath :: ModulePath -> CacheModulePath
toCacheModulePath mpath =
  case mpath of
    InMem x _ -> CacheInMem x
    InFile x -> CacheInFile x

data CacheModulePath
  = CacheInMem String -- ^ module name
  | CacheInFile FilePath -- ^ absolute file path
  deriving (Show, Read, Ord, Eq)

instance Toml.ToValue LoadCache where
  toValue = Toml.defaultTableToValue

instance Toml.ToTable LoadCache where
  toTable x = Toml.table [
    "modules" Toml..= [
      Toml.table $ [
        case k of
          CacheInFile a -> "file" Toml..= a
          CacheInMem a -> "memory" Toml..= a,
        "fingerprint" Toml..= moduleFingerprint fp,
        "foreign_fingerprints" Toml..= Set.toList (foreignFingerprints fp),
        "include_fingerprints" Toml..= [
          Toml.table [
            "file" Toml..= k1,
            "fingerprint" Toml..= v1
          ]
          | (k1, v1) <- Map.assocs (includeFingerprints fp)
        ]
      ] ++
      [ "docstring_result" Toml..= result
        | Just result <- [cacheDocstringResult v]
      ]
      | (k,v) <- Map.assocs (cacheModules x)
      , let fp = cacheFingerprint v
    ]]

instance Toml.FromValue LoadCache where
  fromValue = Toml.parseTableFromValue
   do kvs <- Toml.reqKeyOf "modules"
           $ Toml.listOf \ _ix ->
             Toml.parseTableFromValue
             do k <- Toml.pickKey [
                    Toml.Key "memory" (fmap CacheInMem . Toml.fromValue),
                    Toml.Key "file" (fmap CacheInFile . Toml.fromValue)
                  ]
                fp <- Toml.reqKey "fingerprint"
                foreigns <- Toml.reqKey "foreign_fingerprints"
                includes <- Toml.reqKeyOf "include_fingerprints"
                          $ Toml.listOf \ _ix ->
                            Toml.parseTableFromValue
                          $ (,) <$> Toml.reqKey "file"
                                <*> Toml.reqKey "fingerprint"
                checkResult <- Toml.optKey "docstring_result"
                pure (k, CacheEntry
                  { cacheFingerprint = FullFingerprint
                      { moduleFingerprint = fp
                      , foreignFingerprints = Set.fromList foreigns
                      , includeFingerprints = Map.fromList includes
                      }
                  , cacheDocstringResult = checkResult
                  })
      pure LoadCache {
        cacheModules = Map.fromList kvs
        }

data CacheEntry = CacheEntry
  { cacheFingerprint :: FullFingerprint
  , cacheDocstringResult :: Maybe Bool
  }
  deriving (Show, Read)

-- | The full fingerprint hashes the module, but
-- also the contents of included files and foreign libraries.
data FullFingerprint = FullFingerprint
  { moduleFingerprint   :: Fingerprint
  , includeFingerprints :: Map FilePath Fingerprint
  , foreignFingerprints :: Set Fingerprint
  }
  deriving (Eq, Show, Read)

-- XXX: This should probably be a parameter
metaDir, loadCachePath :: FilePath
metaDir = ".cryproject"
loadCachePath = metaDir FP.</> "loadcache.toml"

emptyLoadCache :: LoadCache
emptyLoadCache = LoadCache { cacheModules = mempty }

loadLoadCache :: IO LoadCache
loadLoadCache =
 do txt <- Text.readFile loadCachePath
    case Toml.decode txt of
      Toml.Success _ c -> pure c
      Toml.Failure _ -> pure emptyLoadCache
  `catchIOError` \_ -> pure emptyLoadCache

saveLoadCache :: LoadCache -> IO ()
saveLoadCache cache =
  do createDirectoryIfMissing False metaDir
     writeFile loadCachePath (show (Toml.encode cache))
