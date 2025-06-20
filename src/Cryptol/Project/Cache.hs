{-# Language OverloadedStrings, BlockArguments, BangPatterns #-}
module Cryptol.Project.Cache where

import           Data.Map.Strict                  (Map)
import qualified Data.Map.Strict                  as Map
import qualified Data.Set                         as Set
import qualified Data.Text                        as Text
import qualified Data.Text.Encoding               as Text
import qualified Data.ByteString                  as BS
import           Data.Set                         (Set)
import           System.Directory
import           System.FilePath                  as FP
import           System.IO.Error
import qualified Toml
import qualified Toml.Schema                      as Toml
import qualified Crypto.Hash.SHA256               as SHA256
import           Cryptol.ModuleSystem.Fingerprint ( Fingerprint )
import           Cryptol.ModuleSystem.Env

-- | This is something to identify a particular cache state.
-- We use a hash of the cache file at the moment.
type CacheId = BS.ByteString

emptyCacheId :: CacheId
emptyCacheId = BS.empty

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
    "version" Toml..= (1 :: Int), -- increase this to invalidate old files
                                  -- also look at the `Toml.FromValue` instance
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
   do 1 <- Toml.reqKey "version" :: Toml.ParseTable l Int
      kvs <- Toml.reqKeyOf "modules"
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

-- | Directory where to store the project state.
-- XXX: This should probably be a parameter
metaDir :: FilePath
metaDir = ".cryproject"

loadCachePath :: FilePath
loadCachePath = metaDir FP.</> "loadcache.toml"

emptyLoadCache :: LoadCache
emptyLoadCache = LoadCache { cacheModules = mempty }

-- | Load a cache.  Also returns an id for the cahce.
-- If there is no cache (or it failed to load), then we return an empty id.
loadLoadCache :: IO (LoadCache, CacheId)
loadLoadCache =
 do bytes <- BS.readFile loadCachePath
    let hash = SHA256.hash bytes
        txt = Text.decodeUtf8 bytes
    case Toml.decode txt of
      Toml.Success _ c -> pure (c,hash)
      Toml.Failure _ -> pure (emptyLoadCache,emptyCacheId)
  `catchIOError` \_ -> pure (emptyLoadCache,emptyCacheId)

-- | Save the cache.  Returns an id for the cache.
saveLoadCache :: LoadCache -> IO BS.ByteString
saveLoadCache cache =
  do createDirectoryIfMissing False metaDir
     let txt = Text.pack (show (Toml.encode cache))
         !bytes = Text.encodeUtf8 txt
     BS.writeFile loadCachePath bytes
     pure (SHA256.hash bytes)
