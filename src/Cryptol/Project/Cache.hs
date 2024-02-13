module Cryptol.Project.Cache where

import           Data.Map.Strict                  (Map)
import qualified Data.Map.Strict                  as Map
import qualified Data.Text                        as Text
import qualified Data.Text.IO                     as Text
import           Data.Set                         (Set)
import           Data.Maybe                       (fromMaybe)
import           System.Directory
import           System.FilePath                  as FP
import           System.IO.Error
import           Text.Read                        (readMaybe)

import           Cryptol.ModuleSystem.Env
import           Cryptol.ModuleSystem.Fingerprint

-- | The load cache. This is what persists across invocations.
newtype LoadCache = LoadCache
  { cacheFingerprints :: Map ModulePath FullFingerprint
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
loadCachePath = metaDir FP.</> "loadcache"

emptyLoadCache :: LoadCache
emptyLoadCache = LoadCache { cacheFingerprints = Map.empty }

loadLoadCache :: IO LoadCache
loadLoadCache =
  do txt <- Text.readFile loadCachePath
     pure $! fromMaybe emptyLoadCache (readMaybe (Text.unpack txt))
  `catchIOError` \_ -> pure emptyLoadCache

saveLoadCache :: LoadCache -> IO ()
saveLoadCache cache =
  do createDirectoryIfMissing False metaDir
     writeFile loadCachePath (show cache)


