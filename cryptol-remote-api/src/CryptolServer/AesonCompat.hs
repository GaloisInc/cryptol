{-# LANGUAGE CPP #-}

-- | A compatibility shim for papering over the differences between
-- @aeson-2.0.*@ and pre-2.0.* versions of @aeson@.
--
-- TODO: When the ecosystem widely uses @aeson-2.0.0.0@ or later, remove this
-- module entirely.
module CryptolServer.AesonCompat where

import Data.HashMap.Strict (HashMap)
import Data.Text (Text)

#if MIN_VERSION_aeson(2,0,0)
import Data.Aeson.Key (Key)
import qualified Data.Aeson.Key as K
import Data.Aeson.KeyMap (KeyMap)
import qualified Data.Aeson.KeyMap as KM
#else
import qualified Data.HashMap.Strict as HM
#endif

#if MIN_VERSION_aeson(2,0,0)
type KeyCompat = Key

deleteKM :: Key -> KeyMap v -> KeyMap v
deleteKM = KM.delete

fromListKM :: [(Key, v)] -> KeyMap v
fromListKM = KM.fromList

keyFromText :: Text -> Key
keyFromText = K.fromText

keyToText :: Key -> Text
keyToText = K.toText

lookupKM :: Key -> KeyMap v -> Maybe v
lookupKM = KM.lookup

toHashMapTextKM :: KeyMap v -> HashMap Text v
toHashMapTextKM = KM.toHashMapText

toListKM :: KeyMap v -> [(Key, v)]
toListKM = KM.toList
#else
type KeyCompat = Text

deleteKM :: Text -> HashMap Text v -> HashMap Text v
deleteKM = HM.delete

fromListKM :: [(Text, v)] -> HashMap Text v
fromListKM = HM.fromList

keyFromText :: Text -> Text
keyFromText = id

keyToText :: Text -> Text
keyToText = id

lookupKM :: Text -> HashMap Text v -> Maybe v
lookupKM = HM.lookup

toHashMapTextKM :: HashMap Text v -> HashMap Text v
toHashMapTextKM = id

toListKM :: HashMap Text v -> [(Text, v)]
toListKM = HM.toList
#endif
