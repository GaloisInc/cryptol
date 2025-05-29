module Config where

import Data.Text(Text)
import Control.Concurrent
import Data.Aeson qualified as JS

-- | Configuration and state of the server
newtype Config = Config {
  stateRef :: MVar State
}

data State = State {
}

-- | Make a fresh server state with the default configuration.
newConfig :: IO Config
newConfig =
  do
    ref <- newMVar State {}
    pure Config { stateRef = ref } 


-- | Update the settings based on some JSON that came from the client.
parseConfig :: Config -> JS.Value -> Either Text Config
parseConfig old _upd = Right old