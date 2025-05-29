module Config where

import Data.Text(Text)
import Data.Map(Map)
import Control.Concurrent
import Data.Aeson qualified as JS
import Language.LSP.Protocol.Types qualified as LSP

-- | Configuration and state of the server
newtype Config = Config {
  stateRef :: MVar State
}

data State = State {
  lexedFiles :: Map LSP.Uri [LSP.SemanticTokenAbsolute]
}

-- | Make a fresh server state with the default configuration.
newConfig :: IO Config
newConfig =
  do
    ref <- newMVar State {
      lexedFiles = mempty
    }
    pure Config { stateRef = ref } 


-- | Update the settings based on some JSON that came from the client.
parseConfig :: Config -> JS.Value -> Either Text Config
parseConfig old _upd = Right old