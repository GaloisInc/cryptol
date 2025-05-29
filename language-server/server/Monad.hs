module Monad (
  M, 
  onConfigChange,
  lspNotification,
  lspSyncRequest,
  Severity(..),
  lspLog,
  lspShow,
  getConfig,
  update
)where

import Data.Text
import Control.Lens((^.))

import Colog.Core.Action((<&))
import Colog.Core.Severity(Severity(..),WithSeverity(..))
import Control.Monad.IO.Class(liftIO)
import Control.Concurrent
import Language.LSP.Server qualified as LSP
import Language.LSP.Protocol.Message qualified as LSP
import Language.LSP.Protocol.Lens qualified as LSP
import Language.LSP.Logging qualified as LSP

import Config

-- | The language server monad.
type M = LSP.LspM Config

-- | Do this when the client-side configuration changes.
onConfigChange :: Config -> M ()
onConfigChange _cfg = pure ()

getConfig :: M Config
getConfig = LSP.getConfig

update :: (Config -> State -> IO (State, a)) -> M a
update f =
  do cfg <- getConfig
     liftIO (modifyMVar (stateRef cfg) (f cfg))


-- | Handle a notification.
lspNotification ::
  LSP.SMethod (m :: LSP.Method LSP.ClientToServer LSP.Notification) ->
  (LSP.MessageParams m -> M ()) ->
  LSP.Handlers M
lspNotification m f =
  LSP.notificationHandler m \msg -> f (msg ^. LSP.params)

-- | Handle a request, synchronously.
lspSyncRequest ::
  LSP.SMethod (m :: LSP.Method LSP.ClientToServer LSP.Request) ->
  (LSP.MessageParams m -> M (LSP.MessageResult m)) ->
  LSP.Handlers M
lspSyncRequest m f =
  LSP.requestHandler m \msg k -> k . Right =<< f (msg ^. LSP.params)

  -- | Log a message to the client.
lspLog :: Severity -> Text -> M ()
lspLog ty msg = LSP.logToLogMessage <& WithSeverity msg ty

-- | Show a visible message to the client.
lspShow :: Severity -> Text -> M ()
lspShow ty msg = LSP.logToShowMessage <& WithSeverity msg ty