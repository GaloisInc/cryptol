module Monad (
  M, 
  onConfigChange,
  lspNotification,
  lspSyncRequest,
  lspAsyncRequest,
  Severity(..),
  lspLog,
  lspShow,
  getConfig,
  update, update_,
  getState,
  liftIO
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

-- | Update the server state.  Blocks if someone else is modifying it.
-- Readers are blocks while this is executign.
update :: (Config -> State -> IO (State, a)) -> M a
update f =
  do cfg <- getConfig
     liftIO (modifyMVar (stateRef cfg) (f cfg))

update_ :: (State -> State) -> M ()
update_ f = update \_ s -> pure (f s, ())

-- | Access the server state.  Blocks if someone is modifying it.
getState :: M State
getState =
  do cfg <- getConfig
     liftIO (readMVar (stateRef cfg))

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

-- | Hand a request, asyncrohously
lspAsyncRequest ::
  LSP.SMethod (m :: LSP.Method LSP.ClientToServer LSP.Request) ->
    (LSP.MessageParams m -> M (LSP.MessageResult m)) ->
    LSP.Handlers M
lspAsyncRequest m f =
  LSP.requestHandler m \msg k ->
    do
      env <- LSP.getLspEnv
      _ <- liftIO (forkIO (LSP.runLspT env (k . Right =<< f (msg ^. LSP.params))))
      pure ()

  -- | Log a message to the client.
lspLog :: Severity -> Text -> M ()
lspLog ty msg = LSP.logToLogMessage <& WithSeverity msg ty

-- | Show a visible message to the client.
lspShow :: Severity -> Text -> M ()
lspShow ty msg = LSP.logToShowMessage <& WithSeverity msg ty