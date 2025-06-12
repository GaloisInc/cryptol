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
  liftIO,
  doModuleCmd', doModuleCmd, doModuleCmd_
)where

import Data.Text(Text)
import Data.Text qualified as Text
import Data.Map qualified as Map
import Control.Lens((^.))

import Colog.Core.Action((<&))
import Colog.Core.Severity(Severity(..),WithSeverity(..))
import Control.Monad.IO.Class(liftIO)
import Control.Concurrent
import Language.LSP.Server qualified as LSP
import Language.LSP.Server qualified as SLSP
import Language.LSP.Protocol.Message qualified as LSP
import Language.LSP.Protocol.Lens qualified as LSP
import Language.LSP.Logging qualified as LSP
import Cryptol.Utils.PP
import Cryptol.ModuleSystem
import State
import Error

-- | The language server monad.
type M = LSP.LspM Config

-- | Do this when the client-side configuration changes.
onConfigChange :: Config -> M ()
onConfigChange cfg =
  update_ \s -> 
    let inp   = cryState s
        me    = minpModuleEnv inp
        meNew = me { meSearchPath = crySearchPath cfg }
    in s { cryState = inp { minpModuleEnv = meNew } }

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

-- | Get a snapshot of the server state.  Blocks if someone is modifying it.
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


-- | Execute a Cryptol command.  All interactions with Cryptol should happen
-- through this, as it coordinates the acces to the Cryptol environment.
doModuleCmd' ::
  ModuleCmd a -> ([ModuleWarning] -> Either ModuleError a -> M ()) -> M ()
doModuleCmd' m k =
  do
    refs  <- getConfig
    senv <- LSP.getLspEnv
    _tid <- liftIO $ forkIO $
      do
        (warns,res) <-
          withMVar (cryWorking refs) \_ ->
            do
              s <- readMVar (stateRef refs)
              (a,ws) <- m (cryState s)
              case a of
                Left err -> pure (ws, Left err)
                Right (res,newEnv) ->
                  do
                    modifyMVar_ (stateRef refs) \s1 ->
                      pure s1 { cryState =
                                  (cryState s) { minpModuleEnv = newEnv } }
                    pure (ws, Right res)
        LSP.runLspT senv (k warns res)
    pure ()


doModuleCmd ::
  ModuleCmd a -> (Maybe a -> M ()) -> M ()
doModuleCmd m k =
  doModuleCmd' m \ws mbRes ->
    do
      let (err,res) =
            case mbRes of
              Left e -> (Just e, Nothing)
              Right a -> (Nothing, Just a)
          (haveErrs, dsMap) = diagnostics err ws
          ds = Map.toList dsMap
      case err of
        Just e | not haveErrs ->
          lspShow Error (Text.pack (show (pp e)))
        _ -> pure ()
      LSP.flushDiagnosticsBySource 10 (Just "cryptol")
      mapM_ (\(u,d) -> SLSP.publishDiagnostics 10 u Nothing d) ds
      k res

doModuleCmd_ :: ModuleCmd a -> M ()
doModuleCmd_ m = doModuleCmd m (const (pure ()))

