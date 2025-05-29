module Handlers where

import Language.LSP.Server qualified as LSP
import qualified Language.LSP.Protocol.Types as LSP
import qualified Language.LSP.Protocol.Message as LSP
import Monad


handlers :: LSP.ClientCapabilities -> LSP.Handlers M
handlers _caps = mconcat [ 
  lspNotification LSP.SMethod_Initialized onInitialized,
  lspNotification LSP.SMethod_WorkspaceDidChangeConfiguration onConfigChanged

  ]

onInitialized :: LSP.InitializedParams -> M ()
onInitialized _ = lspShow Info "Hello"

onConfigChanged :: LSP.DidChangeConfigurationParams -> M ()
onConfigChanged _ = lspShow Info "Config Change"