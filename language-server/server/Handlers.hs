module Handlers where

import Data.Map qualified as Map
import Control.Lens((^.))
import Language.LSP.Server qualified as LSP
import Language.LSP.Protocol.Types(type (|?))
import qualified Language.LSP.Protocol.Types as LSP
import qualified Language.LSP.Protocol.Message as LSP
import qualified Language.LSP.Protocol.Lens as LSP
import Monad
import Config
import SyntaxHighlight

handlers :: LSP.ClientCapabilities -> LSP.Handlers M
handlers _caps = mconcat [ 
  lspNotification LSP.SMethod_Initialized onInitialized,
  lspNotification LSP.SMethod_WorkspaceDidChangeConfiguration onConfigChanged,

  lspNotification LSP.SMethod_TextDocumentDidOpen onDocumentOpen,
  lspNotification LSP.SMethod_TextDocumentDidChange onDocumentChange,
  lspNotification LSP.SMethod_TextDocumentDidSave onDocumentSave,
  lspNotification LSP.SMethod_TextDocumentDidClose onDocumentClose,
  
  lspSyncRequest LSP.SMethod_TextDocumentHover onHover,
  lspSyncRequest LSP.SMethod_TextDocumentSemanticTokensFull onSemTokFull,
  lspSyncRequest LSP.SMethod_TextDocumentSemanticTokensRange onSemTokRange
  ]

onInitialized :: LSP.InitializedParams -> M ()
onInitialized _ = lspShow Info "Hello"

onConfigChanged :: LSP.DidChangeConfigurationParams -> M ()
onConfigChanged _ = lspShow Info "Config Change"

onDocumentOpen :: LSP.DidOpenTextDocumentParams -> M ()
onDocumentOpen _ps = pure () 

onDocumentChange :: LSP.DidChangeTextDocumentParams -> M ()
onDocumentChange _ps = pure ()

onDocumentSave :: LSP.DidSaveTextDocumentParams -> M ()
onDocumentSave ps =
  do let doc = ps ^. LSP.textDocument . LSP.uri
     update_ \s -> s { lexedFiles = Map.delete doc (lexedFiles s) }
     requestSemTokUpdate
     pure ()

onDocumentClose :: LSP.DidCloseTextDocumentParams -> M ()
onDocumentClose ps =
  do
    let doc = ps ^. LSP.textDocument . LSP.uri
    update_ \s -> s { lexedFiles = Map.delete doc (lexedFiles s) }
  

onHover :: LSP.HoverParams -> M (LSP.Hover |? LSP.Null)
onHover ps = pure res
  where
  doc = ps ^. LSP.textDocument
  pos = ps ^. LSP.position
  res = LSP.InL LSP.Hover {
    _range = Nothing,
    _contents = LSP.InL LSP.MarkupContent {
      _kind = LSP.MarkupKind_Markdown,
      _value = "hover *yes*"  
    }
  }

requestSemTokUpdate :: M ()
requestSemTokUpdate =
  do
    _ <- LSP.sendRequest LSP.SMethod_WorkspaceSemanticTokensRefresh Nothing 
          (const (pure ()))
    pure ()

onSemTokFull :: LSP.SemanticTokensParams -> M (LSP.SemanticTokens |? LSP.Null)
onSemTokFull ps =
  do let doc = ps ^. (LSP.textDocument . LSP.uri)
     sendSemanticTokens =<< semanticTokens doc Nothing

onSemTokRange :: LSP.SemanticTokensRangeParams -> M  (LSP.SemanticTokens |? LSP.Null)
onSemTokRange ps =
  do let doc = ps ^. (LSP.textDocument . LSP.uri)
     sendSemanticTokens =<< semanticTokens doc (Just (ps ^. LSP.range))
    
sendSemanticTokens :: [LSP.SemanticTokenAbsolute] -> M  (LSP.SemanticTokens |? LSP.Null)
sendSemanticTokens toks
  | null toks = pure (LSP.InR LSP.Null)
  | otherwise =
    case LSP.makeSemanticTokens LSP.defaultSemanticTokensLegend toks of
      Right a -> pure (if null toks then LSP.InR LSP.Null else LSP.InL a)
      Left err ->
        do
          lspShow Error err
          pure (LSP.InR LSP.Null)