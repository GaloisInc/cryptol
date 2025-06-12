module Handlers where

import Data.Text qualified as Text
import Data.Map qualified as Map
import Control.Lens((^.))
import Language.LSP.Server qualified as LSP
import Language.LSP.Protocol.Types(type (|?))
import qualified Language.LSP.Protocol.Types as LSP
import qualified Language.LSP.Protocol.Message as LSP
import qualified Language.LSP.Protocol.Lens as LSP

import Cryptol.Utils.PP(pp)

import Monad
import State
import Load
import SyntaxHighlight
import Index
import Position

handlers :: LSP.ClientCapabilities -> LSP.Handlers M
handlers _caps = mconcat [ 
  lspNotification LSP.SMethod_Initialized onInitialized,
  lspNotification LSP.SMethod_WorkspaceDidChangeConfiguration onConfigChanged,

  lspNotification LSP.SMethod_TextDocumentDidOpen onDocumentOpen,
  lspNotification LSP.SMethod_TextDocumentDidChange onDocumentChange,
  lspNotification LSP.SMethod_TextDocumentDidSave onDocumentSave,
  lspNotification LSP.SMethod_TextDocumentDidClose onDocumentClose,
  
  lspSyncRequest LSP.SMethod_TextDocumentHover onHover,
  lspSyncRequest LSP.SMethod_TextDocumentDefinition onGotoDefinition,

  lspSyncRequest LSP.SMethod_TextDocumentFoldingRange onFoldingRange,

  lspSyncRequest LSP.SMethod_TextDocumentSemanticTokensFull onSemTokFull,
  lspSyncRequest LSP.SMethod_TextDocumentSemanticTokensRange onSemTokRange
  ]

onInitialized :: LSP.InitializedParams -> M ()
onInitialized _ = lspShow Info "Welcome to Cryptol!"

onConfigChanged :: LSP.DidChangeConfigurationParams -> M ()
onConfigChanged _ = pure ()
      
onDocumentOpen :: LSP.DidOpenTextDocumentParams -> M ()
onDocumentOpen ps = doLoad (ps ^. LSP.textDocument . LSP.uri)

onDocumentChange :: LSP.DidChangeTextDocumentParams -> M ()
onDocumentChange _ps = pure ()

onDocumentSave :: LSP.DidSaveTextDocumentParams -> M ()
onDocumentSave ps =
  do let doc = ps ^. LSP.textDocument . LSP.uri
     update_ \s -> s { lexedFiles = Map.delete doc (lexedFiles s) }
     requestSemTokUpdate
     doLoad doc
     pure ()

onDocumentClose :: LSP.DidCloseTextDocumentParams -> M ()
onDocumentClose ps =
  do
    let doc = ps ^. LSP.textDocument . LSP.uri
    update_ \s -> s { lexedFiles = Map.delete doc (lexedFiles s) }
  

onHover :: LSP.HoverParams -> M (LSP.Hover |? LSP.Null)
onHover ps =
  do
    s <- getState
    -- lspLog Info (Text.pack (show (pp (cryIndex s))))
    case lookupPosition doc pos (cryIndex s) of
        Left n -> lspLog Info ("not found " <> Text.pack (show n)) >> pure (LSP.InR LSP.Null)
        Right (rng,def) ->
          pure $ 
          LSP.InL LSP.Hover {
            _range = Just rng,
            _contents = LSP.InL LSP.MarkupContent {
              _kind = LSP.MarkupKind_Markdown,
              _value = Text.pack (show (pp def))
            }
          }
  where
  doc = ps ^. LSP.textDocument . LSP.uri
  pos = ps ^. LSP.position


onGotoDefinition :: LSP.DefinitionParams -> M (LSP.Definition |? ([LSP.DefinitionLink] |? LSP.Null))
onGotoDefinition ps =
  do
    s <- getState
    case lookupPosition doc pos (cryIndex s) of
      Left n -> lspLog Info ("not found " <> Text.pack (show n)) >> pure (LSP.InR (LSP.InR LSP.Null))
      Right (_, RangeInfo { rangeDef = def }) ->
        do
          let (uri,rng) = rangeToLSP (defRange def)
          pure $ LSP.InL $ LSP.Definition $ LSP.InL LSP.Location {
            _uri = uri,
            _range = rng
          }
  where
  doc = ps ^. LSP.textDocument . LSP.uri
  pos = ps ^. LSP.position

requestSemTokUpdate :: M ()
requestSemTokUpdate =
  do
    _ <- LSP.sendRequest LSP.SMethod_WorkspaceSemanticTokensRefresh Nothing 
          (const (pure ()))
    pure ()

onSemTokFull :: LSP.SemanticTokensParams -> M (LSP.SemanticTokens |? LSP.Null)
onSemTokFull ps =
  do let doc = ps ^. LSP.textDocument . LSP.uri
     sendSemanticTokens . fst =<< semanticTokens doc Nothing

onSemTokRange :: LSP.SemanticTokensRangeParams -> M  (LSP.SemanticTokens |? LSP.Null)
onSemTokRange ps =
  do let doc = ps ^. (LSP.textDocument . LSP.uri)
     sendSemanticTokens . fst =<< semanticTokens doc (Just (ps ^. LSP.range))
    
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

onFoldingRange :: LSP.FoldingRangeParams -> M ([LSP.FoldingRange] |? LSP.Null)
onFoldingRange ps =
  do
    let doc = ps ^. LSP.textDocument . LSP.uri
    (_,rngs) <- semanticTokens doc Nothing
    pure (LSP.InL rngs)