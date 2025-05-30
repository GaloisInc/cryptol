module Main where

import Control.Monad(void)
import Control.Exception(finally)
import Data.Map qualified as Map
import Language.LSP.Server qualified as LSP 
import Language.LSP.Protocol.Types qualified as LSP

import Config
import Monad
import Handlers
import Commands


main :: IO ()
main =
  do
    cfg <- newConfig
    void (LSP.runServer LSP.ServerDefinition {
        defaultConfig     = cfg,
        configSection     = "cryptol",
        parseConfig       = parseConfig,
        onConfigChange    = onConfigChange,
        doInitialize      = \env _ -> pure (Right env),
        staticHandlers    = handlers,
        interpretHandler  = \env -> LSP.Iso (LSP.runLspT env) liftIO,
        options           = lspOptions
      }) `finally` stopConfig cfg

syncOptions :: LSP.TextDocumentSyncOptions
syncOptions = LSP.TextDocumentSyncOptions
  { LSP._openClose         = Just True
  , LSP._change            = Just LSP.TextDocumentSyncKind_Incremental
  , LSP._willSave          = Just False
  , LSP._willSaveWaitUntil = Just False
  , LSP._save              = Just $ LSP.InR $ LSP.SaveOptions $ Just False
  }

lspOptions :: LSP.Options
lspOptions = LSP.defaultOptions
  { LSP.optTextDocumentSync = Just syncOptions
  , LSP.optExecuteCommandCommands = Just (Map.keys commands)
  }
