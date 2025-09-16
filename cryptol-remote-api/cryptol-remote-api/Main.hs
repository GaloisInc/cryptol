{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Main (main) where

import Data.List (intercalate)
import Data.Version (showVersion)
import Options.Applicative
    ( Parser, help, hidden, infoOption, long, short )
import System.Environment (lookupEnv)
import System.FilePath (splitSearchPath)

import Argo (AppMethod, mkApp, defaultAppOpts, StateMutability( PureState ))
import Argo.DefaultMain (customMain, parseNoOpts)
import qualified Argo.Doc as Doc


import CryptolServer
    ( command, notification, initialState, extendSearchPath, ServerState )
import CryptolServer.Call ( call, callDescr )
import CryptolServer.Check ( check, checkDescr )
import CryptolServer.CheckDocstrings ( checkDocstringsAPI, checkDocstringsDescr )
import CryptolServer.ClearState
    ( clearState, clearStateDescr, clearAllStates, clearAllStatesDescr )
import CryptolServer.Data.Expression ( Expression )
import CryptolServer.Data.Type ( JSONSchema )
import CryptolServer.EvalExpr
    ( evalExpression, evalExpressionDescr )
import CryptolServer.ExtendSearchPath
    ( extSearchPath, extSearchPathDescr )
import CryptolServer.FocusedModule (focusedModule, focusedModuleDescr)
import CryptolServer.FocusModule (focusModule, focusModuleDescr)
import CryptolServer.Interrupt
    ( interruptServer, interruptServerDescr )
import CryptolServer.LoadModule
    ( loadFile, loadFileDescr, loadModule, loadModuleDescr )
import CryptolServer.LoadProject ( loadProjectDescr, loadProject )
import CryptolServer.Names ( visibleNames, visibleNamesDescr )
import CryptolServer.Modules ( visibleModules, visibleModulesDescr )
import CryptolServer.Sat ( proveSat, proveSatDescr )
import CryptolServer.TypeCheck ( checkType, checkTypeDescr )
import CryptolServer.Version ( version, versionDescr )
import CryptolServer.FileDeps( fileDeps, fileDepsDescr )
import Cryptol.REPL.Command (CommandResult, DocstringResult)
import Cryptol.Project (ScanStatus, LoadProjectMode)
import Cryptol.Version (displayVersionStr)
import qualified Paths_cryptol_remote_api as RPC

main :: IO ()
main =
  do paths <- getSearchPaths
     initSt <- extendSearchPath paths <$> initialState
     theApp <- mkApp
                 "Cryptol RPC Server"
                 serverDocs
                 (defaultAppOpts PureState)
                 (const (pure initSt))
                 cryptolMethods
     customMain
       parseNoOpts
       parseNoOpts
       parseNoOpts
       parseNoOpts
       versionParser
       description
       (const (pure theApp))

-- | Display the version number when the @--version@/@-v@ option is supplied.
versionParser :: Parser (a -> a)
versionParser =
  infoOption versionStr $
  mconcat
    [ long "version"
    , short 'v'
    , help "Display version number"
    , hidden
    ]
  where
    versionStr :: String
    versionStr =
      intercalate "\n"
        [ "Cryptol RPC server " ++ showVersion RPC.version
        , displayVersionStr
        ]

serverDocs :: [Doc.Block]
serverDocs =
  [ Doc.Section "Summary" [ Doc.Paragraph
    [Doc.Text "An RPC server for ",
     Doc.Link (Doc.URL "https://https://cryptol.net/") "Cryptol",
     Doc.Text " that supports type checking and evaluation of Cryptol code via the methods documented below."]]
  , Doc.Section "Terms and Types"
    [Doc.datatype @Expression,
     Doc.datatype @JSONSchema,
     Doc.datatype @DocstringResult,
     Doc.datatype @CommandResult,
     Doc.datatype @ScanStatus,
     Doc.datatype @LoadProjectMode]
  ]

description :: String
description =
  "An RPC server for Cryptol that supports type checking and evaluation of Cryptol code via the methods documented below."

getSearchPaths :: IO [FilePath]
getSearchPaths =
  maybe [] splitSearchPath <$> lookupEnv "CRYPTOLPATH"

cryptolMethods :: [AppMethod ServerState]
cryptolMethods =
  [ command
    "version"
    versionDescr
    version
  , command
    "check"
    checkDescr
    check
  , notification
    "clear state"
    clearStateDescr
    clearState
  , notification
    "clear all states"
    clearAllStatesDescr
    clearAllStates
  , command
     "extend search path"
     extSearchPathDescr
     extSearchPath
  , command
     "load module"
     loadModuleDescr
     loadModule
  , command
     "load file"
     loadFileDescr
     loadFile
  , command
     "file-deps"
     fileDepsDescr
     fileDeps
  , command
     "focused module"
     focusedModuleDescr
     focusedModule
  , command
     "focus module"
     focusModuleDescr
     focusModule
  , command
     "evaluate expression"
     evalExpressionDescr
     evalExpression
  , command
     "call"
     callDescr
     call
  , command
     "visible names"
     visibleNamesDescr
     visibleNames
  , command
     "visible modules"
     visibleModulesDescr
     visibleModules
  , command
     "check type"
     checkTypeDescr
     checkType
  , command
     "prove or satisfy"
     proveSatDescr
     proveSat
  , command
     "check docstrings"
     checkDocstringsDescr
     checkDocstringsAPI
  , command
     "load project"
     loadProjectDescr
     loadProject
  , notification
     "interrupt"
     interruptServerDescr
     interruptServer
  ]
