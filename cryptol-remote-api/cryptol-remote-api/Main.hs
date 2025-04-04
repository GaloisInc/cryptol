{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Main (main) where

import System.Environment (lookupEnv)
import System.FilePath (splitSearchPath)

import Argo (AppMethod, mkApp, defaultAppOpts, StateMutability( PureState ))
import Argo.DefaultMain (defaultMain)
import qualified Argo.Doc as Doc


import CryptolServer
    ( command, notification, initialState, extendSearchPath, ServerState )
import CryptolServer.Call ( call, callDescr )
import CryptolServer.Check ( check, checkDescr )
import CryptolServer.CheckDocstrings ( checkDocstrings, checkDocstringsDescr )
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
     defaultMain description theApp

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
     checkDocstrings
  , command
     "load project"
     loadProjectDescr
     loadProject
  , notification
     "interrupt"
     interruptServerDescr
     interruptServer
  ]
