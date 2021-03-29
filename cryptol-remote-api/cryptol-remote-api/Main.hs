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
import CryptolServer.ClearState
    ( clearState, clearStateDescr, clearAllStates, clearAllStatesDescr )
import CryptolServer.EvalExpr
    ( evalExpression, evalExpressionDescr )
import CryptolServer.ExtendSearchPath
    ( extSearchPath, extSearchPathDescr )
import CryptolServer.FocusedModule
    ( focusedModule, focusedModuleDescr )
import CryptolServer.LoadModule
    ( loadFile, loadFileDescr, loadModule, loadModuleDescr )
import CryptolServer.Names ( visibleNames, visibleNamesDescr )
import CryptolServer.Sat ( proveSat, proveSatDescr )
import CryptolServer.TypeCheck ( checkType, checkTypeDescr )

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
  [ Doc.Section "Summary" $ [ Doc.Paragraph
    [Doc.Text "An RCP server for ",
     Doc.Link (Doc.URL "https://https://cryptol.net/") "Cryptol",
     Doc.Text " that supports type checking and evaluation of Cryptol code via the methods documented below."]]]

description :: String
description =
  "An RPC server for Cryptol that supports type checking and evaluation of Cryptol code via the methods documented below."

getSearchPaths :: IO [FilePath]
getSearchPaths =
  maybe [] splitSearchPath <$> lookupEnv "CRYPTOLPATH"

cryptolMethods :: [AppMethod ServerState]
cryptolMethods =
  [ notification
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
     "focused module"
     focusedModuleDescr
     focusedModule
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
     "check type"
     checkTypeDescr
     checkType
  , command
     "prove or satisfy"
     proveSatDescr
     proveSat
  ]
