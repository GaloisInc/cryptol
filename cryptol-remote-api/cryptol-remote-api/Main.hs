{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Main (main) where

import System.Environment (lookupEnv)
import System.FilePath (splitSearchPath)

import Argo (MethodType(..), AppMethod, mkApp)
import Argo.DefaultMain
import qualified Argo.Doc as Doc


import CryptolServer
import CryptolServer.Call
import CryptolServer.ChangeDir
import CryptolServer.EvalExpr
import CryptolServer.FocusedModule
import CryptolServer.LoadModule
import CryptolServer.Names
import CryptolServer.Sat
import CryptolServer.TypeCheck

main :: IO ()
main =
  do paths <- getSearchPaths
     initSt <- setSearchPath paths <$> initialState
     theApp <- mkApp "Cryptol RPC Server" serverDocs (const (pure initSt)) cryptolMethods
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
  [ method
     "change directory"
     Command
     cdDescr
     cd
  , method
     "load module"
     Command
     loadModuleDescr
     loadModule
  , method
     "load file"
     Command
     loadFileDescr
     loadFile -- The "current" module.  Used to decide how to print names, for example.
  , method
     "focused module"
     Query
     focusedModuleDescr
     focusedModule
  , method
     "evaluate expression"
     Query
     evalExpressionDescr
     evalExpression
  , method
     "call"
     Query
     callDescr
     call
  , method
     "visible names"
     Query
     visibleNamesDescr
     visibleNames
  , method
     "check type"
     Query
     checkTypeDescr
     checkType
  , method
     "satisfy"
     Query
     satDescr
     sat
  ]
