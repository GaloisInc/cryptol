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
     (Doc.Paragraph [Doc.Text "Changes the server's working directory to the given path."])
     cd
  , method
     "load module"
     Command
     (Doc.Paragraph [Doc.Text "Load the specified module (by name)."])
     loadModule
  , method
     "load file"
     Command
     (Doc.Paragraph [Doc.Text "Load the specified module (by file path)."])
     loadFile -- The "current" module.  Used to decide how to print names, for example.
  , method
     "focused module"
     Query
     (Doc.Paragraph [Doc.Text "The 'current' module. Used to decide how to print names, for example."])
     focusedModule
  , method
     "evaluate expression"
     Query
     (Doc.Paragraph [Doc.Text "Evaluate the Cryptol expression to a value."])
     evalExpression
  , method
     "call"
     Query
     (Doc.Paragraph [Doc.Text "Evaluate the result of calling a Cryptol function on one or more parameters."])
     call
  , method
     "visible names"
     Query
     (Doc.Paragraph [Doc.Text "List the currently visible (i.e., in scope) names."])
     visibleNames
  , method
     "check type"
     Query
     (Doc.Paragraph [Doc.Text "Check and return the type of the given expression."])
     checkType
  , method
     "satisfy"
     Query
     (Doc.Paragraph [ Doc.Text "Find a value which satisfies the given predicate "
                    , Doc.Text "(i.e., a value which when passed to the argument produces true)."])
     sat
  ]
