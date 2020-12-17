{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main (main) where

import qualified Data.Aeson as JSON
import Data.Text (Text)
import System.Environment (lookupEnv)
import System.FilePath (splitSearchPath)

import Argo (MethodType(..), Method, mkApp)
import Argo.DefaultMain


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
     theApp <- mkApp (const (pure initSt)) cryptolMethods
     defaultMain description theApp

description :: String
description =
  "An RPC server for Cryptol that supports type checking and evaluation of Cryptol code."

getSearchPaths :: IO [FilePath]
getSearchPaths =
  maybe [] splitSearchPath <$> lookupEnv "CRYPTOLPATH"

cryptolMethods :: [(Text, MethodType, JSON.Value -> Method ServerState JSON.Value)]
cryptolMethods =
  [ ("change directory",    Command, method cd)
  , ("load module",         Command, method loadModule)
  , ("load file",           Command, method loadFile)
  , ("focused module",      Query,   method focusedModule)
  , ("evaluate expression", Query,   method evalExpression)
  , ("call",                Query,   method call)
  , ("visible names",       Query,   method visibleNames)
  , ("check type",          Query,   method checkType)
  , ("satisfy",             Query,   method sat)
  ]
