{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main (main) where

import qualified Data.Aeson as JSON
import Control.Lens hiding (argument)
import Data.Text (Text)
import System.Environment (lookupEnv)
import System.Exit (exitFailure)
import System.FilePath (splitSearchPath)
import System.IO (hPutStrLn, stderr)
import Options.Applicative

import Cryptol.Eval (EvalOpts(..), defaultPPOpts)
import Cryptol.ModuleSystem (ModuleInput(..), loadModuleByPath, loadModuleByName)
import Cryptol.ModuleSystem.Monad (runModuleM, setFocusedModule)
import Cryptol.TypeCheck.AST (mName)
import Cryptol.Utils.Ident (ModName, modNameToText, textToModName, preludeName)
import Cryptol.Utils.Logger (quietLogger)

import Argo
import Argo.DefaultMain


import CryptolServer
import CryptolServer.EvalExpr
import CryptolServer.FocusedModule
import CryptolServer.Names
import CryptolServer.TypeCheck

main :: IO ()
main = customMain initMod initMod initMod description buildApp
  where
    buildApp opts =
      mkApp (startingState (userOptions opts)) cryptolEvalMethods

    startingState (StartingFile file) reader =
      do paths <- getSearchPaths
         initSt <- setSearchPath paths <$> initialState
         let menv = view moduleEnv initSt
         let minp = ModuleInput False evOpts reader menv
         let die =
               \err ->
                 do hPutStrLn stderr $ "Failed to load " ++ either ("file " ++) (("module " ++) . show) file ++ ":\n" ++ show err
                    exitFailure
         menv' <-
           do (res, _warnings) <- either loadModuleByPath loadModuleByName file minp
              -- NB Warnings suppressed when running server
              case res of
                Left err -> die err
                Right (m, menv') ->
                  do res' <- fst <$> runModuleM minp { minpModuleEnv = menv' } (setFocusedModule (mName (snd m)))
                     case res' of
                       Left err -> die err
                       Right (_, menv'') -> pure menv''
         return $ set moduleEnv menv' initSt

    evOpts =
      EvalOpts { evalLogger = quietLogger
               , evalPPOpts = defaultPPOpts
               }

description :: String
description =
  "An RPC server for Cryptol that supports only type checking and evaluation of Cryptol code."

getSearchPaths :: IO [FilePath]
getSearchPaths =
  maybe [] splitSearchPath <$> lookupEnv "CRYPTOLPATH"

newtype StartingFile =
  StartingFile (Either FilePath ModName)

initMod :: Parser StartingFile
initMod = StartingFile <$> (Left <$> filename <|> Right . textToModName <$> modulename)
  where
    filename =
      strOption $
      long "file" <>
      metavar "FILENAME" <>
      help "Cryptol file to load on startup"
    modulename =
      strOption $
      long "module" <>
      metavar "MODULE" <>
      help "Cryptol module to load on startup" <>
      value (modNameToText preludeName)

cryptolEvalMethods :: [(Text, MethodType, JSON.Value -> Method ServerState JSON.Value)]
cryptolEvalMethods =
  [ ("focused module",      Query,   method focusedModule)
  , ("evaluate expression", Query,   method evalExpression)
  , ("visible names",       Query,   method visibleNames)
  , ("check type",          Query,   method checkType)
  ]
