{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Main (main) where

import Control.Lens hiding (argument)
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

import Argo (MethodType(..), AppMethod, mkApp)
import Argo.DefaultMain
import qualified Argo.Doc as Doc


import CryptolServer
import CryptolServer.Call
import CryptolServer.EvalExpr
import CryptolServer.FocusedModule
import CryptolServer.Names
import CryptolServer.TypeCheck
import CryptolServer.Sat

main :: IO ()
main = customMain initMod initMod initMod initMod description buildApp
  where
    buildApp opts =
      mkApp "Cryptol RPC Server" evalServerDocs (startingState (userOptions opts)) cryptolEvalMethods

    startingState (StartingFile file) reader =
      do paths <- getSearchPaths
         initSt <- setSearchPath paths <$> initialState
         let menv = view moduleEnv initSt
         let minp = ModuleInput False (pure evOpts) reader menv
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


evalServerDocs :: [Doc.Block]
evalServerDocs =
  [ Doc.Paragraph [Doc.Text "A remote server for Cryptol that supports only type checking and evaluation of Cryptol code."]
  ]

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

cryptolEvalMethods :: [AppMethod ServerState]
cryptolEvalMethods =
  [ method
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
