{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Main (main) where

import Control.Lens ( view, set )
import System.Environment (lookupEnv)
import System.Exit (exitFailure)
import System.FilePath (splitSearchPath)
import System.IO (hPutStrLn, stderr)
import Options.Applicative
    ( Parser,
      Alternative((<|>)),
      help,
      long,
      metavar,
      strOption,
      value )

import CryptolServer.ClearState
    ( clearState, clearStateDescr, clearAllStates, clearAllStatesDescr)
import Cryptol.Eval (EvalOpts(..), defaultPPOpts)
import Cryptol.ModuleSystem (ModuleInput(..), loadModuleByPath, loadModuleByName, meSolverConfig)
import Cryptol.ModuleSystem.Monad (runModuleM, setFocusedModule)
import Cryptol.TypeCheck.AST (mName)
import qualified Cryptol.TypeCheck.Solver.SMT as SMT
import Cryptol.Utils.Ident (ModName, modNameToText, textToModName, preludeName)
import Cryptol.Utils.Logger (quietLogger)

import Argo (AppMethod, mkApp, defaultAppOpts, StateMutability(PureState))
import Argo.DefaultMain ( customMain, userOptions )
import qualified Argo.Doc as Doc


import CryptolServer
    ( ServerState, moduleEnv, initialState, setSearchPath, command, notification )
import CryptolServer.Call ( call )
import CryptolServer.EvalExpr
    ( evalExpressionDescr, evalExpression )
import CryptolServer.FocusedModule
    ( focusedModuleDescr, focusedModule )
import CryptolServer.Names ( visibleNamesDescr, visibleNames )
import CryptolServer.TypeCheck ( checkType )
import CryptolServer.Sat ( proveSatDescr, proveSat )

main :: IO ()
main = customMain initMod initMod initMod initMod description buildApp
  where
    buildApp opts =
      mkApp
        "Cryptol RPC Server"
        evalServerDocs
        (defaultAppOpts PureState)
        (startingState (userOptions opts))
        cryptolEvalMethods

    startingState (StartingFile file) reader =
      do paths <- getSearchPaths
         initSt <- setSearchPath paths <$> initialState
         let menv = view moduleEnv initSt
         let minp s = ModuleInput False (pure evOpts) reader menv s
         let die =
               \err ->
                 do hPutStrLn stderr $ "Failed to load " ++ either ("file " ++) (("module " ++) . show) file ++ ":\n" ++ show err
                    exitFailure
         menv' <- SMT.withSolver (meSolverConfig menv) $ \s ->
           do (res, _warnings) <- either loadModuleByPath loadModuleByName file (minp s)
              -- NB Warnings suppressed when running server
              case res of
                Left err -> die err
                Right (m, menv') ->
                  do res' <- fst <$> runModuleM (minp s){ minpModuleEnv = menv' } (setFocusedModule (mName (snd m)))
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
  [ Doc.Section "Summary" $ [ Doc.Paragraph
    [Doc.Text "A remote server for ",
     Doc.Link (Doc.URL "https://https://cryptol.net/") "Cryptol",
     Doc.Text " that supports only type checking and evaluation of Cryptol code."]]]

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
  [ command
     "focused module"
     focusedModuleDescr
     focusedModule
  , command
     "evaluate expression"
     evalExpressionDescr
     evalExpression
  , command
     "call"
     (Doc.Paragraph [Doc.Text "Evaluate the result of calling a Cryptol function on one or more parameters."])
     call
  , command
     "visible names"
     visibleNamesDescr
     visibleNames
  , command
     "check type"
     (Doc.Paragraph [Doc.Text "Check and return the type of the given expression."])
     checkType
  , command
     "prove or satisfy"
     proveSatDescr
     proveSat
  , notification
    "clear state"
    clearStateDescr
    clearState
  , notification
    "clear all states"
    clearAllStatesDescr
    clearAllStates
  ]
