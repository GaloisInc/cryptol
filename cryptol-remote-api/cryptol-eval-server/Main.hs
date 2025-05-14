{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Main (main) where

import Control.Lens ( view, set )
import Data.List (intercalate)
import Data.Version (showVersion)
import System.Environment (lookupEnv)
import System.Exit (exitFailure)
import System.FilePath (splitSearchPath)
import System.IO (hPutStrLn, stderr)
import Options.Applicative
    ( Parser,
      Alternative((<|>)),
      help,
      hidden,
      infoOption,
      long,
      metavar,
      short,
      strOption,
      value )

import CryptolServer.Check ( check, checkDescr )
import CryptolServer.CheckDocstrings ( checkDocstrings, checkDocstringsDescr )
import CryptolServer.ClearState
    ( clearState, clearStateDescr, clearAllStates, clearAllStatesDescr)
import Cryptol.Eval (EvalOpts(..), defaultPPOpts)
import CryptolServer.Interrupt
    ( interruptServer, interruptServerDescr )
import Cryptol.ModuleSystem (ModuleInput(..), loadModuleByPath, loadModuleByName)
import Cryptol.ModuleSystem.Monad (runModuleM, setFocusedModule)
import Cryptol.TypeCheck.AST (tcTopEntitytName, ImpName(..))
import Cryptol.Utils.Ident (ModName, modNameToText, textToModName, preludeName)
import Cryptol.Utils.Logger (quietLogger)
import Cryptol.Version (displayVersionStr)
import qualified Paths_cryptol_remote_api as RPC

import Argo (AppMethod, mkApp, defaultAppOpts, StateMutability(PureState))
import Argo.DefaultMain ( customMain, userOptions )
import qualified Argo.Doc as Doc


import CryptolServer
    ( ServerState, moduleEnv, tcSolver, initialState, extendSearchPath, command, notification )
import CryptolServer.Call ( call )
import CryptolServer.Data.Expression ( Expression )
import CryptolServer.Data.Type ( JSONSchema )
import CryptolServer.EvalExpr (evalExpressionDescr, evalExpression)
import CryptolServer.ExtendSearchPath (extSearchPath, extSearchPathDescr)
import CryptolServer.FocusedModule (focusedModuleDescr, focusedModule)
import CryptolServer.FocusModule (focusModule, focusModuleDescr)
import CryptolServer.Names ( visibleNamesDescr, visibleNames )
import CryptolServer.Modules ( visibleModulesDescr, visibleModules )
import CryptolServer.TypeCheck ( checkType )
import CryptolServer.Sat ( proveSatDescr, proveSat )
import Cryptol.REPL.Command (CommandResult, DocstringResult)

main :: IO ()
main = customMain initMod initMod initMod initMod versionParser description buildApp
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
         initSt <- extendSearchPath paths <$> initialState
         let s    = view tcSolver initSt
         let menv = view moduleEnv initSt
         let minp = ModuleInput False (pure evOpts) reader menv s
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
                  do res' <- fst <$> runModuleM minp{ minpModuleEnv = menv' } (setFocusedModule (ImpTop (tcTopEntitytName (snd m))))
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
     Doc.Text " that supports only type checking and evaluation of Cryptol code."]]
  , Doc.Section "Terms and Types"
    [Doc.datatype @Expression,
     Doc.datatype @JSONSchema,
     Doc.datatype @DocstringResult,
     Doc.datatype @CommandResult]
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

cryptolEvalMethods :: [AppMethod ServerState]
cryptolEvalMethods =
  [ command
    "check"
    checkDescr
    check
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
     "extend search path"
     extSearchPathDescr
     extSearchPath
  , command
     "call"
     (Doc.Paragraph [Doc.Text "Evaluate the result of calling a Cryptol function on one or more parameters."])
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
  , command
     "check docstrings"
     checkDocstringsDescr
     checkDocstrings
  , notification
     "interrupt"
     interruptServerDescr
     interruptServer
  ]
