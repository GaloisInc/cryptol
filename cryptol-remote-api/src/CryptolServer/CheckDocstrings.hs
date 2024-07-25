{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module CryptolServer.CheckDocstrings
  ( checkDocstrings
  , checkDocstringsDescr
  , CheckDocstringsParams(..)
  , CheckDocstringsResult(..)
  )
  where

import qualified Argo.Doc as Doc
import Control.Monad.IO.Class (MonadIO(liftIO))
import Data.Aeson ((.=),FromJSON, ToJSON)
import qualified Data.Aeson as Aeson
import qualified Data.Aeson as JSON
import Data.IORef (newIORef)
import qualified Cryptol.ModuleSystem.Env as M
import Cryptol.REPL.Command
import CryptolServer
import CryptolServer.Exceptions (noModule, moduleNotLoaded)
import qualified Cryptol.REPL.Monad as REPL
import Cryptol.Utils.Logger (quietLogger)
import Cryptol.Parser.AST (ImpName(..))
import qualified System.Random.TF as TF
import qualified Cryptol.Symbolic.SBV as SBV
import Cryptol.REPL.Monad (mkUserEnv, userOptions)

checkDocstringsDescr :: Doc.Block
checkDocstringsDescr =
  Doc.Paragraph
    [ Doc.Text "Check docstrings" ]

checkDocstrings :: CheckDocstringsParams -> CryptolCommand CheckDocstringsResult
checkDocstrings CheckDocstringsParams = do
  env <- getModuleEnv
  ln <- case M.meFocusedModule env of
          Just (ImpTop n) -> pure n
          _ -> raise noModule
  m <- case M.lookupModule ln env of
         Nothing -> raise (moduleNotLoaded ln)
         Just m -> pure m
  solver <- getTCSolver
  cfg <- getTCSolverConfig
  liftIO $
   do rng <- TF.newTFGen
      rwRef <- newIORef REPL.RW
        { REPL.eLoadedMod        = Nothing
        , REPL.eEditFile         = Nothing
        , REPL.eContinue         = True
        , REPL.eIsBatch          = False
        , REPL.eModuleEnv        = env
        , REPL.eUserEnv          = mkUserEnv userOptions
        , REPL.eLogger           = quietLogger
        , REPL.eCallStacks       = False
        , REPL.eUpdateTitle      = return ()
        , REPL.eProverConfig     = Left SBV.defaultProver
        , REPL.eTCConfig         = cfg
        , REPL.eTCSolver         = Just solver
        , REPL.eTCSolverRestarts = 0
        , REPL.eRandomGen        = rng
        }
      REPL.unREPL (CheckDocstringsResult <$> checkDocStrings m) rwRef

newtype CheckDocstringsResult = CheckDocstringsResult [[SubcommandResult]]

instance ToJSON CheckDocstringsResult where
  toJSON (CheckDocstringsResult r) = JSON.object ["results" .= r]

instance ToJSON SubcommandResult where
  toJSON r = JSON.object
    [ "input" .= srInput r
    , "log" .= srLog r
    , "result" .= srResult r
    ]

instance ToJSON CommandResult where
  toJSON r = JSON.object
    [ "type" .= crType r
    , "value" .= crValue r
    , "success" .= crSuccess r
    ]

data CheckDocstringsParams = CheckDocstringsParams

instance FromJSON CheckDocstringsParams where
  parseJSON =
    JSON.withObject "check docstrings parameters" $
    \_ -> pure CheckDocstringsParams


instance Doc.DescribedMethod CheckDocstringsParams CheckDocstringsResult where
  parameterFieldDescription =
    []

  resultFieldDescription =
    []
