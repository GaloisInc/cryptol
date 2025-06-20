{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE InstanceSigs #-}
module CryptolServer.CheckDocstrings
  ( checkDocstrings
  , checkDocstringsDescr
  , CheckDocstringsParams(..)
  , CheckDocstringsResult(..)
  )
  where

import qualified Argo.Doc as Doc
import Control.Monad.IO.Class (MonadIO(liftIO))
import Data.Aeson ((.=),(.:),FromJSON, ToJSON)
import qualified Data.Aeson as Aeson
import qualified Data.Aeson as JSON
import Data.IORef (newIORef)
import qualified Cryptol.ModuleSystem.Env as M
import Cryptol.REPL.Command
import CryptolServer
import CryptolServer.Exceptions (noModule, moduleNotLoaded)
import CryptolServer.Utils
import qualified Cryptol.REPL.Monad as REPL
import Cryptol.Utils.Logger (quietLogger)
import Cryptol.Parser.AST (ImpName(..))
import qualified Cryptol.TypeCheck.AST as T
import qualified System.Random.TF as TF
import qualified Cryptol.Symbolic.SBV as SBV
import Cryptol.REPL.Monad (mkUserEnv, userOptions)
import Cryptol.Project.Cache(CacheId)
import Cryptol.Utils.PP (pp)
import Data.Proxy (Proxy(Proxy))
import Data.Typeable (typeRep)

checkDocstringsDescr :: Doc.Block
checkDocstringsDescr =
  Doc.Paragraph
    [ Doc.Text "Check docstrings" ]

checkDocstrings :: CheckDocstringsParams -> CryptolCommand CheckDocstringsResult
checkDocstrings (CheckDocstringsParams cache) = do
  env <- getModuleEnv
  ln <- case M.meFocusedModule env of
          Just (ImpTop n) -> pure n
          _ -> raise noModule
  case M.lookupModule ln env of
    Nothing ->
      case M.lookupSignature ln env of
        Nothing -> raise (moduleNotLoaded ln)
        Just{} -> pure (CheckDocstringsResult [] cache) -- can't be checked directly
    Just m ->
      if T.isParametrizedModule (M.lmdModule (M.lmData m)) then
        pure (CheckDocstringsResult [] cache) -- can't be checked directly
      else do
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
            let work =
                  do (rs,cid) <- checkDocStrings m (Just cache)
                     pure CheckDocstringsResult {
                       results = rs,
                       cacheId = cid
                     }
            REPL.unREPL work rwRef

data CheckDocstringsResult = CheckDocstringsResult {
  results :: [DocstringResult],
  cacheId :: CacheId
}

instance ToJSON CheckDocstringsResult where
  toJSON r = JSON.object
    [ "results" .= results r
    , "cache_id" .= BS (cacheId r)
    ]

instance ToJSON DocstringResult where
  toJSON dr = JSON.object ["name" .= show (pp (drName dr)), "fences" .= drFences dr]

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

newtype CheckDocstringsParams = CheckDocstringsParams CacheId

instance FromJSON CheckDocstringsParams where
  parseJSON =
    JSON.withObject "check docstrings parameters" $
    \o -> do BS bs <- o .: "cache_id"
             pure (CheckDocstringsParams bs)


instance Doc.DescribedMethod CheckDocstringsParams CheckDocstringsResult where
  parameterFieldDescription =
    [ ("cache_id", Doc.Paragraph [ Doc.Text "A ", Doc.Literal "string", Doc.Text " identifying the cache state before validation." ]) ]

  resultFieldDescription =
    [("results",
        Doc.Paragraph
            [ Doc.Text "A list of "
            , Doc.Link (Doc.TypeDesc (typeRep (Proxy :: Proxy DocstringResult))) "docstring results"
            , Doc.Text " correspoding to each definition in the current module."
            ]),
      ("cache_id", Doc.Paragraph [ Doc.Text "A ", Doc.Literal "string", Doc.Text " identifying the cache state after validation." ]) 
    ]
    
instance Doc.Described DocstringResult where
  typeName = "DocstringResult"
  description =
    [ Doc.Paragraph [Doc.Text "The result of evaluating the code fences in a docstring"]
    , Doc.DescriptionList
        [ ( pure (Doc.Literal "name")
          , Doc.Paragraph[Doc.Text "The definition assocated with the docstring"]
          )
        , ( pure (Doc.Literal "fences")
          , Doc.Paragraph[Doc.Text "An array code fences each containing an array of individual "
          , Doc.Link (Doc.TypeDesc (typeRep (Proxy :: Proxy CommandResult))) "command results"]
          )
        ]
    ]

instance Doc.Described CommandResult where
  typeName = "CommandResult"
  description =
    [ Doc.Paragraph [Doc.Text "The result of executing a single REPL command."]
    , Doc.DescriptionList
        [ ( pure (Doc.Literal "success")
          , Doc.Paragraph [Doc.Text "Boolean indicating successful execution of the command"]
          )
        , ( pure (Doc.Literal "type")
          , Doc.Paragraph[Doc.Text "The string representation of the type returned or null"]
          )
        , ( pure (Doc.Literal "value")
          , Doc.Paragraph[Doc.Text "The string representation of the value returned or null"]
          )
        ]
    ]
