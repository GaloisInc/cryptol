{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
module CryptolServer.Sat (sat, ProveSatParams(..)) where

import Control.Applicative
import Control.Monad.IO.Class
import Data.Aeson ((.=), (.:), FromJSON, ToJSON)
import qualified Data.Aeson as JSON
import Data.IORef
import Data.Scientific (floatingOrInteger)
import Data.Text (Text)
import qualified Data.Text as T

import Cryptol.Eval.Concrete (Value)
import Cryptol.Eval.Type (TValue, tValTy)
import Cryptol.ModuleSystem (checkExpr)
import Cryptol.ModuleSystem.Env (DynamicEnv(..), meDynEnv, meSolverConfig)
import Cryptol.Symbolic (ProverCommand(..), ProverResult(..), QueryType(..), SatNum(..))
import Cryptol.Symbolic.SBV (proverNames, satProve, setupProver)
import Cryptol.TypeCheck.AST (Expr)
import Cryptol.TypeCheck.Solve (defaultReplExpr)
import qualified Cryptol.TypeCheck.Solver.SMT as SMT

import CryptolServer
import CryptolServer.Exceptions (evalPolyErr, proverError)
import CryptolServer.Data.Expression
import CryptolServer.Data.Type

sat :: ProveSatParams -> CryptolMethod SatResult
sat (ProveSatParams (Prover name) jsonExpr num) =
  do e <- getExpr jsonExpr
     (_expr, ty, schema) <- runModuleCmd (checkExpr e)
     -- TODO validEvalContext expr, ty, schema
     me <- getModuleEnv
     let decls = deDecls (meDynEnv me)
     let cfg = meSolverConfig me
     perhapsDef <- liftIO $ SMT.withSolver cfg (\s -> defaultReplExpr s ty schema)
     case perhapsDef of
       Nothing ->
         raise (evalPolyErr schema)
       Just (_tys, checked) ->
         do timing <- liftIO $ newIORef 0
            let cmd =
                  ProverCommand
                  { pcQueryType    = SatQuery num
                  , pcProverName   = name
                  , pcVerbose      = True -- verbose
                  , pcProverStats  = timing
                  , pcExtraDecls   = decls
                  , pcSmtFile      = Nothing -- mfile
                  , pcExpr         = checked
                  , pcSchema       = schema
                  , pcValidate     = False
                  , pcIgnoreSafety = False
                  }
            sbvCfg <- liftIO (setupProver name) >>= \case
                        Left msg -> error msg
                        Right (_ws, sbvCfg) -> return sbvCfg
            (_firstProver, res) <- runModuleCmd $ satProve sbvCfg cmd
            _stats <- liftIO (readIORef timing)
            case res of
              ProverError msg -> raise (proverError msg)
              EmptyResult -> error "got empty result for online prover!"
              CounterExample{} -> error "Unexpected counter-example for SAT query"
              ThmResult _ts -> pure Unsatisfiable
              AllSatResult results ->
                Satisfied <$> traverse satResult results

  where
    satResult :: [(TValue, Expr, Value)] -> CryptolMethod [(JSONType, Expression)]
    satResult es = traverse result es

    result (t, _, v) =
      do e <- observe $ readBack t v
         return (JSONType mempty (tValTy t), e)

data SatResult = Unsatisfiable | Satisfied [[(JSONType, Expression)]]

instance ToJSON SatResult where
  toJSON Unsatisfiable = JSON.object ["result" .= ("unsatisfiable" :: Text)]
  toJSON (Satisfied xs) =
    JSON.object [ "result" .= ("satisfied" :: Text)
                , "model" .=
                  [ [ JSON.object [ "type" .= t
                                  , "expr" .= e
                                  ]
                    | (t, e) <- res
                    ]
                  | res <- xs
                  ]
                ]


newtype Prover = Prover String

instance FromJSON Prover where
  parseJSON =
    JSON.withText "prover name" $
    \txt ->
      let str = T.unpack txt
      in if str `elem` proverNames
           then return (Prover str)
           else empty


data ProveSatParams =
  ProveSatParams
    { prover     :: Prover
    , expression :: Expression
    , numResults :: SatNum
    }

instance FromJSON ProveSatParams where
  parseJSON =
    JSON.withObject "sat or prove parameters" $
    \o ->
      do prover     <- o .: "prover"
         expression <- o .: "expression"
         numResults <- (o .: "result count" >>= num)
         pure ProveSatParams{prover, expression, numResults}
    where
      num v = ((JSON.withText "all" $
               \t -> if t == "all" then pure AllSat else empty) v) <|>
              ((JSON.withScientific "count" $
                \s ->
                  case floatingOrInteger s of
                    Left (_float :: Double) -> empty
                    Right int -> pure (SomeSat int)) v)
