{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
module CryptolServer.Sat
  ( proveSat
  , proveSatDescr
  , ProveSatParams(..)
  )
  where

import qualified Argo.Doc as Doc
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
import Cryptol.ModuleSystem.Env (DynamicEnv(..), meDynEnv)
import Cryptol.Symbolic ( ProverCommand(..), ProverResult(..), QueryType(..)
                        , SatNum(..), CounterExampleType(..))
import Cryptol.Symbolic.SBV (proverNames, satProve, setupProver)
import Cryptol.TypeCheck.AST (Expr)
import Cryptol.TypeCheck.Solve (defaultReplExpr)

import CryptolServer
import CryptolServer.Exceptions (evalPolyErr, proverError)
import CryptolServer.Data.Expression
import CryptolServer.Data.Type

proveSatDescr :: Doc.Block
proveSatDescr =
  Doc.Paragraph
    [ Doc.Text "Find a value which satisfies the given predicate, or show that it is valid."
    , Doc.Text "(i.e., find a value which when passed as the argument produces true or show that for all possible arguments the predicate will produce true)."]

proveSat :: ProveSatParams -> CryptolCommand ProveSatResult
proveSat (ProveSatParams queryType (Prover name) jsonExpr) =
  do e <- getExpr jsonExpr
     (_expr, ty, schema) <- runModuleCmd (checkExpr e)
     -- TODO validEvalContext expr, ty, schema
     me <- getModuleEnv
     let decls = deDecls (meDynEnv me)
     s <- getTCSolver

     perhapsDef <- liftIO (defaultReplExpr s ty schema)
     case perhapsDef of
       Nothing ->
         raise (evalPolyErr schema)
       Just (_tys, checked) ->
         do timing <- liftIO $ newIORef 0
            let cmd =
                  ProverCommand
                  { pcQueryType    = queryType
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
              CounterExample cexType es -> Invalid cexType <$> satResult es
              ThmResult _ts -> pure Unsatisfiable
              AllSatResult results ->
                Satisfied <$> traverse satResult results

  where
    satResult :: [(TValue, Expr, Value)] -> CryptolCommand [(JSONType, Expression)]
    satResult es = traverse result es

    result (t, _, v) =
      do e <- observe $ readBack t v
         return (JSONType mempty (tValTy t), e)

data ProveSatResult
  = Unsatisfiable
  | Invalid CounterExampleType [(JSONType, Expression)]
  | Satisfied [[(JSONType, Expression)]]

instance ToJSON ProveSatResult where
  toJSON Unsatisfiable = JSON.object ["result" .= ("unsatisfiable" :: Text)]
  toJSON (Invalid cexType xs) =
    JSON.object [ "result" .= ("invalid" :: Text)
                , "counterexample type" .=
                  case cexType of
                    SafetyViolation -> "safety violation" :: JSON.Value
                    PredicateFalsified -> "predicate falsified" :: JSON.Value
                , "counterexample" .=
                  [ JSON.object [ "type" .= t
                                , "expr" .= e
                                ]
                  | (t, e) <- xs
                  ]
                ]
  toJSON (Satisfied xs) =
    JSON.object [ "result" .= ("satisfied" :: Text)
                , "models" .=
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
    { queryType  :: QueryType
    , prover     :: Prover
    , expression :: Expression
    }

instance FromJSON ProveSatParams where
  parseJSON =
    JSON.withObject "sat or prove parameters" $
    \o ->
      do prover     <- o .: "prover"
         expression <- o .: "expression"
         numResults <- (o .: "result count" >>= num)
         queryType  <- (o .: "query type" >>= getQueryType numResults)
         pure ProveSatParams{queryType, prover, expression}
    where
      getQueryType numResults =
        (JSON.withText "query" $
           \case
             "sat" -> pure (SatQuery numResults)
             "prove" -> pure ProveQuery
             "safe" -> pure SafetyQuery
             _ -> empty)
      num v = ((JSON.withText "all" $
               \t -> if t == "all" then pure AllSat else empty) v) <|>
              ((JSON.withScientific "count" $
                \s ->
                  case floatingOrInteger s of
                    Left (_float :: Double) -> empty
                    Right int -> pure (SomeSat int)) v)


instance Doc.DescribedMethod ProveSatParams ProveSatResult where
  parameterFieldDescription =
    [("prover",
      Doc.Paragraph ([Doc.Text "The SMT solver to use to check for satisfiability. I.e., one of the following: "]
                     ++ (concat (map (\p -> [Doc.Literal (T.pack p), Doc.Text ", "]) proverNames))
                     ++ [Doc.Text "."]))
    , ("expression",
      Doc.Paragraph [ Doc.Text "The function to check for validity, satisfiability, or safety"
                    , Doc.Text " depending on the specified value for "
                    , Doc.Literal "query type"
                    , Doc.Text ". For validity and satisfiability checks, the function must be a predicate"
                    , Doc.Text " (i.e., monomorphic function with return type Bit)."
                    ])
    , ("result count",
      Doc.Paragraph [Doc.Text "How many satisfying results to search for; either a positive integer or "
                    , Doc.Literal "all", Doc.Text". Only affects satisfiability checks."])
    , ("query type",
      Doc.Paragraph [ Doc.Text "Whether to attempt to prove the predicate is true for all possible inputs ("
                    , Doc.Literal "prove"
                    , Doc.Text "), find some inputs which make the predicate true ("
                    , Doc.Literal "sat"
                    , Doc.Text "), or prove a function is safe ("
                    , Doc.Literal "safe"
                    , Doc.Text ")."
                    ]
      )
    ]

  resultFieldDescription =
    [ ("result",
      Doc.Paragraph [ Doc.Text "A string (one of "
                    , Doc.Literal "unsatisfiable", Doc.Text ", "
                    , Doc.Literal "invalid", Doc.Text ", or "
                    , Doc.Literal "satisfied"
                    , Doc.Text ") indicating the result of checking for validity, satisfiability, or safety."
                    ])
    , ("counterexample type",
      Doc.Paragraph $ onlyIfResultIs "invalid" ++
                    [ Doc.Text "This describes the variety of counterexample that was produced. This can be either "
                    , Doc.Literal "safety violation", Doc.Text " or ", Doc.Literal "predicate falsified", Doc.Text "."
                    ])
    , ("counterexample",
      Doc.Paragraph $ onlyIfResultIs "invalid" ++
                    [ Doc.Text "A list of objects where each object has an "
                    , Doc.Literal "expr", Doc.Text "field, indicating a counterexample expression, and a "
                    , Doc.Literal "type", Doc.Text "field, indicating the type of the expression."
                    ])
    , ("models",
      Doc.Paragraph $ onlyIfResultIs "satisfied" ++
                    [ Doc.Text "A list of list of objects where each object has an "
                    , Doc.Literal "expr", Doc.Text "field, indicating a expression in a model, and a "
                    , Doc.Literal "type", Doc.Text "field, indicating the type of the expression."
                    ])
    ]
    where
      onlyIfResultIs val = [ Doc.Text "Only used if the " , Doc.Literal "result"
                           , Doc.Text " is ", Doc.Literal val, Doc.Text "." ]
