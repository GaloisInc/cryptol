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
import Data.Aeson ((.=), (.:), (.:?), (.!=), FromJSON, ToJSON)
import qualified Data.Aeson as Aeson
import qualified Data.Aeson.Types as Aeson
import qualified Data.Aeson as JSON
import Data.IORef
import qualified Data.List as List
import Data.Scientific (floatingOrInteger)
import Data.Text (Text)
import qualified Data.Text as T

import Cryptol.Eval.Concrete (Value)
import Cryptol.Eval.Type (TValue, tValTy)
import Cryptol.ModuleSystem (checkExpr)
import Cryptol.ModuleSystem.Env (DynamicEnv(..), meDynEnv)
import Cryptol.REPL.Command (withRWTempFile)
import Cryptol.Symbolic ( ProverCommand(..), ProverResult(..), QueryType(..)
                        , SatNum(..), CounterExampleType(..))
import qualified Cryptol.Symbolic.SBV as SBV
import qualified Cryptol.Symbolic.What4 as W4
import Cryptol.TypeCheck.AST (Expr)
import Cryptol.TypeCheck.Solve (defaultReplExpr)

import CryptolServer
import CryptolServer.Exceptions (evalPolyErr, proverError)
import CryptolServer.Data.Expression
import CryptolServer.Data.Type
import Data.Text.IO as TIO
import System.IO (hSeek,SeekMode(..))

proveSatDescr :: Doc.Block
proveSatDescr =
  Doc.Paragraph
    [ Doc.Text "Find a value which satisfies the given predicate, or show that it is valid."
    , Doc.Text "(i.e., find a value which when passed as the argument produces true or show that for all possible arguments the predicate will produce true)."]



proveSat :: ProveSatParams -> CryptolCommand ProveSatResult
proveSat (ProveSatParams queryType (ProverName proverName) jsonExpr hConsing) = do
  e <- getExpr jsonExpr
  (_expr, ty, schema) <- liftModuleCmd (checkExpr e)
  validEvalContext ty
  validEvalContext schema
  decls <- deDecls . meDynEnv <$> getModuleEnv
  s <- getTCSolver
  perhapsDef <- liftIO (defaultReplExpr s ty schema)
  case perhapsDef of
    Nothing -> raise (evalPolyErr schema)
    Just (_tys, checked) -> do
      timing <- liftIO $ newIORef 0
      let cmd =
            ProverCommand
            { pcQueryType    = queryType
            , pcProverName   = proverName
            , pcVerbose      = False
            , pcProverStats  = timing
            , pcExtraDecls   = decls
            , pcSmtFile      = Nothing
            , pcExpr         = checked
            , pcSchema       = schema
            , pcValidate     = False
            , pcIgnoreSafety = False
            }
      res <- if proverName `elem` ["offline","sbv-offline","w4-offline"]
             then offlineProveSat proverName cmd hConsing
             else onlineProveSat  proverName cmd hConsing
      _stats <- liftIO (readIORef timing)
      pure res


getProverConfig ::
  -- | Prover name.
  String ->
  CryptolCommand (Either SBV.SBVProverConfig W4.W4ProverConfig)
getProverConfig proverName =
  if proverName `elem` W4.proverNames then do
    liftIO (W4.setupProver proverName) >>= \case
      Left msg -> raise $ proverError $ "error setting up " ++ proverName ++ ": " ++ msg
      Right (_ws, w4Cfg) -> pure $ Right w4Cfg
  else if proverName `elem` SBV.proverNames  then do
    liftIO (SBV.setupProver proverName) >>= \case
      Left msg -> raise $ proverError $ "error setting up " ++ proverName ++ ": " ++ msg
      Right (_ws, sbvCfg) -> pure $ Left sbvCfg
  else do
    raise $ proverError
          $ proverName ++ "is not a recognized solver;"
            ++ " please choose one of the following instead: "
            ++ (show $ W4.proverNames ++ SBV.proverNames)


offlineProveSat ::
  -- | Prover name.
  String ->
  ProverCommand ->
  -- | Whether hash consing is enabled.
  Bool ->
  CryptolCommand ProveSatResult
offlineProveSat proverName cmd hConsing = do
  getProverConfig proverName >>= \case
    Left sbvCfg -> do
      result <- liftModuleCmd $ SBV.satProveOffline sbvCfg cmd
      case result of
        Left msg -> do
          raise $ proverError $ "error setting up " ++ proverName ++ ": " ++ msg
        Right smtlib -> pure $ OfflineSMTQuery $ T.pack smtlib
    Right _w4Cfg -> do
      smtlibRef <- liftIO $ newIORef ("" :: Text)
      result <- liftModuleCmd $
        W4.satProveOffline hConsing False cmd $ \f -> do
          withRWTempFile "smtOutput.tmp" $ \h -> do
            f h
            hSeek h AbsoluteSeek 0
            contents <- TIO.hGetContents h
            writeIORef smtlibRef contents
      case result of
        Just errMsg -> raise $ proverError $ "encountered an error using " ++ proverName ++ " to generate a query: " ++ errMsg
        Nothing -> do
          smtlib <- liftIO $ readIORef smtlibRef
          pure $ OfflineSMTQuery smtlib


onlineProveSat ::
  -- | Prover name.
  String ->
  ProverCommand ->
  -- | Type of expression sat is being called for.
  Bool ->
  CryptolCommand ProveSatResult
onlineProveSat proverName cmd hConsing = do
  res <-
    getProverConfig proverName >>= \case
      Left sbvCfg -> do
        (_firstProver, res) <- liftModuleCmd $ SBV.satProve sbvCfg cmd
        _stats <- liftIO (readIORef (pcProverStats cmd))
        pure res
      Right w4Cfg -> do
        (_firstProver, res) <-
          liftModuleCmd $ W4.satProve w4Cfg hConsing False {- warn uninterp fns -} cmd
        _stats <- liftIO (readIORef (pcProverStats cmd))
        pure res
  case res of
    ProverError msg -> raise (proverError msg)
    EmptyResult -> raise $ proverError "got empty result for online prover!"
    CounterExample cexType es -> Invalid cexType <$> convertSatResult es
    ThmResult _ts -> pure Unsatisfiable
    AllSatResult results ->
      Satisfied <$> traverse convertSatResult results

  where
    convertSatResult :: [(TValue, Expr, Value)] -> CryptolCommand [(JSONType, Expression)]
    convertSatResult es = traverse result es
      where
        result :: forall b. (TValue, b, Value) -> CryptolCommand (JSONType, Expression)
        result (t, _, v) = do
          me <- readBack t v
          case me of
            Nothing -> error $ "type is not convertable: " ++ (show t)
            Just e -> pure (JSONType mempty (tValTy t), e)

data ProveSatResult
  = Unsatisfiable
  | Invalid CounterExampleType [(JSONType, Expression)]
  | Satisfied [[(JSONType, Expression)]]
  | OfflineSMTQuery Text

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
  toJSON (OfflineSMTQuery smtlib) =
    JSON.object [ "result" .= ("offline" :: Text)
                , "query" .= smtlib
                ]

newtype ProverName = ProverName String

instance FromJSON ProverName where
  parseJSON (Aeson.String name) = pure $ ProverName $ T.unpack name
  parseJSON invalid    =
        Aeson.prependFailure "parsing prover name failed, "
            (Aeson.typeMismatch "String" invalid)

data ProveSatParams =
  ProveSatParams
    { queryType  :: QueryType
    , prover     :: ProverName
    , expression :: Expression
    , w4HashConsing :: Bool
    }

instance FromJSON ProveSatParams where
  parseJSON =
    JSON.withObject "sat or prove parameters" $
    \o ->
      do prover     <- o .: "prover"
         expression <- o .: "expression"
         numResults <- (o .: "result count" >>= num)
         queryType  <- (o .: "query type" >>= getQueryType numResults)
         hConsing   <- (o .:? "hash consing" >>= onOrOff) .!= True
         pure $ ProveSatParams
                  { queryType = queryType,
                    prover = prover,
                    expression = expression,
                    w4HashConsing = hConsing}
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
      onOrOff Nothing = pure Nothing
      onOrOff (Just val) =
        (JSON.withText "hash consing"
           (\case
             "on"    -> pure $ Just True
             "true"  -> pure $ Just True
             "yes"   -> pure $ Just True
             "off"   -> pure $ Just False
             "false" -> pure $ Just False
             "no"    -> pure $ Just False
             _ -> empty)
           val)


instance Doc.DescribedMethod ProveSatParams ProveSatResult where
  parameterFieldDescription =
    [("prover",
      Doc.Paragraph ([Doc.Text "The SMT solver to use to check for satisfiability. I.e., one of the following: "]
                     ++ (List.intersperse (Doc.Text ", ") $ map (Doc.Literal . T.pack) $ W4.proverNames ++ SBV.proverNames)
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
    , ("hash consing",
      Doc.Paragraph [Doc.Text "Whether or not to use hash consing of terms (if available)."
                    , Doc.Literal "true", Doc.Text" to enable or ", Doc.Literal "false", Doc.Text " to disable."])
    ]

  resultFieldDescription =
    [ ("result",
      Doc.Paragraph [ Doc.Text "Either a string indicating the result of checking for validity, satisfiability, or safety"
                    , Doc.Text "---i.e., one of "
                    , Doc.Literal "unsatisfiable", Doc.Text ", "
                    , Doc.Literal "invalid", Doc.Text ", or "
                    , Doc.Literal "satisfied",  Doc.Text "---"
                    , Doc.Text "or the string literal "
                    , Doc.Literal "offline"
                    , Doc.Text " indicating an offline solver option was selected and the contents of the SMT query will be"
                    , Doc.Text " returned instead of a SAT result."
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
    , ("query",
      Doc.Paragraph $ onlyIfResultIs "offline" ++
                    [ Doc.Text "The raw textual contents of the requested SMT query which can inspected or manually"
                    , Doc.Text " given to an SMT solver."
                    ])
    ]
    where
      onlyIfResultIs val = [ Doc.Text "Only used if the " , Doc.Literal "result"
                           , Doc.Text " is ", Doc.Literal val, Doc.Text ". " ]
