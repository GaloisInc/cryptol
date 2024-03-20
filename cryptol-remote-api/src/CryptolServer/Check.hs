{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
module CryptolServer.Check
  ( check
  , checkDescr
  , CheckParams(..)
  , CheckResult(..)
  )
  where

import qualified Argo.Doc as Doc
import Control.Applicative
import Control.Monad.IO.Class
import Data.Aeson ((.=), (.:), (.:?), (.!=), FromJSON, ToJSON)
import qualified Data.Aeson as JSON
import Data.Scientific (floatingOrInteger)
import Data.Text (Text)
import qualified Data.Text as T
import System.Random.TF(newTFGen)

import qualified Cryptol.Eval.Concrete as CEC
import qualified Cryptol.Eval.Env as CEE
import qualified Cryptol.Eval.Type as CET
import qualified Cryptol.ModuleSystem as CM
import Cryptol.ModuleSystem.Env (DynamicEnv(..), meDynEnv)
import qualified Cryptol.Testing.Random as R
import qualified Cryptol.TypeCheck.AST as AST
import Cryptol.TypeCheck.Subst (apSubst, listParamSubst)
import Cryptol.TypeCheck.Solve (defaultReplExpr)


import CryptolServer
    ( getTCSolver,
      getModuleEnv,
      liftModuleCmd,
      validEvalContext,
      CryptolMethod(raise),
      CryptolCommand )
import CryptolServer.AesonCompat (KeyCompat)
import CryptolServer.Exceptions (evalPolyErr)
import CryptolServer.Data.Expression
    ( readBack, getExpr, Expression)
import CryptolServer.Data.Type ( JSONType(..) )
import Cryptol.Utils.PP (pretty)

checkDescr :: Doc.Block
checkDescr =
  Doc.Paragraph
    [ Doc.Text "Tests a property against random values to give quick feedback."]

-- | Check a property a la quickcheck (see `:check` at the Cryptol REPL)
check :: CheckParams -> CryptolCommand CheckResult
check (CheckParams jsonExpr cMode) =
  do e <- getExpr jsonExpr
     (_expr, ty, schema) <- liftModuleCmd (CM.checkExpr e)
     validEvalContext ty
     validEvalContext schema
     s <- getTCSolver
     perhapsDef <- liftIO (defaultReplExpr s ty schema)
     case perhapsDef of
       Nothing -> raise (evalPolyErr schema)
       Just (tys, checked) -> do
         (val,tyv) <- do -- TODO: warnDefaults here
           let su = listParamSubst tys
           let theType = apSubst su (AST.sType schema)
           tenv  <- CEE.envTypes . deEnv . meDynEnv <$> getModuleEnv
           let tval = CET.evalValType tenv theType
           val <- liftModuleCmd (CM.evalExpr checked)
           pure (val,tval)
         let (isExaustive, randomTestNum) = case cMode of
                                              ExhaustiveCheckMode -> (True, 0)
                                              RandomCheckMode n -> (False, n)
         case R.testableType tyv of
           Just (Just sz, argTys, vss, _gens) | isExaustive || sz <= randomTestNum -> do
             -- TODO? catch interruptions in testing like `qcExpr` in REPL
             (res,num) <- R.exhaustiveTests (const $ pure ()) val vss
             args <- convertTestResult argTys res
             pure $ CheckResult args num (Just sz)
           Just (sz,argTys,_,gens) | isExaustive ==False -> do
             g <- liftIO $ newTFGen
             (res,num) <- R.randomTests (const $ pure ()) randomTestNum val gens g
             args <- convertTestResult argTys res
             return $ CheckResult args num sz
           _ -> error $ "type is not testable: " ++ (pretty ty)

convertTestArg :: (CET.TValue, CEC.Value) -> CryptolCommand (JSONType, Expression)
convertTestArg (t, v) = do
   me <- readBack t v
   case me of
     Nothing -> error $ "type is not convertable: " ++ (show t)
     Just e -> return (JSONType mempty (CET.tValTy t), e)

convertTestResult ::
  [CET.TValue] {- ^ Argument types -} ->
  R.TestResult {- ^ Result to convert -} ->
  CryptolCommand ServerTestResult
convertTestResult _ R.Pass = pure Pass
convertTestResult ts (R.FailFalse vals) = do
  args <- mapM convertTestArg $ zip ts vals
  pure $ FailFalse args
convertTestResult ts (R.FailError exn vals) = do
  args <- mapM convertTestArg $ zip ts vals
  pure $ FailError (T.pack (pretty exn)) args




data ServerTestResult
  = Pass
  | FailFalse [(JSONType, Expression)]
  | FailError Text [(JSONType, Expression)]

data CheckResult =
  CheckResult
  { checkTestResult :: ServerTestResult
  , checkTestsRun :: Integer
  , checkTestsPossible :: Maybe Integer
  }

convertServerTestResult :: ServerTestResult -> [(KeyCompat, JSON.Value)]
convertServerTestResult Pass = ["result" .= ("pass" :: Text)]
convertServerTestResult (FailFalse args) =
  [ "result" .= ("fail" :: Text)
  , "arguments" .=
    [ JSON.object [ "type" .= t, "expr" .= e] | (t, e) <- args ]
  ]
convertServerTestResult (FailError err args) =
  [ "result" .= ("error" :: Text)
  , "error message" .= (pretty err)
  , "arguments" .=
    [ JSON.object [ "type" .= t, "expr" .= e] | (t, e) <- args ]
  ]


instance ToJSON CheckResult where
  toJSON res = JSON.object $ [ "tests run" .= (checkTestsRun res)
                             , "tests possible" .= (checkTestsPossible res)
                             ] ++ (convertServerTestResult (checkTestResult res))

data CheckMode
  = ExhaustiveCheckMode
  | RandomCheckMode Integer
  deriving (Eq, Show)

data CheckParams =
  CheckParams
    { checkExpression :: Expression
    , checkMode :: CheckMode
    }


instance FromJSON CheckParams where
  parseJSON =
    JSON.withObject "check parameters" $
    \o ->
      do e <- o .: "expression"
         m <- (o .:? "number of tests" >>= num) .!= (RandomCheckMode 100)
         pure CheckParams {checkExpression = e, checkMode = m}
    where
      num (Just v) =
        ((JSON.withText "all" $
          \t -> if t == "all" then pure $ Just ExhaustiveCheckMode else empty) v)
        <|>
        ((JSON.withScientific "number of tests" $
          \s ->
            case floatingOrInteger s of
              Left (_float :: Double) -> empty
              Right n -> pure $ Just $ RandomCheckMode $ (toInteger :: Int -> Integer) n) v)
      num Nothing = pure Nothing

instance Doc.DescribedMethod CheckParams CheckResult where
  parameterFieldDescription =
    [ ("expression",
      Doc.Paragraph [Doc.Text "The predicate (i.e., function) to check; "
                    , Doc.Text "must be a monomorphic function with return type Bit." ])
    , ("number of tests",
      Doc.Paragraph [Doc.Text "The number of random inputs to test the property with, or "
                    , Doc.Literal "all"
                    , Doc.Text " to exhaustively check the property (defaults to "
                    , Doc.Literal "100"
                    , Doc.Text " if not provided). If "
                    , Doc.Literal "all"
                    , Doc.Text " is specified and the property's argument types are not"
                    , Doc.Text " sufficiently small, checking may take longer than you are willing to wait!"
                      ])
    ]

  resultFieldDescription =
    [ ("tests run",
      Doc.Paragraph [Doc.Text "The number of tests that were successfully run."])
    , ("tests possible",
      Doc.Paragraph [Doc.Text "The maximum number of possible tests."])
    , ("result",
      Doc.Paragraph [ Doc.Text "The overall test result, represented as one of three string values:"
                    , Doc.Literal "pass", Doc.Text " (all tests succeeded), "
                    , Doc.Literal "fail", Doc.Text " (a test evaluated to ", Doc.Literal "False", Doc.Text "), or"
                    , Doc.Literal "error", Doc.Text " (an exception was raised during evaluation)."
                    ])
    , ("arguments",
      Doc.Paragraph [ Doc.Text "Only returned if the ", Doc.Literal "result"
                    , Doc.Text " is ", Doc.Literal "fail", Doc.Text " or ", Doc.Literal "error", Doc.Text ". "
                    , Doc.Text "An array of JSON objects indicating the arguments passed to the property "
                    , Doc.Text "which triggered the failure or error. Each object has an "
                    , Doc.Literal "expr", Doc.Text " field, which is an individual argument expression, and a "
                    , Doc.Literal "type", Doc.Text " field, which is the type of the argument expression."
                    ])
    , ("error message",
      Doc.Paragraph [ Doc.Text "Only returned if the ", Doc.Literal "result"
                    , Doc.Text " is ", Doc.Literal "error", Doc.Text ". "
                    , Doc.Text "A human-readable representation of the exception that was raised during evaluation."
                    ])
    ]
