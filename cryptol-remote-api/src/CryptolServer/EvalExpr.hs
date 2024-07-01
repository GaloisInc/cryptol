{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
module CryptolServer.EvalExpr
  ( evalExpression
  , evalExpressionDescr
  , evalExpression'
  , EvalExprParams(..)
  ) where

import qualified Argo.Doc as Doc
import Control.Exception (throwIO)
import Control.Monad.IO.Class
import Data.Aeson as JSON
import Data.Typeable (Proxy(..), typeRep)


import Cryptol.ModuleSystem (evalExpr, checkExpr)
import Cryptol.ModuleSystem.Env (deEnv,meDynEnv)
import Cryptol.TypeCheck.Solve (defaultReplExpr)
import Cryptol.TypeCheck.Subst (apSubst, listParamSubst)
import Cryptol.TypeCheck.Type (Schema(..))
import qualified Cryptol.Parser.AST as P
import Cryptol.Utils.PP (pretty)
import qualified Cryptol.Eval.Env as E
import qualified Cryptol.Eval.Type as E

import CryptolServer
import CryptolServer.Data.Expression
import CryptolServer.Data.Type
import CryptolServer.Exceptions

evalExpressionDescr :: Doc.Block
evalExpressionDescr =
  Doc.Paragraph [Doc.Text "Evaluate the Cryptol expression to a value."]

evalExpression :: EvalExprParams -> CryptolCommand JSON.Value
evalExpression (EvalExprParams jsonExpr) =
  do e <- getExpr jsonExpr
     evalExpression' e

evalExpression' :: P.Expr P.PName -> CryptolCommand JSON.Value
evalExpression' e = do
  (_expr, ty, schema) <- liftModuleCmd (checkExpr e)
  validEvalContext ty
  validEvalContext schema
  s <- getTCSolver
  perhapsDef <- liftIO (defaultReplExpr s ty schema)
  case perhapsDef of
    Nothing ->
      raise (evalPolyErr schema)
    Just (tys, checked) ->
      do -- TODO: warnDefaults here
         let su = listParamSubst tys
         let theType = apSubst su (sType schema)
         tenv  <- E.envTypes . deEnv . meDynEnv <$> getModuleEnv
         let tval = E.evalValType tenv theType
         val <- liftModuleCmd (evalExpr checked)
         mExpr<- readBack tval val
         case mExpr of
           Just expr ->
             pure $  JSON.object [ "value" .= expr
                                 , "type string" .= pretty theType
                                 , "type" .= JSONSchema (Forall [] [] theType)
                                 ]
           Nothing -> liftIO $ throwIO (invalidType theType)
newtype EvalExprParams =
  EvalExprParams Expression

instance JSON.FromJSON EvalExprParams where
  parseJSON =
    JSON.withObject "params for \"evaluate expression\"" $
    \o -> EvalExprParams <$> o .: "expression"

instance Doc.DescribedMethod EvalExprParams JSON.Value where
  parameterFieldDescription =
    [("expression",
      Doc.Paragraph [Doc.Text "The expression to evaluate."])
    ]

  resultFieldDescription =
    [ ("value",
      Doc.Paragraph [ Doc.Text "A "
                    , Doc.Link (Doc.TypeDesc (typeRep (Proxy @Expression))) "JSON Cryptol expression"
                    , Doc.Text " that denotes the value"
                    ])
    , ("type",
      Doc.Paragraph [ Doc.Text " A"
                    , Doc.Link (Doc.TypeDesc (typeRep (Proxy @JSONSchema))) "JSON Cryptol type"
                    , Doc.Text " that denotes the result type"
                    ])
    , ("type string",
      Doc.Paragraph [Doc.Text "A human-readable representation of the result type"])
    ]
