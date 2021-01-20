{-# LANGUAGE OverloadedStrings #-}
module CryptolServer.EvalExpr
  ( evalExpression
  , evalExpressionDescr
  , evalExpression'
  , EvalExprParams(..)
  ) where

import qualified Argo.Doc as Doc
import Control.Monad.IO.Class
import Data.Aeson as JSON


import Cryptol.ModuleSystem (checkExpr, evalExpr)
import Cryptol.ModuleSystem.Env (meSolverConfig,deEnv,meDynEnv)
import Cryptol.TypeCheck.Solve (defaultReplExpr)
import Cryptol.TypeCheck.Subst (apSubst, listParamSubst)
import Cryptol.TypeCheck.Type (Schema(..))
import qualified Cryptol.Parser.AST as P
import Cryptol.Parser.Name (PName)
import qualified Cryptol.TypeCheck.Solver.SMT as SMT
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

evalExpression :: EvalExprParams -> CryptolMethod JSON.Value
evalExpression (EvalExprParams jsonExpr) =
  do e <- getExpr jsonExpr
     evalExpression' e

evalExpression' :: P.Expr PName -> CryptolMethod JSON.Value
evalExpression' e =
  do (_expr, ty, schema) <- runModuleCmd (checkExpr e)
     -- TODO: see Cryptol REPL for how to check whether we
     -- can actually evaluate things, which we can't do in
     -- a parameterized module
     me <- getModuleEnv
     let cfg = meSolverConfig me
     perhapsDef <- liftIO $ SMT.withSolver cfg (\s -> defaultReplExpr s ty schema)
     case perhapsDef of
       Nothing ->
         raise (evalPolyErr schema)
       Just (tys, checked) ->
         do -- TODO: warnDefaults here
            let su = listParamSubst tys
            let theType = apSubst su (sType schema)
            tenv  <- E.envTypes . deEnv . meDynEnv <$> getModuleEnv
            let tval = E.evalValType tenv theType
            res <- runModuleCmd (evalExpr checked)
            val <- observe $ readBack tval res
            return (JSON.object [ "value" .= val
                                , "type string" .= pretty theType
                                , "type" .= JSONSchema (Forall [] [] theType)
                                ])

newtype EvalExprParams =
  EvalExprParams Expression

instance JSON.FromJSON EvalExprParams where
  parseJSON =
    JSON.withObject "params for \"evaluate expression\"" $
    \o -> EvalExprParams <$> o .: "expression"

instance Doc.DescribedParams EvalExprParams where
  parameterFieldDescription =
    [("expression",
      Doc.Paragraph [Doc.Text "The expression to evaluate."])
    ]
