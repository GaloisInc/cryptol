{-# LANGUAGE OverloadedStrings #-}
module CryptolServer.EvalExpr (evalExpression, EvalExprParams(..)) where

import Control.Lens hiding ((.=))
import Control.Monad.IO.Class
import Data.Aeson as JSON


import Cryptol.ModuleSystem (checkExpr, evalExpr, getPrimMap)
import Cryptol.ModuleSystem.Env (meSolverConfig)
import Cryptol.TypeCheck.AST (sType)
import Cryptol.TypeCheck.Solve (defaultReplExpr)
import Cryptol.TypeCheck.Subst (apSubst, listParamSubst)
import Cryptol.TypeCheck.Type (Schema(..))
import qualified Cryptol.TypeCheck.Solver.SMT as SMT
import Cryptol.Utils.PP (pretty)

import Argo
import CryptolServer
import CryptolServer.Data.Expression
import CryptolServer.Data.Type
import CryptolServer.Exceptions

evalExpression :: EvalExprParams -> Method ServerState JSON.Value
evalExpression (EvalExprParams jsonExpr) =
  do e <- getExpr jsonExpr
     (_expr, ty, schema) <- runModuleCmd (checkExpr e)
      -- TODO: see Cryptol REPL for how to check whether we
      -- can actually evaluate things, which we can't do in
      -- a parameterized module
     me <- view moduleEnv <$> getState
     let cfg = meSolverConfig me
     perhapsDef <- liftIO $ SMT.withSolver cfg (\s -> defaultReplExpr s ty schema)
     case perhapsDef of
       Nothing ->
         raise (evalPolyErr schema)
       Just (tys, checked) ->
         do -- TODO: warnDefaults here
            let su = listParamSubst tys
            let theType = apSubst su (sType schema)
            res <- runModuleCmd (evalExpr checked)
            prims <- runModuleCmd getPrimMap
            val <- observe $ readBack prims theType res
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
