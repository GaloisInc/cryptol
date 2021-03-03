{-# LANGUAGE OverloadedStrings #-}
module CryptolServer.TypeCheck
  ( checkType
  , checkTypeDescr
  , TypeCheckParams(..)
  ) where

import qualified Argo.Doc as Doc

--import Control.Lens hiding ((.=))
import Data.Aeson as JSON

import Cryptol.ModuleSystem (checkExpr)
import Cryptol.ModuleSystem.Env (meSolverConfig)

import CryptolServer
import CryptolServer.Exceptions
import CryptolServer.Data.Expression
import CryptolServer.Data.Type

checkTypeDescr :: Doc.Block
checkTypeDescr =
  Doc.Paragraph [Doc.Text "Check and return the type of the given expression."]

checkType :: TypeCheckParams -> CryptolCommand JSON.Value
checkType (TypeCheckParams e) =
  do e' <- getExpr e
     (_expr, _ty, schema) <- runModuleCmd (checkExpr e')
     -- FIXME: why are we running this command if the result isn't used?
     _cfg <- meSolverConfig <$> getModuleEnv
     return (JSON.object [ "type schema" .= JSONSchema schema ])
  where
    -- FIXME: Why is this check not being used?
    _noDefaults [] = return ()
    _noDefaults xs@(_:_) = raise (unwantedDefaults xs)

newtype TypeCheckParams =
  TypeCheckParams Expression

instance JSON.FromJSON TypeCheckParams where
  parseJSON =
    JSON.withObject "params for \"check type\"" $
    \o -> TypeCheckParams <$> o .: "expression"

instance Doc.DescribedParams TypeCheckParams where
  parameterFieldDescription =
    [("expression",
      Doc.Paragraph [Doc.Text "Expression to type check."])
    ]
