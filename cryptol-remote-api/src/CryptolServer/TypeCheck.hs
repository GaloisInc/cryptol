{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
module CryptolServer.TypeCheck
  ( checkType
  , checkTypeDescr
  , TypeCheckParams(..)
  ) where

import qualified Argo.Doc as Doc

--import Control.Lens hiding ((.=))
import Data.Aeson as JSON
import Data.Typeable

import Cryptol.ModuleSystem (checkExpr)

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

instance Doc.DescribedMethod TypeCheckParams JSON.Value where
  parameterFieldDescription =
    [("expression",
      Doc.Paragraph [Doc.Text "Expression to type check."])
    ]

  resultFieldDescription =
    [("type schema",
      Doc.Paragraph [Doc.Text "A ", Doc.Link (Doc.TypeDesc (typeRep (Proxy @JSONSchema))) "JSON Cryptol Type"])
    ]
