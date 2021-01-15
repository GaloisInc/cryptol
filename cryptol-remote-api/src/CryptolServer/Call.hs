{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
module CryptolServer.Call
  ( Expression(..)
  , Encoding(..)
  , LetBinding(..)
  , call
  , CallParams(..)
  ) where

import qualified Argo.Doc as Doc
import Data.Aeson as JSON hiding (Encoding, Value, decode)
import qualified Data.Aeson as JSON

import CryptolServer
import CryptolServer.Data.Expression
import CryptolServer.EvalExpr (evalExpression')

call :: CallParams -> CryptolMethod JSON.Value
call (CallParams rawFun rawArgs) =
  do fun <- getExpr rawFun
     args <- traverse getExpr rawArgs
     let appExpr = mkEApp fun args
     evalExpression' appExpr


data CallParams
  = CallParams Expression [Expression]

instance FromJSON CallParams where
  parseJSON =
    withObject "params for \"call\"" $
    \o -> CallParams <$> o .: "function" <*> o .: "arguments"

instance Doc.DescribedParams CallParams where
  parameterFieldDescription =
    [("function",
      Doc.Paragraph [Doc.Text "The function being called."])
    , ("arguments",
      Doc.Paragraph [Doc.Text "The arguments the function is being applied to."])
    ]
