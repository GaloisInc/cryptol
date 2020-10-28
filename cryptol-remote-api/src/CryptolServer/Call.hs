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

import Data.Aeson as JSON hiding (Encoding, Value, decode)
import qualified Data.Aeson as JSON

import Argo

import CryptolServer
import CryptolServer.Data.Expression
import CryptolServer.EvalExpr (evalExpression')

call :: CallParams -> Method ServerState JSON.Value
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
