{-# OPTIONS_GHC -fno-warn-type-defaults -Wno-missing-deriving-strategies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
module CryptolServer.Options (Options(..), WithOptions(..)) where

import qualified Argo.Doc as Doc
import Data.Aeson hiding (Options)
import qualified Data.HashMap.Strict as HM

import Cryptol.Eval(EvalOpts(..))
import Cryptol.REPL.Monad (parsePPFloatFormat)
import Cryptol.Utils.Logger (quietLogger)
import Cryptol.Utils.PP (PPOpts(..), PPFloatFormat(..), PPFloatExp(..))

data Options = Options { optCallStacks :: Bool, optEvalOpts :: EvalOpts }

newtype JSONEvalOpts = JSONEvalOpts { getEvalOpts :: EvalOpts }

instance FromJSON JSONEvalOpts where
  parseJSON =
    withObject "output options" $
    \o -> fmap (JSONEvalOpts . EvalOpts quietLogger) $
          PPOpts <$>
           o .:! "ASCII" .!= True <*>
           o .:! "base" .!= 10 <*>
           o .:! "prefix of infinite lengths" .!= 5 <*>
           o .:! "floating point base" .!= 10 <*>
           (getFloatFormat <$>
            o .:! "floating point format" .!=
            JSONFloatFormat (FloatFree AutoExponent))

newtype JSONFloatFormat = JSONFloatFormat { getFloatFormat :: PPFloatFormat }

instance FromJSON JSONFloatFormat where
  parseJSON =
    withObject "floating point format" $
    \o ->
      fmap JSONFloatFormat $
      do str <- o .: "format"
         case parsePPFloatFormat str of
           Just fmt ->
             pure fmt
           Nothing ->
             fail $ "Expected a valid floating point spec as in the Cryptol REPL, but got " ++ str


instance FromJSON Options where
  parseJSON =
    withObject "options" $
    \o -> Options <$> o .:! "call stacks" .!= False <*> (getEvalOpts <$> o .:! "output" .!= JSONEvalOpts theEvalOpts)

data WithOptions a = WithOptions Options a
  deriving Functor

instance forall params . Doc.DescribedParams params => Doc.DescribedParams (WithOptions params) where
  parameterFieldDescription = (Doc.parameterFieldDescription @params)

instance FromJSON a => FromJSON (WithOptions a) where
  parseJSON = withObject "parameters with options" $
    \o ->
      WithOptions <$>
      o .:! "options" .!= defaultOpts <*>
      parseJSON (Object (HM.delete "options" o))

defaultOpts :: Options
defaultOpts = Options False theEvalOpts

theEvalOpts :: EvalOpts
theEvalOpts = EvalOpts quietLogger (PPOpts False 10 25 10 (FloatFree AutoExponent))
