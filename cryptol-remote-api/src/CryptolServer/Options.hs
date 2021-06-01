{-# OPTIONS_GHC -fno-warn-type-defaults -Wno-missing-deriving-strategies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
module CryptolServer.Options (Options(..), WithOptions(..)) where

import qualified Argo.Doc as Doc
import Data.Aeson hiding (Options)
import Data.Aeson.Types (Parser, typeMismatch)
import Data.Coerce
import qualified Data.HashMap.Strict as HM
import qualified Data.Text as T

import Cryptol.Eval(EvalOpts(..))
import Cryptol.REPL.Monad (parseFieldOrder, parsePPFloatFormat)
import Cryptol.Utils.Logger (quietLogger)
import Cryptol.Utils.PP (PPOpts(..), PPFloatFormat(..), PPFloatExp(..), FieldOrder(..), defaultPPOpts)

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
           newtypeField getFloatFormat o "floating point format" (FloatFree AutoExponent) <*>
           newtypeField getFieldOrder o "field order" DisplayOrder

newtypeField :: forall wrapped bare proxy.
  (Coercible wrapped bare, FromJSON wrapped) =>
  proxy wrapped bare ->
  Object -> T.Text -> bare -> Parser bare
newtypeField _proxy o field def = unwrap (o .:! field) .!= def where
  unwrap :: Parser (Maybe wrapped) -> Parser (Maybe bare)
  unwrap = coerce


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


newtype JSONFieldOrder = JSONFieldOrder { getFieldOrder :: FieldOrder }

instance FromJSON JSONFieldOrder where
  parseJSON (String t)
    | Just order <- parseFieldOrder (T.unpack t) = pure $ JSONFieldOrder order
  parseJSON v = typeMismatch "field order (\"display\" or \"canonical\")" v


instance FromJSON Options where
  parseJSON =
    withObject "options" $
    \o -> Options <$> o .:! "call stacks" .!= False <*> (getEvalOpts <$> o .:! "output" .!= JSONEvalOpts theEvalOpts)

data WithOptions a = WithOptions Options a
  deriving Functor

instance forall params result . Doc.DescribedMethod params result => Doc.DescribedMethod (WithOptions params) result where
  parameterFieldDescription = Doc.parameterFieldDescription @params
  resultFieldDescription    = Doc.resultFieldDescription @params @result

instance FromJSON a => FromJSON (WithOptions a) where
  parseJSON = withObject "parameters with options" $
    \o ->
      WithOptions <$>
      o .:! "options" .!= defaultOpts <*>
      parseJSON (Object (HM.delete "options" o))

defaultOpts :: Options
defaultOpts = Options False theEvalOpts

theEvalOpts :: EvalOpts
theEvalOpts = EvalOpts quietLogger defaultPPOpts
  { useInfLength = 25
  , useFPBase = 10
  }
