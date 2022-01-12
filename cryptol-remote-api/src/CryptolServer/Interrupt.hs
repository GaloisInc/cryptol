{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
module CryptolServer.Interrupt
  ( interruptServer
  , interruptServerDescr
  ) where

import qualified Argo
import qualified Argo.Doc as Doc
import qualified Data.Aeson as JSON

import CryptolServer



------------------------------------------------------------------------
-- Interrupt All Threads Command
data InterruptServerParams = InterruptServerParams

instance JSON.FromJSON InterruptServerParams where
  parseJSON =
    JSON.withObject "params for \"interrupt\"" $
    \_ -> pure InterruptServerParams

instance Doc.DescribedMethod InterruptServerParams () where
  parameterFieldDescription = []

interruptServerDescr :: Doc.Block
interruptServerDescr =
  Doc.Paragraph [Doc.Text "Interrupt the server, terminating it's current task (if one exists)."]

interruptServer :: InterruptServerParams -> CryptolNotification ()
interruptServer _ = CryptolNotification . const $ Argo.interruptAllThreads
