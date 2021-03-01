{-# LANGUAGE OverloadedStrings #-}
module CryptolServer.FocusedModule
  ( focusedModule
  , focusedModuleDescr
  , FocusedModParams(..)
  ) where

import qualified Argo.Doc as Doc
import Data.Aeson as JSON

import Cryptol.ModuleSystem (meFocusedModule, meLoadedModules)
import Cryptol.ModuleSystem.Env (isLoadedParamMod)
import Cryptol.Utils.PP

import CryptolServer

focusedModuleDescr :: Doc.Block
focusedModuleDescr =
  Doc.Paragraph
    [Doc.Text "The 'current' module. Used to decide how to print names, for example."]

focusedModule :: FocusedModParams -> CryptolCommand JSON.Value
focusedModule _ =
  do me <- getModuleEnv
     case meFocusedModule me of
       Nothing ->
         return $ JSON.object [ "module" .= JSON.Null ]
       Just name ->
         do let parameterized = isLoadedParamMod name (meLoadedModules me)
            return $ JSON.object [ "module" .= pretty name
                                 , "parameterized" .= parameterized
                                 ]

data FocusedModParams = FocusedModParams

instance JSON.FromJSON FocusedModParams where
  parseJSON _ = pure FocusedModParams

instance Doc.DescribedParams FocusedModParams where
  parameterFieldDescription = []
