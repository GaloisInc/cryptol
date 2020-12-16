{-# LANGUAGE OverloadedStrings #-}
module CryptolServer.FocusedModule (focusedModule, FocusedModParams(..)) where

import Data.Aeson as JSON

import Cryptol.ModuleSystem (meFocusedModule, meLoadedModules)
import Cryptol.ModuleSystem.Env (isLoadedParamMod)
import Cryptol.Utils.PP

import CryptolServer

focusedModule :: FocusedModParams -> CryptolMethod JSON.Value
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
