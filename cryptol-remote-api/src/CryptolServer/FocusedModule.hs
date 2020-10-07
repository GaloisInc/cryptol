{-# LANGUAGE OverloadedStrings #-}
module CryptolServer.FocusedModule (focusedModule, FocusedModParams(..)) where

import Control.Lens hiding ((.=))
import Data.Aeson as JSON


import Cryptol.ModuleSystem (meFocusedModule, meLoadedModules)
import Cryptol.ModuleSystem.Env (isLoadedParamMod)
import Cryptol.Utils.PP

import Argo
import CryptolServer

focusedModule :: FocusedModParams -> Method ServerState JSON.Value
focusedModule _ =
  do me <- view moduleEnv <$> getState
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
