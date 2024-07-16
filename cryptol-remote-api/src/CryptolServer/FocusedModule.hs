{-# LANGUAGE MultiParamTypeClasses #-}
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
import qualified Cryptol.TypeCheck.AST as T
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
         do let parameterized =
                  case name of
                    T.ImpTop top -> isLoadedParamMod top (meLoadedModules me)
                    _ -> False
            return $ JSON.object [ "module" .= pretty name
                                 , "parameterized" .= parameterized
                                 ]

data FocusedModParams = FocusedModParams

instance JSON.FromJSON FocusedModParams where
  parseJSON _ = pure FocusedModParams

instance Doc.DescribedMethod FocusedModParams JSON.Value where
  parameterFieldDescription = []

  resultFieldDescription =
    [ ("module",
      Doc.Paragraph [ Doc.Text "The name of the focused module, which would be shown in the "
                    , Doc.Text "prompt in the Cryptol REPL, or "
                    , Doc.Literal "null", Doc.Text " if there is no such focused module."
                    ])
    , ("parameterized",
      Doc.Paragraph [ Doc.Text "A Boolean value indicating whether the focused module is "
                    , Doc.Text "parameterized. This field is only present when the module name is not "
                    , Doc.Literal "null", Doc.Text "."
                    ])
    ]
