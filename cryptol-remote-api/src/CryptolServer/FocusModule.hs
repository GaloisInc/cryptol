{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BlockArguments #-}
module CryptolServer.FocusModule
  ( focusModule
  , focusModuleDescr
  , FocusModuleParams(..)
  ) where

import qualified Argo.Doc as Doc
import Control.Applicative
import Data.Aeson as JSON
import qualified Data.Text as T

import Cryptol.ModuleSystem (meFocusedModule, renameImpNameInCurrentEnv)
import Cryptol.Parser (parseImpName)

import CryptolServer
import Cryptol.Parser.AST (ImpName, PName)
import Cryptol.ModuleSystem.Monad (runModuleM)

focusModuleDescr :: Doc.Block
focusModuleDescr = Doc.Paragraph [Doc.Text "Focus the specified module (by name)."]

focusModule :: FocusModuleParams -> CryptolCommand ()
focusModule (FocusModuleParams pimpName) =
 do resetTCSolver
    impName <- liftModuleCmd (`runModuleM` renameImpNameInCurrentEnv pimpName)
    modifyModuleEnv \env -> env { meFocusedModule = Just impName }

newtype JSONModuleName
  = JSONModuleName { unJSONModName :: ImpName PName }

instance JSON.FromJSON JSONModuleName where
  parseJSON =
    JSON.withText "module name" $
    \txt ->
      case parseImpName (T.unpack txt) of
        Nothing -> empty
        Just n -> return (JSONModuleName n)

newtype FocusModuleParams
  = FocusModuleParams (ImpName PName)

instance JSON.FromJSON FocusModuleParams where
  parseJSON =
    JSON.withObject "params for \"focus module\"" $
    \o -> FocusModuleParams . unJSONModName <$> o .: "module name"

instance Doc.DescribedMethod FocusModuleParams () where
  parameterFieldDescription =
    [("module name",
      Doc.Paragraph [Doc.Text "Name of module to focus."])
    ]
