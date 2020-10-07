{-# LANGUAGE OverloadedStrings #-}
module CryptolServer.LoadModule
  ( loadFile
  , loadModule
  , LoadFileParams(..)
  , LoadModuleParams(..)
  ) where

import Control.Applicative
import Data.Aeson as JSON
import qualified Data.Text as T
import Data.Functor

import Cryptol.ModuleSystem (loadModuleByPath, loadModuleByName)
import Cryptol.Parser (parseModName)
import Cryptol.Parser.AST (ModName)

import CryptolServer
import Argo


loadFile :: LoadFileParams -> Method ServerState ()
loadFile (LoadFileParams fn) =
  void $ runModuleCmd (loadModuleByPath fn)

newtype LoadFileParams
  = LoadFileParams FilePath

instance JSON.FromJSON LoadFileParams where
  parseJSON =
    JSON.withObject "params for \"load module\"" $
    \o -> LoadFileParams <$> o .: "file"

loadModule :: LoadModuleParams -> Method ServerState ()
loadModule (LoadModuleParams mn) =
  void $ runModuleCmd (loadModuleByName mn)

newtype JSONModuleName
  = JSONModuleName { unJSONModName :: ModName }

instance JSON.FromJSON JSONModuleName where
  parseJSON =
    JSON.withText "module name" $
    \txt ->
      case parseModName (T.unpack txt) of
        Nothing -> empty
        Just n -> return (JSONModuleName n)

newtype LoadModuleParams
  = LoadModuleParams ModName

instance JSON.FromJSON LoadModuleParams where
  parseJSON =
    JSON.withObject "params for \"load module\"" $
    \o -> LoadModuleParams . unJSONModName <$> o .: "module name"
