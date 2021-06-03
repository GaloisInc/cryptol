{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
module CryptolServer.LoadModule
  ( loadFile
  , loadFileDescr
  , loadModule
  , loadModuleDescr
  , LoadFileParams(..)
  , LoadModuleParams(..)
  ) where

import qualified Argo.Doc as Doc
import Control.Applicative
import Data.Aeson as JSON
import qualified Data.Text as T
import Data.Functor

import Cryptol.ModuleSystem (loadModuleByPath, loadModuleByName)
import Cryptol.Parser (parseModName)
import Cryptol.Parser.AST (ModName)

import CryptolServer

loadFileDescr :: Doc.Block
loadFileDescr = Doc.Paragraph [Doc.Text "Load the specified module (by file path)."]

loadFile :: LoadFileParams -> CryptolCommand ()
loadFile (LoadFileParams fn) =
  void $ liftModuleCmd (loadModuleByPath fn)

newtype LoadFileParams
  = LoadFileParams FilePath

instance JSON.FromJSON LoadFileParams where
  parseJSON =
    JSON.withObject "params for \"load module\"" $
    \o -> LoadFileParams <$> o .: "file"


instance Doc.DescribedMethod LoadFileParams () where
  parameterFieldDescription =
    [("file",
      Doc.Paragraph [Doc.Text "File path of the module to load."])
    ]



loadModuleDescr :: Doc.Block
loadModuleDescr = Doc.Paragraph [Doc.Text "Load the specified module (by name)."]

loadModule :: LoadModuleParams -> CryptolCommand ()
loadModule (LoadModuleParams mn) =
  void $ liftModuleCmd (loadModuleByName mn)

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

instance Doc.DescribedMethod LoadModuleParams () where
  parameterFieldDescription =
    [("module name",
      Doc.Paragraph [Doc.Text "Name of module to load."])
    ]
