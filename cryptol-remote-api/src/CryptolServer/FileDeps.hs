{-# Language BlockArguments #-}
{-# Language OverloadedStrings #-}
{-# Language MultiParamTypeClasses #-}
module CryptolServer.FileDeps
  ( fileDeps
  , fileDepsDescr
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Set as Set
import Control.Monad.IO.Class(liftIO)
import System.Directory(canonicalizePath)

import qualified Data.Aeson as JSON
import Data.Aeson (FromJSON(..),ToJSON(..),(.=),(.:))
import qualified Argo.Doc as Doc

import Cryptol.Parser.AST (ModName)
import Cryptol.Parser (parseModName)
import Cryptol.ModuleSystem.Env
  (LoadedModuleG(..), FileInfo(..), lookupTCEntity, ModulePath(..))
import Cryptol.ModuleSystem.Fingerprint(fingerprintHexString)
import Cryptol.Utils.PP(pp)

import CryptolServer
import CryptolServer.Exceptions(moduleNotLoaded)

data FileDepsParams = FileDepsOfModule ModName

data FileDeps = FileDeps
  { fdSource :: ModulePath
  , fdInfo   :: FileInfo
  }

fileDeps :: FileDepsParams -> CryptolCommand FileDeps
fileDeps (FileDepsOfModule m) =
  do env <- getModuleEnv
     case lookupTCEntity m env of
       Nothing -> raise (moduleNotLoaded m)
       Just lm ->
         do src <- case lmFilePath lm of
                     InFile f' -> InFile <$> liftIO (canonicalizePath f')
                     InMem l x -> pure (InMem l x)
            pure FileDeps { fdSource = src, fdInfo = lmFileInfo lm }


fileDepsDescr :: Doc.Block
fileDepsDescr =
  txt [ "Get information about the dependencies of a loaded top-level module."
      , "The dependencies include the dependencies of modules nested in this one."
      ]

txt :: [Text] -> Doc.Block
txt xs = Doc.Paragraph (map Doc.Text xs)

instance FromJSON FileDepsParams where
  parseJSON =
    JSON.withObject "params for \"file deps\"" $
    \o -> do val <- o .: "module name"
             JSON.withText
                "module name"
                (\str ->
                    case parseModName (Text.unpack str) of
                      Nothing -> mempty
                      Just n  -> return (FileDepsOfModule n))
                val

instance ToJSON FileDeps where
  toJSON fd =
    JSON.object
      [ "source"      .= case fdSource fd of
                           InFile f  -> toJSON f
                           InMem l _ -> JSON.object [ "internal" .= l ]
      , "fingerprint" .= fingerprintHexString (fiFingerprint fi)
      , "includes"    .= Set.toList (fiForeignDeps fi)
      , "imports"     .= map (show . pp) (Set.toList (fiImportDeps fi))
      , "foreign"     .= Set.toList (fiForeignDeps fi)
      ]
    where
    fi = fdInfo fd


instance Doc.DescribedMethod FileDepsParams FileDeps where
  parameterFieldDescription =
    [ ("module name", txt ["Get information about this loaded module."])
    ]

  resultFieldDescription =
    [ ("source",      txt [ "File containing the module."
                          , "For internal modules this is an object { internal: LABEL }"
                          ])
    , ("fingerprint", txt ["A hash of the module content."])
    , ("includes",    txt ["Files included in this module"])
    , ("imports",     txt ["Modules imported by this module"])
    , ("foreign",     txt ["Foreign libraries loaded by this module"])
    ]


