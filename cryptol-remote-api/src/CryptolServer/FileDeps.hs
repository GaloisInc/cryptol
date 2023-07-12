{-# Language BlockArguments #-}
{-# Language OverloadedStrings #-}
{-# Language MultiParamTypeClasses #-}
module CryptolServer.FileDeps
  ( fileDeps
  , fileDepsDescr
  ) where

import Data.Text (Text)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map

import qualified Data.Aeson as JSON
import Data.Aeson (FromJSON(..),ToJSON(..),(.=),(.:))
import qualified Argo.Doc as Doc

import Cryptol.Parser.AST (ModName)
import Cryptol.Parser (parseModName)
import Cryptol.ModuleSystem(getFileDependencies,getModuleDependencies)
import Cryptol.ModuleSystem.Env (FileInfo(..), ModulePath(..))
import Cryptol.ModuleSystem.Fingerprint(fingerprintHexString)
import Cryptol.Utils.PP(pp)

import CryptolServer

data FileDepsParams = FileDepsOfModule ModName
                    | FileDepsOfFile FilePath

data FileDeps = FileDeps
  { fdSource :: ModulePath
  , fdInfo   :: FileInfo
  }

fileDeps :: FileDepsParams -> CryptolCommand FileDeps
fileDeps param =
  do (p,fi) <- case param of
                 FileDepsOfFile f   -> liftModuleCmd (getFileDependencies f)
                 FileDepsOfModule m -> liftModuleCmd (getModuleDependencies m)
     pure FileDeps { fdSource = p, fdInfo = fi }

fileDepsDescr :: Doc.Block
fileDepsDescr =
  txt [ "Get information about the dependencies of a file or module."
      , " The dependencies include the dependencies of modules nested in this one."
      ]

txt :: [Text] -> Doc.Block
txt xs = Doc.Paragraph (map Doc.Text xs)

instance FromJSON FileDepsParams where
  parseJSON =
    JSON.withObject "params for \"file deps\"" $
    \o -> do name   <- o .: "name"
             isFile <- o .: "is-file"
             if isFile
               then pure (FileDepsOfFile name)
               else case parseModName name of
                      Nothing -> mempty
                      Just n  -> return (FileDepsOfModule n)



instance ToJSON FileDeps where
  toJSON fd =
    JSON.object
      [ "source"      .= case fdSource fd of
                           InFile f  -> toJSON f
                           InMem l _ -> JSON.object [ "internal" .= l ]
      , "fingerprint" .= fingerprintHexString (fiFingerprint fi)
      , "includes"    .= Map.keys (fiIncludeDeps fi)
      , "imports"     .= map (show . pp) (Set.toList (fiImportDeps fi))
      , "foreign"     .= Map.toList (fiForeignDeps fi)
      ]
    where
    fi = fdInfo fd


instance Doc.DescribedMethod FileDepsParams FileDeps where
  parameterFieldDescription =
    [ ("name", txt ["Get information about this entity."])
    , ("is-file", txt ["Indicates if the name is a file (true) or module (false)"])
    ]

  resultFieldDescription =
    [ ("source",      txt [ "File containing the module."
                          , " For internal modules this is an object { internal: \"LABEL\" }."
                          ])
    , ("fingerprint", txt ["A hash of the module content."])
    , ("includes",    txt ["Files included in this module."])
    , ("imports",     txt ["Modules imported by this module."])
    , ("foreign",     txt ["Foreign libraries loaded by this module."])
    ]


