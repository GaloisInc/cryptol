{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
module CryptolServer.Version
  ( version
  , versionDescr
  , VersionParams(..)
  ) where

import qualified Argo.Doc as Doc
import Data.Aeson as JSON

import qualified Paths_cryptol_remote_api as RPC
import qualified Cryptol.Version as Cry
import Data.Version (showVersion)

import CryptolServer

versionDescr :: Doc.Block
versionDescr =
  Doc.Paragraph
    [Doc.Text "Version information about this Cryptol server."]

version :: VersionParams -> CryptolCommand JSON.Value
version _ =
  return $ JSON.object [ "RPC server version" .= showVersion RPC.version
                       , "version"            .= showVersion Cry.version
                       , "commit hash"        .= Cry.commitHash
                       , "commit branch"      .= Cry.commitBranch
                       , "commit dirty"       .= Cry.commitDirty
                       , "FFI enabled"        .= Cry.ffiEnabled
                       ]

data VersionParams = VersionParams

instance JSON.FromJSON VersionParams where
  parseJSON _ = pure VersionParams

instance Doc.DescribedMethod VersionParams JSON.Value where
  parameterFieldDescription = []

  resultFieldDescription =
    [ ("RPC server version",
      Doc.Paragraph [ Doc.Text "The cryptol-remote-api version string."
                    ])
    , ("version",
      Doc.Paragraph [ Doc.Text "The Cryptol version string."
                    ])
    , ("commit hash",
      Doc.Paragraph [ Doc.Text "The string of the git commit hash during the build of Cryptol."
                    ])
    , ("commit branch",
      Doc.Paragraph [ Doc.Text "The string of the git commit branch during the build of Cryptol."
                    ])
    , ("commit dirty",
      Doc.Paragraph [ Doc.Text "True iff non-committed files were present during the build of Cryptol."
                    ])
    , ("FFI enabled",
      Doc.Paragraph [ Doc.Text "True iff the FFI is enabled."
                    ])
    ]
