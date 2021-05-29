{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
module CryptolServer.ExtendSearchPath
  ( extSearchPath
  , extSearchPathDescr
  , ExtendSearchPathParams(..)
  ) where


import qualified Argo
import qualified Argo.Doc as Doc
import Data.Aeson as JSON ( (.:), withObject, FromJSON(parseJSON) )

import CryptolServer

-- | Documentation for @extendSearchPath@
extSearchPathDescr :: Doc.Block
extSearchPathDescr =
  Doc.Paragraph
    [Doc.Text "Extend the server's search path with the given paths."]

-- | Extend the search path with the provided directories.
extSearchPath :: ExtendSearchPathParams -> CryptolCommand ()
extSearchPath (ExtendSearchPathParams newDirs) =
  CryptolCommand $ const $ Argo.modifyState (extendSearchPath newDirs)

data ExtendSearchPathParams
  = ExtendSearchPathParams [FilePath]

instance FromJSON ExtendSearchPathParams where
  parseJSON =
    withObject "params for \"extend search path\"" $
    \o -> ExtendSearchPathParams <$> o .: "paths"

instance Doc.DescribedMethod ExtendSearchPathParams () where
  parameterFieldDescription =
    [("paths",
      Doc.Paragraph [Doc.Text "The paths to add to the search path."])
    ]
