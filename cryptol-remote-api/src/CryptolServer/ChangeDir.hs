{-# LANGUAGE OverloadedStrings #-}
module CryptolServer.ChangeDir
  ( cd
  , cdDescr
  , ChangeDirectoryParams(..)
  ) where

import qualified Argo.Doc as Doc
import Control.Monad.IO.Class
import Data.Aeson as JSON
import System.Directory

import CryptolServer
import CryptolServer.Exceptions


cdDescr :: Doc.Block
cdDescr = Doc.Paragraph
            [Doc.Text "Changes the server's working directory to the given path."]

cd :: ChangeDirectoryParams -> CryptolCommand ()
cd (ChangeDirectoryParams newDir) =
  do exists <- liftIO $ doesDirectoryExist newDir
     if exists
       then liftIO $ setCurrentDirectory newDir
       else raise (dirNotFound newDir)

data ChangeDirectoryParams
  = ChangeDirectoryParams FilePath

instance FromJSON ChangeDirectoryParams where
  parseJSON =
    withObject "params for \"change directory\"" $
    \o -> ChangeDirectoryParams <$> o .: "directory"

instance Doc.DescribedParams ChangeDirectoryParams where
  parameterFieldDescription =
    [("directory",
      Doc.Paragraph [Doc.Text "The path to change the current directory."])
    ]
