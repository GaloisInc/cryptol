{-# LANGUAGE OverloadedStrings #-}
module CryptolServer.ChangeDir (cd, ChangeDirectoryParams(..)) where

import Control.Monad.IO.Class
import Data.Aeson as JSON
import System.Directory

import CryptolServer
import CryptolServer.Exceptions
import Argo

cd :: ChangeDirectoryParams -> Method ServerState ()
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
