{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE OverloadedStrings #-}
module Cryptol.Project.Config where

import           Data.Maybe                       (fromMaybe)
import qualified Data.Text.IO                     as Text
import           Toml
import           Toml.Schema
import           Data.Bifunctor (first)
import           System.Directory
import           System.FilePath                  as FP
import           System.IO.Error

import           Cryptol.Utils.PP                 as PP

data Config = Config
  { root    :: FilePath
    -- ^ The root of the project.

  , modules :: [String]
    -- ^ Git-style patterns describing the files for the project.
  } deriving Show

data LoadProjectMode
  = RefreshMode 
    -- ^ load all files
  | ModifiedMode
    -- ^ load modified files
  | UntestedMode CheckFailedMode
    -- ^ load files without a successful test result
  deriving Show

-- | Indicates if we should load files that have not changed, but
-- contain failed properties.
data CheckFailedMode = RecheckFailed | CachedFailed
  deriving Show

instance FromValue Config where
  fromValue =
    parseTableFromValue
    do mbRoot <- optKey "root"
       mods <- reqKey "modules"
       pure Config
         { root = fromMaybe "." mbRoot
         , modules = mods
         }

data ConfigLoadError = ConfigLoadError FilePath ConfigLoadErrorInfo
  deriving Show

data ConfigLoadErrorInfo
  = ConfigParseError [String]
  | SetRootFailed IOError
  deriving Show

instance PP ConfigLoadError where
  ppPrec _ (ConfigLoadError path info) =
    case info of
      ConfigParseError errs -> text (unlines errs)
      SetRootFailed ioe ->
        hang topMsg
           4 (hang "Failed to set project root:"
                 4 (text (show ioe)))
    where
    topMsg = "Error loading project configuration" <+> text path PP.<.> ":"

-- | Parse project configuration.
loadConfig :: FilePath -> IO (Either ConfigLoadError Config)
loadConfig path =
  do isDir <- doesDirectoryExist path
     let filePath = if isDir then path FP.</> "cryproject.toml" else path
     -- Use strict IO since we are writing to the same file later
     file <- Text.readFile filePath
     first (ConfigLoadError filePath) <$>
       case decode file of
         Failure errs  -> pure (Left (ConfigParseError errs))
         Success _warns config ->
           first SetRootFailed <$>
           tryIOError
             do dir <- canonicalizePath
                                    (takeDirectory filePath FP.</> root config)
                setCurrentDirectory dir
                pure config { root = dir }
