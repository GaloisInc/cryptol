{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE NamedFieldPuns   #-}
{-# LANGUAGE OverloadedStrings #-}
module Cryptol.Project.Config where

import qualified Data.Text                        as Text
import           Data.YAML
import qualified Data.ByteString                  as BS.Strict
import qualified Data.ByteString.Lazy             as BS.Lazy
import           Data.Bifunctor (first)
import           System.Directory
import           System.FilePath                  as FP
import           System.IO.Error

import           Cryptol.Utils.PP                 as PP

data Config = Config
  { root    :: FilePath
  , modules :: [FilePath]
  }

instance FromYAML Config where
  parseYAML = withMap "Config" \m ->
    do root    <- Text.unpack <$> m .:? "root" .!= "."
       modules <- map Text.unpack <$> m .:? "modules" .!= ["."]
       pure Config { root, modules }

data ConfigLoadError = ConfigLoadError FilePath ConfigLoadErrorInfo

data ConfigLoadErrorInfo
  = ConfigParseError BS.Lazy.ByteString (Pos, String)
  | SetRootFailed IOError

instance PP ConfigLoadError where
  ppPrec _ (ConfigLoadError path info) =
    case info of
      ConfigParseError file (pos, err) -> text $
        show topMsg ++ prettyPosWithSource pos file "\nParse error:" ++ err
      SetRootFailed ioe ->
        hang topMsg
           4 (hang "Failed to set project root:"
                 4 (text (show ioe)))
    where
    topMsg = "Error loading project configuration" <+> text path PP.<.> ":"

-- | Parse project configuration.
loadConfig :: FilePath -> IO (Either ConfigLoadError Config)
loadConfig path = do
  isDir <- doesDirectoryExist path
  let filePath = if isDir then path FP.</> "cryproject.yaml" else path
  -- Use strict IO since we are writing to the same file later
  file <- BS.Lazy.fromStrict <$> BS.Strict.readFile filePath
  first (ConfigLoadError filePath) <$>
    case decode1 file of
      Left (pos, err) -> pure (Left (ConfigParseError file (pos, err)))
      Right config ->
        first SetRootFailed <$>
        tryIOError
          do setCurrentDirectory (takeDirectory filePath FP.</> root config)
             pure config


