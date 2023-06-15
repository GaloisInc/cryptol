{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeFamilies      #-}

module Cryptol.Project
  ( Config
  , loadConfig
  , run
  ) where

import           Control.Monad.Except
import           Data.Aeson
import           Data.Functor
import           Data.Maybe
import           Data.Traversable
import           Data.Yaml
import           GHC.Generics
import           System.Directory
import           System.FilePath            as FP
import           System.IO.Error

import           Data.Foldable

import           Cryptol.ModuleSystem.Base
import           Cryptol.ModuleSystem.Env
import           Cryptol.ModuleSystem.Monad as M
import           Cryptol.Parser.Unlit
import           Cryptol.REPL.Command
import           Cryptol.REPL.Monad         as REPL
import           Cryptol.Utils.PP           as PP

type family MaybeIf (opt :: Bool) t where
  MaybeIf 'True t = Maybe t
  MaybeIf 'False t = t

data GenericConfig (opt :: Bool) = Config
  { root    :: MaybeIf opt FilePath
  , modules :: MaybeIf opt [FilePath] }
  deriving Generic

type ParsedConfig = GenericConfig 'True
type Config = GenericConfig 'False

instance FromJSON ParsedConfig where
  parseJSON = genericParseJSON defaultOptions { rejectUnknownFields = True }

data ConfigLoadError = ConfigLoadError FilePath ConfigLoadErrorInfo

data ConfigLoadErrorInfo
  = ConfigParseError ParseException
  | SetRootFailed IOError

instance PP ConfigLoadError where
  ppPrec _ (ConfigLoadError path info) =
    hang ("Error loading project configuration" <+> text path PP.<.> ":")
       4 (pp info)

instance PP ConfigLoadErrorInfo where
  ppPrec _ (ConfigParseError exn) =
    text (prettyPrintParseException exn)
  ppPrec _ (SetRootFailed ioe) =
    hang "Failed to set project root:"
       4 (text (show ioe))

loadConfig :: FilePath -> IO (Either ConfigLoadError Config)
loadConfig path = do
  isDir <- doesDirectoryExist path
  let filePath = if isDir then path FP.</> "cryproject.yaml" else path
  runExceptT $ withExceptT (ConfigLoadError filePath) do
    Config {..} <- withExceptT ConfigParseError do
      ExceptT (decodeFileEither @ParsedConfig filePath)
        <&> \Config {..} -> Config
          { root = fromMaybe "." root
          , modules = fromMaybe ["."] modules } :: Config
    withExceptT SetRootFailed $ ExceptT $ tryIOError $
      setCurrentDirectory (takeDirectory filePath FP.</> root)
    pure Config {..}

run :: Config -> REPL CommandResult
run Config {..} = do
  minp <- getModuleInput
  (res, warnings) <- REPL.io $ runModuleM minp do
    let load path = do
          isDir <- M.io $ doesDirectoryExist path
          if isDir
            then M.io (tryIOError (listDirectory path)) >>= \case
              Left err -> otherIOError path err
              Right entries -> concat <$> for entries \case
                '.':_ -> pure []
                entry -> load (path FP.</> entry)
            else case takeExtension path of
              '.':ext
                | ext `elem` knownExts ->
                  pure <$> loadModuleByPath True path
              _ -> pure []
    concat <$> traverse load modules
  printModuleWarnings warnings
  case res of
    Left err -> do
      names <- mctxNameDisp <$> REPL.getFocusedEnv
      rPrint $ pp $ ModuleSystemError names err
      pure emptyCommandResult { crSuccess = False }
    Right (tops, _) -> do
      rPutStrLn "all loaded!"
      for_ tops \t -> do
        rPrint $ pp t
      pure emptyCommandResult
