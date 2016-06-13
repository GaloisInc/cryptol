-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import OptParser

import Cryptol.REPL.Command (loadCmd,loadPrelude)
import Cryptol.REPL.Monad (REPL,updateREPLTitle,setUpdateREPLTitle,
                   io,prependSearchPath,setSearchPath)
import qualified Cryptol.REPL.Monad as REPL

import REPL.Haskeline
import REPL.Logo

import Cryptol.Utils.PP
import Cryptol.Utils.Color (warningMsg)
import Cryptol.Version (commitHash, commitBranch, commitDirty)
import Paths_cryptol (version)

import Control.Monad (when)
import Data.Maybe (isJust)
import Data.Version (showVersion)
import GHC.IO.Encoding (setLocaleEncoding, utf8)
import System.Console.GetOpt
    (OptDescr(..),ArgOrder(..),ArgDescr(..),getOpt,usageInfo)
import System.Directory (getTemporaryDirectory, removeFile)
import System.Environment (getArgs, getProgName, lookupEnv)
import System.Exit (exitFailure)
import System.FilePath (searchPathSeparator, splitSearchPath, takeDirectory)
import System.IO (hClose, hPutStr, openTempFile)


import Prelude ()
import Prelude.Compat

data Options = Options
  { optLoad            :: [FilePath]
  , optVersion         :: Bool
  , optHelp            :: Bool
  , optBatch           :: Maybe FilePath
  , optCommands        :: [String]
  , optCryptolrc       :: Cryptolrc
  , optCryptolPathOnly :: Bool
  } deriving (Show)

defaultOptions :: Options
defaultOptions  = Options
  { optLoad            = []
  , optVersion         = False
  , optHelp            = False
  , optBatch           = Nothing
  , optCommands        = []
  , optCryptolrc       = CryrcDefault
  , optCryptolPathOnly = False
  }

options :: [OptDescr (OptParser Options)]
options  =
  [ Option "b" ["batch"] (ReqArg setBatchScript "FILE")
    "run the script provided and exit"

  , Option "c" ["command"] (ReqArg addCommand "COMMAND")
    (concat [ "run the given command and then exit; if multiple --command "
            , "arguments are given, run them in the order they appear "
            , "on the command line (overrides --batch)"
            ])

  , Option "v" ["version"] (NoArg setVersion)
    "display version number"

  , Option "h" ["help"] (NoArg setHelp)
    "display this message"

  , Option ""  ["ignore-cryptolrc"] (NoArg setCryrcDisabled)
    "disable reading of .cryptolrc files"

  , Option ""  ["cryptolrc-script"] (ReqArg addCryrc "FILE")
    "read additional .cryptolrc files"

  , Option ""  ["cryptolpath-only"] (NoArg setCryptolPathOnly)
    "only look for .cry files in CRYPTOLPATH; don't use built-in locations"
  ]

-- | Set a single file to be loaded.  This should be extended in the future, if
-- we ever plan to allow multiple files to be loaded at the same time.
addFile :: String -> OptParser Options
addFile path = modify $ \ opts -> opts { optLoad = [ path ] }

-- | Add a command to be run on interpreter startup.
addCommand :: String -> OptParser Options
addCommand cmd =
  modify $ \ opts -> opts { optCommands = cmd : optCommands opts }

-- | Set a batch script to be run.
setBatchScript :: String -> OptParser Options
setBatchScript path = modify $ \ opts -> opts { optBatch = Just path }

-- | Signal that version should be displayed.
setVersion :: OptParser Options
setVersion  = modify $ \ opts -> opts { optVersion = True }

-- | Signal that help should be displayed.
setHelp :: OptParser Options
setHelp  = modify $ \ opts -> opts { optHelp = True }

-- | Disable .cryptolrc files entirely
setCryrcDisabled :: OptParser Options
setCryrcDisabled  = modify $ \ opts -> opts { optCryptolrc = CryrcDisabled }

-- | Add another file to read as a @.cryptolrc@ file, unless @.cryptolrc@
-- files have been disabled
addCryrc :: String -> OptParser Options
addCryrc path = modify $ \ opts ->
  case optCryptolrc opts of
    CryrcDefault  -> opts { optCryptolrc = CryrcFiles [path] }
    CryrcDisabled -> opts
    CryrcFiles xs -> opts { optCryptolrc = CryrcFiles (path:xs) }

setCryptolPathOnly :: OptParser Options
setCryptolPathOnly  = modify $ \opts -> opts { optCryptolPathOnly = True }

-- | Parse arguments.
parseArgs :: [String] -> Either [String] Options
parseArgs args = case getOpt (ReturnInOrder addFile) options args of
  (ps,[],[]) -> runOptParser defaultOptions (mconcat ps)
  (_,_,errs) -> Left errs

displayVersion :: IO ()
displayVersion = do
    let ver = showVersion version
    putStrLn ("Cryptol " ++ ver)
    putStrLn ("Git commit " ++ commitHash)
    putStrLn ("    branch " ++ commitBranch ++ dirtyLab)
      where
      dirtyLab | commitDirty = " (non-committed files present during build)"
               | otherwise   = ""

displayHelp :: [String] -> IO ()
displayHelp errs = do
  prog <- getProgName
  let banner = "Usage: " ++ prog ++ " [OPTIONS]"
      paraLines = fsep . map text . words . unlines
      ppEnv (varname, desc) = hang varname 4 (paraLines $ desc)
      envs = [
          ( "CRYPTOLPATH"
          , [ "A `" ++ [searchPathSeparator] ++ "`-separated"
            , "list of directories to be searched for Cryptol modules in"
            , "addition to the default locations"
            ]
          )
        , ( "SBV_{ABC,BOOLECTOR,CVC4,MATHSAT,YICES,Z3}_OPTIONS"
          , [ "A string of command-line arguments to be passed to the"
            , "corresponding solver invoked for `:sat` and `:prove`"
            ]
          )
        ]
  putStrLn (usageInfo (concat (errs ++ [banner])) options)
  print $ hang "Influential environment variables:"
             4 (vcat (map ppEnv envs))
main :: IO ()
main  = do
  setLocaleEncoding utf8
  args <- getArgs
  case parseArgs args of

    Left errs -> do
      displayHelp errs
      exitFailure

    Right opts
      | optHelp opts    -> displayHelp []
      | optVersion opts -> displayVersion
      | otherwise       -> do
          (opts', mCleanup) <- setupCmdScript opts
          repl (optCryptolrc opts')
               (optBatch opts')
               (setupREPL opts')
          case mCleanup of
            Nothing -> return ()
            Just cmdFile -> removeFile cmdFile

setupCmdScript :: Options -> IO (Options, Maybe FilePath)
setupCmdScript opts =
  case optCommands opts of
    [] -> return (opts, Nothing)
    cmds -> do
      tmpdir <- getTemporaryDirectory
      (path, h) <- openTempFile tmpdir "cmds.icry"
      hPutStr h (unlines cmds)
      hClose h
      when (isJust (optBatch opts)) $
        putStrLn $ warningMsg ++ " --command argument specified; ignoring batch file"
      return (opts { optBatch = Just path }, Just path)

setupREPL :: Options -> REPL ()
setupREPL opts = do
  smoke <- REPL.smokeTest
  case smoke of
    [] -> return ()
    _  -> io $ do
      print (hang "Errors encountered on startup; exiting:"
                4 (vcat (map pp smoke)))
      exitFailure
  displayLogo True
  setUpdateREPLTitle setREPLTitle
  updateREPLTitle
  mCryptolPath <- io $ lookupEnv "CRYPTOLPATH"
  case mCryptolPath of
    Nothing -> return ()
    Just path | optCryptolPathOnly opts -> setSearchPath path'
              | otherwise               -> prependSearchPath path'
#if defined(mingw32_HOST_OS) || defined(__MINGW32__)
      -- Windows paths search from end to beginning
      where path' = reverse (splitSearchPath path)
#else
      where path' = splitSearchPath path
#endif
  case optBatch opts of
    Nothing -> return ()
    -- add the directory containing the batch file to the module search path
    Just file -> prependSearchPath [ takeDirectory file ]
  case optLoad opts of
    []  -> loadPrelude `REPL.catch` \x -> io $ print $ pp x
    [l] -> loadCmd l `REPL.catch` \x -> do
           io $ print $ pp x
           -- If the requested file fails to load, load the prelude instead
           loadPrelude `REPL.catch` \y -> do
           io $ print $ pp y
    _   -> io $ putStrLn "Only one file may be loaded at the command line."
