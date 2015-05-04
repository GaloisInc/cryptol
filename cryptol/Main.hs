-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
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
import Cryptol.Version (commitHash, commitBranch, commitDirty)
import Paths_cryptol (version)

import Data.Version (showVersion)
import GHC.IO.Encoding (setLocaleEncoding, utf8)
import System.Console.GetOpt
    (OptDescr(..),ArgOrder(..),ArgDescr(..),getOpt,usageInfo)
import System.Environment (getArgs, getProgName, lookupEnv)
import System.Exit (exitFailure)
import System.FilePath (searchPathSeparator, splitSearchPath, takeDirectory)

#if __GLASGOW_HASKELL__ < 710
import Data.Monoid (mconcat)
#endif

data Options = Options
  { optLoad            :: [FilePath]
  , optVersion         :: Bool
  , optHelp            :: Bool
  , optBatch           :: Maybe FilePath
  , optCryptolrc       :: Cryptolrc
  , optCryptolPathOnly :: Bool
  } deriving (Show)

defaultOptions :: Options
defaultOptions  = Options
  { optLoad            = []
  , optVersion         = False
  , optHelp            = False
  , optBatch           = Nothing
  , optCryptolrc       = CryrcDefault
  , optCryptolPathOnly = False
  }

options :: [OptDescr (OptParser Options)]
options  =
  [ Option "b" ["batch"] (ReqArg setBatchScript "FILE")
    "run the script provided and exit"

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
      | otherwise       -> repl (optCryptolrc opts)
                                (optBatch opts)
                                (setupREPL opts)

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
    [l] -> loadCmd l `REPL.catch` \x -> io $ print $ pp x
    _   -> io $ putStrLn "Only one file may be loaded at the command line."
