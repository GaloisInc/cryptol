-- |
-- Module      :  Main
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

import Cryptol.REPL.Command (loadCmd,loadPrelude,CommandExitCode(..))
import Cryptol.REPL.Monad (REPL,updateREPLTitle,setUpdateREPLTitle,
                   io,prependSearchPath,setSearchPath)
import qualified Cryptol.REPL.Monad as REPL
import Cryptol.ModuleSystem.Env(ModulePath(..))

import REPL.Haskeline
import REPL.Logo

import Cryptol.Utils.PP
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
import System.Exit (exitFailure,exitSuccess)
import System.FilePath (searchPathSeparator, splitSearchPath, takeDirectory)
import System.IO (hClose, hPutStr, openTempFile)


import Prelude ()
import Prelude.Compat

data ColorMode = AutoColor | NoColor | AlwaysColor
  deriving (Show, Eq)

data Options = Options
  { optLoad            :: [FilePath]
  , optVersion         :: Bool
  , optHelp            :: Bool
  , optBatch           :: Maybe FilePath
  , optCommands        :: [String]
  , optColorMode       :: ColorMode
  , optCryptolrc       :: Cryptolrc
  , optCryptolPathOnly :: Bool
  , optStopOnError     :: Bool
  } deriving (Show)

defaultOptions :: Options
defaultOptions  = Options
  { optLoad            = []
  , optVersion         = False
  , optHelp            = False
  , optBatch           = Nothing
  , optCommands        = []
  , optColorMode       = AutoColor
  , optCryptolrc       = CryrcDefault
  , optCryptolPathOnly = False
  , optStopOnError     = False
  }

options :: [OptDescr (OptParser Options)]
options  =
  [ Option "b" ["batch"] (ReqArg setBatchScript "FILE")
    "run the script provided and exit"

  , Option "e" ["stop-on-error"] (NoArg setStopOnError)
    "stop script execution as soon as an error occurs."

  , Option "c" ["command"] (ReqArg addCommand "COMMAND")
    (concat [ "run the given command and then exit; if multiple --command "
            , "arguments are given, run them in the order they appear "
            , "on the command line (overrides --batch)"
            ])

  , Option "" ["color"] (ReqArg setColorMode "MODE")
    (concat [ "control the color output for the terminal, which may be "
            , "'auto', 'none' or 'always' (default: 'auto')"
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

-- | Stop script (batch mode) execution on first error.
setStopOnError :: OptParser Options
setStopOnError = modify $ \opts -> opts { optStopOnError = True }

-- | Set a batch script to be run.
setBatchScript :: String -> OptParser Options
setBatchScript path = modify $ \ opts -> opts { optBatch = Just path }

-- | Set the color mode of the terminal output.
setColorMode :: String -> OptParser Options
setColorMode "auto"   = modify $ \ opts -> opts { optColorMode = AutoColor }
setColorMode "none"   = modify $ \ opts -> opts { optColorMode = NoColor }
setColorMode "always" = modify $ \ opts -> opts { optColorMode = AlwaysColor }
setColorMode x        = OptFailure ["invalid color mode: " ++ x ++ "\n"]

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
          status <- repl (optCryptolrc opts')
                         (optBatch opts')
                         (optStopOnError opts')
                         (setupREPL opts')
          case mCleanup of
            Nothing -> return ()
            Just cmdFile -> removeFile cmdFile

          case status of
            CommandError -> exitFailure
            CommandOk    -> exitSuccess

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
        putStrLn "[warning] --command argument specified; ignoring batch file"
      return (opts { optBatch = Just path }, Just path)

setupREPL :: Options -> REPL ()
setupREPL opts = do
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
  smoke <- REPL.smokeTest
  case smoke of
    [] -> return ()
    _  -> io $ do
      print (hang "Errors encountered on startup; exiting:"
                4 (vcat (map pp smoke)))
      exitFailure

  color <- case optColorMode opts of
    AlwaysColor -> return True
    NoColor     -> return False
    AutoColor   -> canDisplayColor
  displayLogo color

  setUpdateREPLTitle (shouldSetREPLTitle >>= \b -> when b setREPLTitle)
  updateREPLTitle
  case optBatch opts of
    Nothing -> return ()
    -- add the directory containing the batch file to the module search path
    Just file -> prependSearchPath [ takeDirectory file ]
  case optLoad opts of
    []  -> loadPrelude `REPL.catch` \x -> io $ print $ pp x
    [l] -> loadCmd l `REPL.catch` \x -> do
             io $ print $ pp x
             -- If the requested file fails to load, load the prelude instead...
             loadPrelude `REPL.catch` \y -> do
               io $ print $ pp y
             -- ... but make sure the loaded module is set to the file
             -- we tried, instead of the Prelude
             REPL.setEditPath l
             REPL.setLoadedMod REPL.LoadedModule
               { REPL.lName = Nothing
               , REPL.lPath = InFile l
               }
    _   -> io $ putStrLn "Only one file may be loaded at the command line."
