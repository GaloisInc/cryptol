-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

module Main where

import Notebook

import Cryptol.REPL.Command
import Cryptol.REPL.Monad (lName, lPath)
import qualified Cryptol.REPL.Monad as REPL

import qualified Cryptol.ModuleSystem as M
import qualified Cryptol.ModuleSystem.Monad as M (setFocusedModule)
import Cryptol.Parser (defaultConfig, parseModule, Config(..))
import qualified Cryptol.Parser.AST as P
import qualified Cryptol.TypeCheck.AST as T
import Cryptol.Utils.PP (pp, pretty)

import Control.Applicative ((<$>))
import qualified Control.Exception as X
import Control.Monad (forever, forM_)

import qualified Data.Text as T

import IHaskell.IPython.Kernel
import IHaskell.IPython.EasyKernel (easyKernel, KernelConfig(..))

import System.Environment (getArgs)
import System.IO (hFlush, stdout)

import Debug.Trace

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["kernel", profileFile] ->
      runNB $ do
        liftREPL loadPrelude `catch` \x -> io $ print $ pp x
        easyKernel profileFile cryptolConfig
    _ -> do
      putStrLn "Usage:"
      putStrLn "icryptol-kernel kernel FILE  -- run a kernel with FILE for \
               \communication with the frontend"

-- Kernel Configuration --------------------------------------------------------
cryptolConfig :: KernelConfig NB String String
cryptolConfig = KernelConfig
  { languageName = "cryptol"
  , languageVersion = [0,0,1]
  , profileSource = return Nothing
  , displayResult = displayRes
  , displayOutput = displayOut
  , completion = compl
  , objectInfo = info
  , run = runCell
  , debug = False
  }
  where
    displayRes str = [ DisplayData MimeHtml . T.pack $ str
                     , DisplayData PlainText . T.pack $ str
                     ]
    displayOut str = [ DisplayData PlainText . T.pack $ str ]
    compl _ _ _    = Nothing
    info _         = Nothing
    runCell contents clear nbPutStr = do
      putStrOrig <- liftREPL REPL.getPutStr
      liftREPL $ REPL.setPutStr nbPutStr
      let go = do
            handleAuto (T.unpack contents)
            return ("", Ok)
          handle exn =
            return (pretty exn, Err)
      (result, status) <- catch go handle
      liftREPL $ REPL.setPutStr putStrOrig
      return (result, status, "")

-- Input Handling --------------------------------------------------------------

-- | Determine whether the input is a module fragment or a series of
-- interactive commands, and behave accordingly.
handleAuto :: String -> NB ()
handleAuto str = do
  let cfg = defaultConfig { cfgSource = "<notebook>" }
      cmdParses cmd =
        case parseCommand (findNbCommand False) cmd of
          Just (Unknown _)     -> False
          Just (Ambiguous _ _) -> False
          _                    -> True
  case parseModule cfg str of
    Right m -> handleModFrag m
    Left modExn -> do
      let cmds = lines str
      if and (map cmdParses cmds)
         then forM_ cmds handleCmd
         else raise (AutoParseError modExn)

parseModFrag :: String -> NB P.Module
parseModFrag str = liftREPL $ replParse (parseModule cfg) str
  where cfg = defaultConfig { cfgSource = "<notebook>" }

-- | Read a module fragment and incorporate it into the current context.
handleModFrag :: P.Module -> NB ()
handleModFrag m = do
  let m' = removeIncludes $ removeImports m
  old <- getTopDecls
  
  let new = modNamedDecls m'
      merged = updateNamedDecls old new
      doLoad = try $ liftREPL $ liftModuleCmd (M.loadModule "<notebook>" (moduleFromDecls nbName merged))
  em'' <- doLoad
  -- only update the top decls if the module successfully loaded
  case em'' of
    Left exn -> raise exn
    Right m'' -> do
      setTopDecls merged
      liftREPL $ REPL.setLoadedMod REPL.LoadedModule
                   { lName = Just (T.mName m'')
                   , lPath = "<notebook>"
                   }

readUntil :: (String -> Bool) -> NB String
readUntil shouldStop = unlines . reverse <$> go []
  where go xs = do
          line <- io getLine
          if shouldStop line
             then return xs
             else go (line : xs)

-- | Treat a line as an interactive command.
handleCmd :: String -> NB ()
handleCmd line =
    case parseCommand (findNbCommand False) line of
      Nothing -> return ()
      Just cmd -> do
        mod <- (liftREPL (REPL.getLoadedMod))
        liftREPL $ runCommand cmd
