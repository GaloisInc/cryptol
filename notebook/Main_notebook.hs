-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

module Main where

import Notebook

import REPL.Command
import REPL.Monad (lName, lPath)
import qualified REPL.Monad as REPL

import qualified Cryptol.ModuleSystem as M
import Cryptol.Parser (defaultConfig, parseModule, Config(..))
import qualified Cryptol.Parser.AST as P
import qualified Cryptol.TypeCheck.AST as T
import Cryptol.Utils.PP (pp)

import Control.Applicative ((<$>))
import Control.Monad (forever, forM_)
import System.IO (hFlush, stdout)

main :: IO ()
main = runNB $ do
  liftREPL loadPrelude `catch` \x -> io $ print $ pp x
  io $ putStr "<READY>" >> hFlush stdout
  let loop = do
        line <- io getLine
        runExns $ case line of
          "<BEGINMOD>" ->
            handleModFrag =<< parseModFrag =<< readUntil (== "<ENDMOD>")
          "<BEGINAUTO>" ->
            handleAuto =<< readUntil (== "<ENDAUTO>")
          _ ->
            handleCmd line
        io $ putStr "<DONE>" >> hFlush stdout
  forever loop

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
        liftREPL $ runCommand cmd
