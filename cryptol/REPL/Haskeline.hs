-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE PatternGuards #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module REPL.Haskeline where

import REPL.Command
import REPL.Monad
import REPL.Trie

import Control.Monad (guard, when)
import Data.Char (isAlphaNum, isSpace)
import Data.Function (on)
import Data.List (isPrefixOf,nub,sortBy)
import System.Console.Haskeline
import System.Directory(getAppUserDataDirectory,createDirectoryIfMissing)
import System.FilePath((</>))
import qualified Control.Monad.IO.Class as MTL
import qualified Control.Monad.Trans.Class as MTL
import qualified Control.Exception as X


-- | Haskeline-specific repl implementation.
--
-- XXX this needs to handle Ctrl-C, which at the moment will just cause
-- haskeline to exit.  See the function 'withInterrupt' for more info on how to
-- handle this.
repl :: Maybe FilePath -> REPL () -> IO ()
repl mbBatch begin =
  do settings <- setHistoryFile replSettings
     runREPL isBatch (runInputTBehavior style settings body)
  where
  body = withInterrupt $ do
    MTL.lift begin
    loop

  (isBatch,style) = case mbBatch of
    Nothing   -> (False,defaultBehavior)
    Just path -> (True,useFile path)

  loop = do
    prompt <- MTL.lift getPrompt
    mb     <- handleInterrupt (return (Just "")) (getInputLines prompt [])
    case mb of

      Just line
        | Just cmd <- parseCommand findCommandExact line -> do
          continue <- MTL.lift $ do
            handleInterrupt handleCtrlC (runCommand cmd)
            shouldContinue
          when continue loop

        | otherwise -> loop

      Nothing -> return ()

  getInputLines prompt ls =
    do mb <- getInputLine prompt
       let newPropmpt = map (\_ -> ' ') prompt
       case mb of
          Nothing -> return Nothing
          Just l | not (null l) && last l == '\\' ->
                                      getInputLines newPropmpt (init l : ls)
                 | otherwise -> return $ Just $ unlines $ reverse $ l : ls



-- | Try to set the history file.
setHistoryFile :: Settings REPL -> IO (Settings REPL)
setHistoryFile ss =
  do dir <- getAppUserDataDirectory "cryptol"
     createDirectoryIfMissing True dir
     return ss { historyFile = Just (dir </> "history") }
   `X.catch` \(SomeException {}) -> return ss

-- | Haskeline settings for the REPL.
replSettings :: Settings REPL
replSettings  = Settings
  { complete       = cryptolCommand
  , historyFile    = Nothing
  , autoAddHistory = True
  }


-- Utilities -------------------------------------------------------------------

instance MTL.MonadIO REPL where
  liftIO = io

instance MonadException REPL where
  controlIO branchIO = REPL $ \ ref -> do
    runBody <- branchIO $ RunIO $ \ m -> do
      a <- unREPL m ref
      return (return a)
    unREPL runBody ref


-- Completion ------------------------------------------------------------------

-- | Completion for cryptol commands.
cryptolCommand :: CompletionFunc REPL
cryptolCommand cursor@(l,r)
  | ":" `isPrefixOf` l'
  , Just (cmd,rest) <- splitCommand l' = case nub (findCommand cmd) of

      [c] | null rest && not (any isSpace l') -> do
            return (l, cmdComp cmd c)
          | otherwise -> do
            (rest',cs) <- cmdArgument (cBody c) (reverse (sanitize rest),r)
            return (unwords [rest', reverse cmd],cs)

      cmds ->
        return (l, concat [ cmdComp l' c | c <- cmds ])
  -- Complete all : commands when the line is just a :
  | ":" == l' = return (l, concat [ cmdComp l' c | c <- nub (findCommand ":") ])
  | otherwise = completeExpr cursor
  where
  l' = sanitize (reverse l)

-- | Generate completions from a REPL command definition.
cmdComp :: String -> CommandDescr -> [Completion]
cmdComp prefix c = do
  cName <- cNames c
  guard (prefix `isPrefixOf` cName)
  return $ Completion
    { replacement = drop (length prefix) cName
    , display     = cName
    , isFinished  = True
    }

-- | Dispatch to a completion function based on the kind of completion the
-- command is expecting.
cmdArgument :: CommandBody -> CompletionFunc REPL
cmdArgument ct cursor@(l,_) = case ct of
  ExprArg     _ -> completeExpr cursor
  DeclsArg    _ -> (completeExpr +++ completeType) cursor
  ExprTypeArg _ -> (completeExpr +++ completeType) cursor
  FilenameArg _ -> completeFilename cursor
  ShellArg _    -> completeFilename cursor
  OptionArg _   -> completeOption cursor
  NoArg       _ -> return (l,[])

-- | Complete a name from the expression environment.
completeExpr :: CompletionFunc REPL
completeExpr (l,_) = do
  ns <- getExprNames
  let n    = reverse (takeWhile isIdentChar l)
      vars = filter (n `isPrefixOf`) ns
  return (l,map (nameComp n) vars)

-- | Complete a name from the type synonym environment.
completeType :: CompletionFunc REPL
completeType (l,_) = do
  ns <- getTypeNames
  let n    = reverse (takeWhile isIdentChar l)
      vars = filter (n `isPrefixOf`) ns
  return (l,map (nameComp n) vars)

-- | Generate a completion from a prefix and a name.
nameComp :: String -> String -> Completion
nameComp prefix c = Completion
  { replacement = drop (length prefix) c
  , display     = c
  , isFinished  = True
  }

isIdentChar :: Char -> Bool
isIdentChar c = isAlphaNum c || c `elem` "_\'"

-- | Join two completion functions together, merging and sorting their results.
(+++) :: CompletionFunc REPL -> CompletionFunc REPL -> CompletionFunc REPL
(as +++ bs) cursor = do
  (_,acs) <- as cursor
  (_,bcs) <- bs cursor
  return (fst cursor, sortBy (compare `on` replacement) (acs ++ bcs))


-- | Complete an option from the options environment.
--
-- XXX this can do better, as it has access to the expected form of the value
completeOption :: CompletionFunc REPL
completeOption cursor@(l,_) = return (fst cursor, map comp opts)
  where
  n        = reverse l
  opts     = lookupTrie n userOptions
  comp opt = Completion
    { replacement = drop (length n) (optName opt)
    , display     = optName opt
    , isFinished  = False
    }
