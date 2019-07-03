-- |
-- Module      :  REPL.Haskeline
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternGuards #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module REPL.Haskeline where

import           Cryptol.REPL.Command
import           Cryptol.REPL.Monad
import           Cryptol.REPL.Trie
import           Cryptol.Utils.PP
import           Cryptol.Utils.Logger(stdoutLogger)
import           Cryptol.Utils.Ident(modNameToText, interactiveName)

import qualified Control.Exception as X
import           Control.Monad (guard, join)
import qualified Control.Monad.Trans.Class as MTL
import           Control.Monad.Trans.Control
import           Data.Char (isAlphaNum, isSpace)
import           Data.Maybe(isJust)
import           Data.Function (on)
import           Data.List (isPrefixOf,nub,sortBy,sort)
import qualified Data.Set as Set
import qualified Data.Text as T (unpack)
import           System.IO (stdout)
import           System.Console.ANSI (setTitle, hSupportsANSI)
import           System.Console.Haskeline
import           System.Directory ( doesFileExist
                                  , getHomeDirectory
                                  , getCurrentDirectory)
import           System.FilePath ((</>))

import           Prelude ()
import           Prelude.Compat


-- | One REPL invocation, either from a file or from the terminal.
crySession :: Maybe FilePath -> Bool -> REPL CommandExitCode
crySession mbBatch stopOnError =
  do settings <- io (setHistoryFile (replSettings isBatch))
     let act = runInputTBehavior behavior settings (withInterrupt loop)
     if isBatch then asBatch act else act
  where
  (isBatch,behavior) = case mbBatch of
    Nothing   -> (False,defaultBehavior)
    Just path -> (True,useFile path)

  loop :: InputT REPL CommandExitCode
  loop =
    do ln <- getInputLines =<< MTL.lift getPrompt
       case ln of
         NoMoreLines -> return CommandOk
         Interrupted
           | isBatch && stopOnError -> return CommandError
           | otherwise -> loop
         NextLine line
           | all isSpace line -> loop
           | otherwise        -> doCommand line

  doCommand txt =
    case parseCommand findCommandExact txt of
      Nothing | isBatch && stopOnError  -> return CommandError
              | otherwise -> loop -- say somtething?
      Just cmd -> join $ MTL.lift $
        do status <- handleInterrupt (handleCtrlC CommandError) (runCommand cmd)
           case status of
             CommandError | isBatch && stopOnError -> return (return status)
             _ -> do goOn <- shouldContinue
                     return (if goOn then loop else return status)


data NextLine = NextLine String | NoMoreLines | Interrupted

getInputLines :: String -> InputT REPL NextLine
getInputLines = handleInterrupt (MTL.lift (handleCtrlC Interrupted)) . loop []
  where
  loop ls prompt =
    do mb <- getInputLine prompt
       let newPropmpt = map (\_ -> ' ') prompt
       case mb of
         Nothing -> return NoMoreLines
         Just l
           | not (null l) && last l == '\\' -> loop (init l : ls) newPropmpt
           | otherwise -> return $ NextLine $ unlines $ reverse $ l : ls

loadCryRC :: Cryptolrc -> REPL CommandExitCode
loadCryRC cryrc =
  case cryrc of
    CryrcDisabled   -> return CommandOk
    CryrcDefault    -> check [ getCurrentDirectory, getHomeDirectory ]
    CryrcFiles opts -> loadMany opts
  where
  check [] = return CommandOk
  check (place : others) =
    do dir <- io place
       let file = dir </> ".cryptolrc"
       present <- io (doesFileExist file)
       if present
         then crySession (Just file) True
         else check others

  loadMany []       = return CommandOk
  loadMany (f : fs) = do status <- crySession (Just f) True
                         case status of
                           CommandOk -> loadMany fs
                           _         -> return status

-- | Haskeline-specific repl implementation.
repl :: Cryptolrc -> Maybe FilePath -> Bool -> REPL () -> IO CommandExitCode
repl cryrc mbBatch stopOnError begin =
  runREPL (isJust mbBatch) stdoutLogger $
  do status <- loadCryRC cryrc
     case status of
       CommandOk -> begin >> crySession mbBatch stopOnError
       _         -> return status



-- | Try to set the history file.
setHistoryFile :: Settings REPL -> IO (Settings REPL)
setHistoryFile ss =
  do dir <- getHomeDirectory
     return ss { historyFile = Just (dir </> ".cryptol_history") }
   `X.catch` \(SomeException {}) -> return ss

-- | Haskeline settings for the REPL.
replSettings :: Bool -> Settings REPL
replSettings isBatch = Settings
  { complete       = cryptolCommand
  , historyFile    = Nothing
  , autoAddHistory = not isBatch
  }

-- .cryptolrc ------------------------------------------------------------------

-- | Configuration of @.cryptolrc@ file behavior. The default option
-- searches the following locations in order, and evaluates the first
-- file that exists in batch mode on interpreter startup:
--
-- 1. $PWD/.cryptolrc
-- 2. $HOME/.cryptolrc
--
-- If files are specified, they will all be evaluated, but none of the
-- default files will be (unless they are explicitly specified).
--
-- The disabled option inhibits any reading of any .cryptolrc files.
data Cryptolrc =
    CryrcDefault
  | CryrcDisabled
  | CryrcFiles [FilePath]
  deriving (Show)

-- Utilities -------------------------------------------------------------------

instance MonadException REPL where
  controlIO f = join $ liftBaseWith $ \f' ->
    f $ RunIO $ \m -> restoreM <$> (f' m)

-- Titles ----------------------------------------------------------------------

mkTitle :: Maybe LoadedModule -> String
mkTitle lm = maybe "" (\ m -> pretty m ++ " - ") (lName =<< lm)
          ++ "cryptol"

setREPLTitle :: REPL ()
setREPLTitle = do
  lm <- getLoadedMod
  io (setTitle (mkTitle lm))

-- | In certain environments like Emacs, we shouldn't set the terminal
-- title. Note: this does not imply we can't use color output. We can
-- use ANSI color sequences in places like Emacs, but not terminal
-- codes.
--
-- This checks that @'stdout'@ is a proper terminal handle, and that the
-- terminal mode is not @dumb@, which is set by Emacs and others.
shouldSetREPLTitle :: REPL Bool
shouldSetREPLTitle = io (hSupportsANSI stdout)

-- | Whether we can display color titles. This checks that @'stdout'@
-- is a proper terminal handle, and that the terminal mode is not
-- @dumb@, which is set by Emacs and others.
canDisplayColor :: REPL Bool
canDisplayColor = io (hSupportsANSI stdout)

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
  return $ nameComp prefix cName

-- | Dispatch to a completion function based on the kind of completion the
-- command is expecting.
cmdArgument :: CommandBody -> CompletionFunc REPL
cmdArgument ct cursor@(l,_) = case ct of
  ExprArg     _ -> completeExpr cursor
  DeclsArg    _ -> (completeExpr +++ completeType) cursor
  ExprTypeArg _ -> (completeExpr +++ completeType) cursor
  ModNameArg _  -> completeModName cursor
  FilenameArg _ -> completeFilename cursor
  ShellArg _    -> completeFilename cursor
  OptionArg _   -> completeOption cursor
  HelpArg     _ -> completeHelp cursor
  NoArg       _ -> return (l,[])
  FileExprArg _ -> completeExpr cursor

-- | Additional keywords to suggest in the REPL
--   autocompletion list.
keywords :: [String]
keywords =
  [ "else"
  , "if"
  , "let"
  , "then"
  , "where"
  ]

-- | Complete a name from the expression environment.
completeExpr :: CompletionFunc REPL
completeExpr (l,_) = do
  ns <- (keywords++) <$> getExprNames
  let n    = reverse (takeIdent l)
      vars = sort $ filter (n `isPrefixOf`) ns
  return (l,map (nameComp n) vars)

-- | Complete a name from the type synonym environment.
completeType :: CompletionFunc REPL
completeType (l,_) = do
  ns <- getTypeNames
  let n    = reverse (takeIdent l)
      vars = filter (n `isPrefixOf`) ns
  return (l,map (nameComp n) vars)

-- | Complete a name for which we can show REPL help documentation.
completeHelp :: CompletionFunc REPL
completeHelp (l, _) = do
  ns1 <- getExprNames
  ns2 <- getTypeNames
  let ns3 = concatMap cNames (nub (findCommand ":"))
  let ns = Set.toAscList (Set.fromList (ns1 ++ ns2)) ++ ns3
  let n    = reverse l
  case break isSpace n of
    (":set", _ : n') ->
      do let n'' = dropWhile isSpace n'
         let vars = map optName (lookupTrie (dropWhile isSpace n') userOptions)
         return (l, map (nameComp n'') vars)
    _                ->
      do let vars = filter (n `isPrefixOf`) ns
         return (l, map (nameComp n) vars)


-- | Complete a name from the list of loaded modules.
completeModName :: CompletionFunc REPL
completeModName (l, _) = do
  ms <- getModNames
  let ns   = map (T.unpack . modNameToText) (interactiveName : ms)
      n    = reverse (takeWhile (not . isSpace) l)
      vars = filter (n `isPrefixOf`) ns
  return (l, map (nameComp n) vars)

-- | Generate a completion from a prefix and a name.
nameComp :: String -> String -> Completion
nameComp prefix c = Completion
  { replacement = drop (length prefix) c
  , display     = c
  , isFinished  = True
  }

-- | Return longest identifier (possibly a qualified name) that is a
-- prefix of the given string
takeIdent :: String -> String
takeIdent (c : cs) | isIdentChar c = c : takeIdent cs
takeIdent (':' : ':' : cs) = ':' : ':' : takeIdent cs
takeIdent _ = []

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
