-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
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

import qualified Control.Exception as X
import           Control.Monad (guard, when)
import qualified Control.Monad.IO.Class as MTL
import qualified Control.Monad.Trans.Class as MTL
import           Data.Char (isAlphaNum, isSpace)
import           Data.Function (on)
import           Data.List (isPrefixOf,nub,sortBy)
import           System.Console.ANSI (setTitle)
import           System.Console.Haskeline
import           System.Directory ( doesFileExist
                                  , getHomeDirectory
                                  , getCurrentDirectory)
import           System.FilePath ((</>))

-- | Haskeline-specific repl implementation.
repl :: Cryptolrc -> Maybe FilePath -> REPL () -> IO ()
repl cryrc mbBatch begin =
  do settings <- setHistoryFile (replSettings isBatch)
     runREPL isBatch (runInputTBehavior behavior settings body)
  where
  body = withInterrupt $ do
    MTL.lift evalCryptolrc
    MTL.lift begin
    loop

  (isBatch,behavior) = case mbBatch of
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

  evalCryptolrc =
    case cryrc of
      CryrcDefault -> do
        here <- io $ getCurrentDirectory
        home <- io $ getHomeDirectory
        let dcHere = here </> ".cryptolrc"
            dcHome = home </> ".cryptolrc"
        isHere <- io $ doesFileExist dcHere
        isHome <- io $ doesFileExist dcHome
        if | isHere    -> slurp dcHere
           | isHome    -> slurp dcHome
           | otherwise -> whenDebug $ io $ putStrLn "no .cryptolrc found"
      CryrcFiles paths -> mapM_ slurp paths
      CryrcDisabled -> return ()

  -- | Actually read the contents of a file, but don't save the
  -- history
  --
  -- XXX: friendlier error message would be nice if the file can't be
  -- found, but since these will be specified on the command line it
  -- should be obvious what's going wrong
  slurp path = do
    let settings' = defaultSettings { autoAddHistory = False }
    runInputTBehavior (useFile path) settings' (withInterrupt loop)


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

instance MTL.MonadIO REPL where
  liftIO = io

instance MonadException REPL where
  controlIO branchIO = REPL $ \ ref -> do
    runBody <- branchIO $ RunIO $ \ m -> do
      a <- unREPL m ref
      return (return a)
    unREPL runBody ref

-- Titles ----------------------------------------------------------------------

mkTitle :: Maybe LoadedModule -> String
mkTitle lm = maybe "" (\ m -> pretty m ++ " - ") (lName =<< lm)
          ++ "cryptol"

setREPLTitle :: REPL ()
setREPLTitle = do
  lm <- getLoadedMod
  io (setTitle (mkTitle lm))

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
