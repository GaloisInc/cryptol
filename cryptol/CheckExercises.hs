{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}

module Main(main) where

import Control.Monad.State
import Options.Applicative
import Data.Char (isSpace)
import Data.List (isInfixOf)
import Data.Maybe (catMaybes)
import qualified Data.Sequence as Seq
import Numeric.Natural
import System.Process
import Data.Foldable (toList)

data Opts = Opts { latexFile :: FilePath }
  deriving Show

optsParser :: Parser Opts
optsParser = Opts
  <$> strArgument (help "path to latex file")

trim :: String -> String
trim = f . f
   where f = reverse . dropWhile isSpace

data ExerciseError = ExerciseError
  { expectedOutputLine :: Natural
  , expectedOutput :: String
  , actualOutput :: String
  }

data PMode = None | Exercise | Answer
  deriving (Eq, Show)

data PREPLMode = REPL | NoREPL
  deriving (Eq, Show)

data Line = Line { lineNum :: Natural
                 , lineText :: String
                 }
  deriving (Eq, Show)

data PState = PState { pMode          :: PMode
                     , pREPLMode      :: PREPLMode
                     , pExerciseLines :: Seq.Seq Line
                     , pAnswerLines   :: Seq.Seq Line
                     , pCurrentLine   :: Natural
                     }
  deriving (Eq, Show)

initPState :: PState
initPState = PState None NoREPL Seq.Empty Seq.Empty 1

type P = StateT PState IO

processLine :: String -> P ()
processLine (trim -> s) = do
  let s' = filter (not . isSpace) s
  m <- gets pMode
  repl <- gets pREPLMode
  ln <- gets pCurrentLine
  case (m, repl) of
    (None, REPL) -> error $
      show ln ++ ": encountered \begin{REPL} outside of exercise or answer"
    (None, NoREPL)
      | "\\begin{Exercise}" `isInfixOf` s' ->
        modify' $ \st -> st {pMode = Exercise }
      | "\\begin{Answer}" `isInfixOf` s' ->
        modify' $ \st -> st {pMode = Answer }
    (Exercise, NoREPL)
      | "\\end{Exercise}" `isInfixOf` s' ->
        modify $ \st -> st { pMode = None }
      | "\\begin{REPL}" `isInfixOf` s' ->
        modify' $ \st -> st { pREPLMode = REPL}
    (Answer, NoREPL)
      | "\\end{Answer}" `isInfixOf` s' ->
        modify $ \st -> st { pMode = None }
      | "\\begin{REPL}" `isInfixOf` s' ->
        modify' $ \st -> st { pREPLMode = REPL}
    (Exercise, REPL)
      | "\\end{REPL}" `isInfixOf` s' ->
        modify' $ \st -> st { pREPLMode = NoREPL }
      | otherwise ->
        modify' $ \st -> st { pExerciseLines = pExerciseLines st Seq.:|> Line ln s }
    (Answer, REPL)
      | "\\end{REPL}" `isInfixOf` s' ->
        modify' $ \st -> st { pREPLMode = NoREPL }
      | otherwise ->
        modify' $ \st -> st { pAnswerLines = pAnswerLines st Seq.:|> Line ln s }
    _ -> return ()

  modify' $ \st -> st { pCurrentLine = pCurrentLine st + 1 }

main :: IO ()
main = do
  opts <- execParser p
  allLines <- lines <$> readFile (latexFile opts)
  PState {..} <- flip execStateT initPState $ forM allLines processLine
  let args = concatMap (\i -> "-c \"" ++ i ++ "\" ") (lineText <$> pExerciseLines)
      cmd = "cabal v2-exec cryptol -- " ++ args
  (_, out, _) <- readCreateProcessWithExitCode (shell cmd) ""
  let outLines = trim <$> (tail $ lines out)
      checkLine actualOutput (Line expectedOutputLine expectedOutput) =
        if actualOutput == expectedOutput
        then Nothing
        else Just $ ExerciseError {..}
      errs = catMaybes $ zipWith checkLine outLines (toList pAnswerLines)
  case errs of
    [] -> putStrLn $ "Exercises validated! (" ++ show (length pExerciseLines) ++ ")"
    _ -> forM_ errs $ \(ExerciseError {..}) -> do
      putStrLn $ "Exercise mismatch."
      putStrLn $ "  Expected output (line " ++ show expectedOutputLine ++
        "): " ++ expectedOutput
      putStrLn $ "  Actual output: " ++ actualOutput
  where p = info (optsParser <**> helper)
            ( fullDesc
              <> progDesc "Test the exercises in a cryptol LaTeX file"
              <> header "check-exercises -- test cryptol exercises"
            )
