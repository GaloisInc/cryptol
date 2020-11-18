{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}

module Main(main) where

import Control.Monad.State
import Options.Applicative
import Data.Char (isSpace)
import Data.List (isInfixOf, stripPrefix)
import Data.Maybe (catMaybes, fromMaybe)
import qualified Data.Sequence as Seq
import Numeric.Natural
import qualified System.Process as P
import System.Directory
import System.Exit
import System.IO.Temp
import Data.Foldable (toList)

data Opts = Opts { latexFile :: FilePath
                 , cryptolExe :: Maybe FilePath
                 , tempDir :: Maybe FilePath
                 }
  deriving Show

optsParser :: Parser Opts
optsParser = Opts
  <$> strArgument (  help "path to latex file" )
  <*> ( optional $ strOption
        (  long "exe"
        <> short 'e'
        <> metavar "PATH"
        <> help "Path to cryptol executable (defaults to 'cabal v2-exec cryptol')"
        ) )
  <*> ( optional $ strOption
        (  long "log-dir"
        <> short 'l'
        <> metavar "PATH"
        <> help "Directory for log files in case of failure"
        ) )

trim :: String -> String
trim = f . f
   where f = reverse . dropWhile isSpace

data PMode = SearchingMode
           | ExerciseMode Natural (Seq.Seq Line)
           -- ^ Line of exercise, lines so far
           | ExerciseREPLMode Natural (Seq.Seq Line)
           -- ^ Line of exercise, lines so far
           | ExerciseDoneMode Natural (Seq.Seq Line)
           -- ^ Line of exercise, exercise lines
           | AnswerMode Natural (Seq.Seq Line) Natural (Seq.Seq Line)
           -- ^ Line of exercise, exercise lines, line of answer, answer lines so far
           | AnswerREPLMode Natural (Seq.Seq Line) Natural (Seq.Seq Line)
           -- ^ Line of exercise, exercise lines, line of answer, answer lines so far
  deriving (Eq, Show)

data Line = Line { lineNum :: Natural
                 , lineText :: String
                 }
  deriving (Eq, Show)

data Exercise = Exercise { exerciseLineNum :: Natural
                         , exerciseLines :: Seq.Seq Line
                         , answerLineNum :: Natural
                         , answerLines :: Seq.Seq Line
                         }
  deriving (Eq, Show)

data PState = PState { pMode        :: PMode
                     , pExercises   :: Seq.Seq Exercise
                     , pCurrentLine :: Natural
                     }
  deriving (Eq, Show)

initPState :: PState
initPState = PState SearchingMode Seq.Empty 1

type P = StateT PState IO

first :: (a -> a') -> (a, b) -> (a', b)
first f (a, b) = (f a, b)

-- | Like 'stripInfix' from the `extra` package, but the caller supplies a list
-- of lists that could be interpreted as infix separators. The first one
-- supplied that matches is used.
stripInfixOneOf :: Eq a => [[a]] -> [a] -> Maybe ([a], [a])
stripInfixOneOf needles haystack
  | suffixes <- catMaybes (flip stripPrefix haystack <$> needles)
  , (rest : _) <- suffixes = Just ([], rest)
stripInfixOneOf _ [] = Nothing
stripInfixOneOf needles (x:xs) = first (x:) <$> stripInfixOneOf needles xs

inlineRepls :: String -> [String]
inlineRepls s
  | Just (_, s1) <- stripInfixOneOf ["\\repl{","\\hiderepl{"] s
  , (s2, s3) <- break (=='}') s1 = s2 : inlineRepls s3
  | otherwise = []

processLine :: String -> P ()
processLine (trim -> s) = do
  -- We remove all whitespace in s, but this is only to normalize s for
  -- detecting state changes. We don't want to use s' when recording actual
  -- lines of REPL commands because it will squish everything together.
  let s' = filter (not . isSpace) s
  m <- gets pMode
  ln <- gets pCurrentLine
  case m of
    SearchingMode
      | "\\begin{Exercise}" `isInfixOf` s' ->
        modify' $ \st -> st { pMode = ExerciseMode ln Seq.empty}
      | otherwise -> return ()
    ExerciseMode eln elines
      | "\\end{Exercise}" `isInfixOf` s' ->
        modify $ \st -> st { pMode = ExerciseDoneMode eln elines}
      | "\\begin{REPL}" `isInfixOf` s' ->
        modify' $ \st -> st { pMode = ExerciseREPLMode eln elines}
      | otherwise -> do
          let rs = Line ln <$> Seq.fromList (inlineRepls s)
              elines' = elines Seq.>< rs
          modify' $ \st -> st { pMode = ExerciseMode eln elines' }
    ExerciseREPLMode eln elines
      | "\\end{REPL}" `isInfixOf` s' ->
        modify' $ \st -> st { pMode = ExerciseMode eln elines }
      | otherwise ->
        modify' $ \st -> st { pMode = ExerciseREPLMode eln (elines Seq.|> Line ln s) }
    ExerciseDoneMode eln elines
      | "\\begin{Exercise}" `isInfixOf` s' ->
        modify' $ \st -> st { pMode = ExerciseMode ln Seq.empty }
      | "\\begin{Answer}" `isInfixOf` s' ->
        modify' $ \st -> st { pMode = AnswerMode eln elines ln Seq.Empty }
      | otherwise -> return ()
    AnswerMode eln elines aln alines
      | "\\end{Answer}" `isInfixOf` s' -> do
          let exercise = Exercise eln elines aln alines
          modify $ \st -> st { pExercises = pExercises st Seq.|> exercise
                             , pMode = SearchingMode }
      | "\\begin{REPL}" `isInfixOf` s' ->
        modify' $ \st -> st { pMode = AnswerREPLMode eln elines aln alines}
      | otherwise -> do
          let rs = Line ln <$> Seq.fromList (inlineRepls s)
              alines' = alines Seq.>< rs
          modify' $ \st -> st { pMode = AnswerMode eln elines aln alines' }
    AnswerREPLMode eln elines aln alines
      | "\\end{REPL}" `isInfixOf` s' ->
        modify' $ \st -> st { pMode = AnswerMode eln elines aln alines }
      | otherwise ->
        modify' $ \st ->
          st { pMode = AnswerREPLMode eln elines aln (alines Seq.|> Line ln s) }

  modify' $ \st -> st { pCurrentLine = pCurrentLine st + 1 }

main :: IO ()
main = do
  opts <- execParser p
  allLines <- lines <$> readFile (latexFile opts)
  PState {..} <- flip execStateT initPState $ forM allLines processLine
  let exercises = filter (not . null . exerciseLines) (toList pExercises)
      dir = fromMaybe "." (tempDir opts)

  forM_ exercises $ \ex -> do
    let exText = unlines $ fmap lineText $ toList $ exerciseLines ex
        exFileNameTemplate = "ex-" ++ show (exerciseLineNum ex) ++ "-in.icry"
        ansText = unlines $ fmap lineText $ toList $ answerLines ex
        ansFileNameTemplate = "ex-" ++ show (answerLineNum ex) ++ "-out-expected.icry"
        outFileNameTemplate = "ex-" ++ show (answerLineNum ex) ++ "-out.icry"
    exFile <- writeTempFile dir exFileNameTemplate exText
    ansFile <- writeTempFile dir ansFileNameTemplate ansText
    outFile <- emptyTempFile dir outFileNameTemplate

    let exe = fromMaybe "./cry run" (cryptolExe opts)
        cmd = (P.shell (exe ++ " -b " ++ exFile))

    cmdOut <- P.readCreateProcess cmd ""

    let outText = unlines $ filter (not . null) $ trim <$> (tail $ lines cmdOut)

    writeFile outFile outText

    let diffCmd = (P.shell ("diff " ++ ansFile ++ " " ++ outFile))

    (diffEC, diffOut, _) <- P.readCreateProcessWithExitCode diffCmd ""
    case diffEC of
      ExitSuccess -> do
        -- Remove temporary files
        removeFile exFile
        removeFile ansFile
        removeFile outFile
      ExitFailure _ -> do
        putStrLn $ "Exercise mismatch:"
        putStrLn $ "  Exercise line: " ++ show (exerciseLineNum ex)
        putStrLn $ "  Answer line: " ++ show (answerLineNum ex)
        putStrLn $ "Diff output:"
        putStr diffOut

        let ansFileName = dir ++ "/" ++ ansFileNameTemplate
            outFileName = dir ++ "/" ++ outFileNameTemplate

        putStrLn ""
        putStrLn $ "Expected output written to: " ++ ansFileName
        putStrLn $ "Actual output written to: " ++ outFileName

        -- Write to log files
        writeFile ansFileName ansText
        writeFile outFileName outText

        -- Remove temporary files and exit
        removeFile exFile
        removeFile ansFile
        removeFile outFile
        exitFailure

  putStrLn $ "Successfully checked " ++ show (length exercises) ++ " exercises."

  where p = info (optsParser <**> helper)
            ( fullDesc
              <> progDesc "Test the exercises in a cryptol LaTeX file"
              <> header "check-exercises -- test cryptol exercises"
            )
