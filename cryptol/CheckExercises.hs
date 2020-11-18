{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}

module Main(main) where

import Control.Monad.State
import Options.Applicative
import Data.Char (isSpace)
import Data.Foldable (traverse_)
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
  <$> strArgument (  help "path to latex file"
                  <> metavar "PATH"
                  )
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

data PMode = AwaitingReplinMode
           | ReplinMode
           | AwaitingReploutMode
           | ReploutMode
  deriving (Eq, Show)

data Line = Line { lineNum :: Natural
                 , lineText :: String
                 }
  deriving (Eq, Show)

-- | REPL input and expected output, with line number annotations.
data ReplData = ReplData { rdReplin  :: Seq.Seq Line
                         , rdReplout :: Seq.Seq Line
                         }
  deriving (Eq, Show)

-- | State for the state monad
data PState = PState { pMode              :: PMode
                     , pCompletedReplData :: Seq.Seq ReplData
                     , pReplin            :: Seq.Seq Line
                     , pReplout           :: Seq.Seq Line
                     , pCurrentLine       :: Natural
                     }
  deriving (Eq, Show)

initPState :: PState
initPState = PState AwaitingReplinMode Seq.empty Seq.empty Seq.empty 1

type P = StateT PState IO

addReplData :: P ()
addReplData = do
  replin <- gets pReplin
  replout <- gets pReplout
  completedReplData <- gets pCompletedReplData
  let completedReplData' = completedReplData Seq.|> ReplData replin replout
  when (not (Seq.null replin && Seq.null replout)) $
    modify' $ \st -> st { pCompletedReplData = completedReplData'
                        , pReplin = Seq.empty
                        , pReplout = Seq.empty
                        }

addReplin :: String -> P ()
addReplin s = do
  ln <- gets pCurrentLine
  replin <- gets pReplin
  modify' $ \st -> st { pReplin = replin Seq.|> Line ln s }

addReplout :: String -> P ()
addReplout s = do
  ln <- gets pCurrentLine
  replout <- gets pReplout
  modify' $ \st -> st { pReplout = replout Seq.|> Line ln s }

first3  :: (a -> a') -> (a, b, c) -> (a', b, c)
first3 f (a, b, c) = (f a, b, c)

-- | Like 'stripPrefix', but takes a list of prefixes rather than a single
-- prefix. Returns the first prefix that matches the start of the list along
-- with the remainder of the list.
stripPrefixOneOf :: Eq a => [[a]] -> [a] -> Maybe ([a], [a])
stripPrefixOneOf [] _ = Nothing
stripPrefixOneOf (p:ps) as = case stripPrefix p as of
  Nothing -> stripPrefixOneOf ps as
  Just as' -> Just (p, as')

-- | Like 'stripInfix', but takes a list of infixes. Returns the infix that
-- matches at the earliest index.
stripInfixOneOf :: Eq a => [[a]] -> [a] -> Maybe ([a], [a], [a])
stripInfixOneOf needles haystack
  | Just (needle, suffix) <- stripPrefixOneOf needles haystack
  = Just ([], needle, suffix)
stripInfixOneOf _ [] = Nothing
stripInfixOneOf needles (x:xs) = first3 (x:) <$> stripInfixOneOf needles xs

-- inlineRepls :: String -> [String]
-- inlineRepls s
--   | Just (_, s1) <- stripInfixOneOf ["\\replin{","\\hidereplin{"] s
--   , (s2, s3) <- break (=='}') s1 = s2 : inlineRepls s3
--   | otherwise = []

data InlineRepl = InlineReplin | InlineReplout

-- | Extracts the first inline repl command returns the type of command, its
-- contents, and the remainder of the string.
inlineRepl :: String -> Maybe (InlineRepl, String, String)
inlineRepl s
  | Just (_, ir, s1) <- stripInfixOneOf [ "\\replin{"
                                        , "\\hidereplin{"
                                        , "\\replout{"
                                        , "\\hidereplout{"] s
  , (s2, s3) <- break (=='}') s1 = case ir of
      "\\replin{" -> Just (InlineReplin, s2, s3)
      "\\hidereplin{" -> Just (InlineReplin, s2, s3)
      "\\replout{" -> Just (InlineReplout, s2, s3)
      "\\hidereplout{" -> Just (InlineReplout, s2, s3)
      _ -> error "PANIC: CheckExercises.inlineRepl"
  | otherwise = Nothing

processLine :: String -> P ()
processLine (trim -> s) = do
  -- We remove all whitespace in s, but this is only to normalize s for
  -- detecting state changes. We don't want to use s' when recording actual
  -- lines of REPL commands because it will squish everything together.
  let s' = filter (not . isSpace) s
  m <- gets pMode
  ln <- gets pCurrentLine
  case m of
    AwaitingReplinMode
      | "\\begin{replinVerb}" `isInfixOf` s' -> do
          -- Switching from awaiting to ingesting repl input.
          modify' $ \st -> st { pMode = ReplinMode }
      | "\\begin{reploutVerb}" `isInfixOf` s' ->
          -- Switching from awaiting repl input to ingesting repl output.
          modify' $ \st -> st { pMode = ReploutMode }
      | "\\restartrepl" `isInfixOf` s' ->
          -- Commit the input with no accompanying output, indicating it should
          -- be checked for errors but that the result can be discarded.
          addReplData
      | Just (InlineReplin, cmd, rst) <- inlineRepl s -> do
          -- Ingest an inline replin command.
          addReplin cmd
          processLine rst
      | Just (InlineReplout, cmd, rst) <- inlineRepl s -> do
          -- Ingest an inline replout command, switching to replout mode.
          modify' $ \st -> st { pMode = AwaitingReploutMode }
          addReplout cmd
          processLine rst
      | otherwise -> return ()
    ReplinMode
      | "\\end{replinVerb}" `isInfixOf` s' ->
          -- Switching from ingesting repl input to awaiting repl input.
          modify' $ \st -> st { pMode = AwaitingReplinMode }
      | otherwise -> do
          -- Ingest the current line, and stay in ReplinMode.
          replin <- gets pReplin
          let replin' = replin Seq.|> Line ln s
          modify' $ \st -> st { pReplin = replin' }
    AwaitingReploutMode
      | "\\begin{reploutVerb}" `isInfixOf` s' -> do
          -- Switching from awaiting to ingesting repl output.
          modify' $ \st -> st { pMode = ReploutMode }
      | "\\begin{replinVerb}" `isInfixOf` s' -> do
          -- Switching from awaiting repl output to ingesting repl input. This
          -- indicates we have finished building the current repl data, so
          -- commit it by appending it to the end of the list of completed repl
          -- data and start a fresh one.
          addReplData
          modify' $ \st -> st { pMode = ReplinMode }
      | Just (InlineReplin, cmd, rst) <- inlineRepl s -> do
          -- Ingest an inline replin command, switching to replin mode and
          -- committing the current repl data.
          addReplData
          modify' $ \st -> st { pMode = AwaitingReplinMode }
          addReplin cmd
          processLine rst
      | Just (InlineReplout, cmd, rst) <- inlineRepl s -> do
          -- Ingest an replout command.
          addReplout cmd
          processLine rst
      | otherwise -> return ()
    ReploutMode
      | "\\end{reploutVerb}" `isInfixOf` s' -> do
          -- Switching from ingesting repl output to awaiting repl output.
          modify' $ \st -> st { pMode = AwaitingReploutMode }
      | otherwise -> do
          -- Ingest the current line, and stay in ReploutMode.
          replout <- gets pReplout
          let replout' = replout Seq.|> Line ln s
          modify' $ \st -> st { pReplout = replout' }

  modify' $ \st -> st { pCurrentLine = pCurrentLine st + 1 }

main :: IO ()
main = do
  opts <- execParser p
  allLines <- lines <$> readFile (latexFile opts)
  PState {..} <- flip execStateT initPState $ do
    -- Process every line
    traverse_ processLine allLines
    -- Insert the final ReplData upon completion
    addReplData
  let allReplData = toList pCompletedReplData
      dir = fromMaybe "." (tempDir opts)

  forM_ allReplData $ \rd -> do
    let inText = unlines $ fmap lineText $ toList $ rdReplin rd
        inFileNameTemplate = "in.icry"
    inFile <- writeTempFile dir inFileNameTemplate inText

    let exe = fromMaybe "./cry run" (cryptolExe opts)
        cryCmd = (P.shell (exe ++ " -b " ++ inFile))

    cryOut <- P.readCreateProcess cryCmd ""

    -- remove temporary input file
    removeFile inFile

    if Seq.null (rdReplout rd)
      then do Line lnInrepl _ Seq.:<| _ <- return $ rdReplin rd
              when ("error" `isInfixOf` cryOut) $ do
                putStrLn $ "REPL error (replin starting at line " ++ show lnInrepl ++ ")."
                putStr cryOut
                exitFailure
      else do let outExpectedText = unlines $ fmap lineText $ toList $ rdReplout rd
                  outExpectedFileNameTemplate = "out-expected.icry"
                  outFileNameTemplate = "out.icry"
              outExpectedFile <- writeTempFile dir outExpectedFileNameTemplate outExpectedText
              outFile <- emptyTempFile dir outFileNameTemplate

              let outText = unlines $ filter (not . null) $ trim <$> (tail $ lines cryOut)

              writeFile outFile outText

              let diffCmd = (P.shell ("diff " ++ outExpectedFile ++ " " ++ outFile))

              (diffEC, diffOut, _) <- P.readCreateProcessWithExitCode diffCmd ""
              case diffEC of
                ExitSuccess -> do
                  -- Remove temporary output files
                  removeFile outExpectedFile
                  removeFile outFile
                ExitFailure _ -> do
                  Line lnInrepl _ Seq.:<| _ <- return $ rdReplin rd

                  putStrLn $ "REPL output mismatch (replin starting at line " ++ show lnInrepl ++ ")."
                  putStrLn $ "Diff output:"
                  putStr diffOut

                  let outExpectedFileName = dir ++ "/" ++ outExpectedFileNameTemplate
                      outFileName = dir ++ "/" ++ outFileNameTemplate

                  putStrLn ""
                  putStrLn $ "Expected output written to: " ++ outExpectedFileName
                  putStrLn $ "Actual output written to: " ++ outFileName

                  -- Write to log files
                  writeFile outExpectedFileName outExpectedText
                  writeFile outFileName outText

                  -- Remove temporary output files and exit
                  removeFile outExpectedFile
                  removeFile outFile
                  exitFailure

  putStrLn $ "Successfully checked " ++ show (length allReplData) ++ " repl examples."

  return ()

  where p = info (optsParser <**> helper)
            ( fullDesc
              <> progDesc "Test the exercises in a cryptol LaTeX file"
              <> header "check-exercises -- test cryptol exercises"
            )
