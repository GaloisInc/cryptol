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
import Data.Maybe (fromMaybe)
import qualified Data.Sequence as Seq
import Numeric.Natural
import qualified System.Process as P
import System.Directory
import System.Exit
import System.IO.Temp
import Data.Foldable (toList)

data Opts = Opts { latexFile :: FilePath
                   -- ^ The latex file we are going to check
                 , cryptolExe :: Maybe FilePath
                   -- ^ Path to cryptol executable (default: cabal v2-exec cryptol)
                 , tempDir :: Maybe FilePath
                   -- ^ Path to store temporary files and log files
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
        <> help "Directory for log files in case of failure (defaults to .)"
        ) )

-- | Trim whitespace off both ends of a string
trim :: String -> String
trim = f . f
   where f = reverse . dropWhile isSpace

----------------------------------------------------------------------
-- LaTeX processing state monad
--
-- We process the text-by-line. The behavior of the state monad on a line is
-- governed by the mode it is currently in. The overall idea is to read in
-- "replin" and "replout" sections of the file in alternation, grouping each
-- replin/replout pair into discrete ReplData elements which will be validated
-- against the Cryptol REPL. The current mode dictates how to interpret each
-- line, and which mode to transition to next.
--
-- There are four modes: AwaitingReplinMode, ReplinMode, AwaitingReploutMode,
-- and ReploutMode. Below we describe the behavior of each mode.
--
-- AwaitingReplinMode: When in this mode, we are anticipating "replin" lines;
-- that is, lines that will be issued as input to the repl. When we see a
-- \begin{replinVerb}, we transition to ReplinMode. When we see a
-- \begin{reploutVerb}, we transition to ReploutMode. When we see an inline
-- \replin{..} command, we add the content to the list of replin lines without
-- changing modes. When we see an inline \replout{..} command, we switch to
-- AwaitingReploutMode and add the content to the list of replout lines.
--
-- ReplinMode: When in this mode, we are inside of a "\begin{replinVerb}"
-- section. When we see a \end{replinVerb} line, we transition to
-- AwaitingReplinMode (since there could be more replin lines following some
-- explanatory text). Otherwise, we simply add the entire line to the list of
-- replin lines.
--
-- AwaitingReploutMode: When in this mode, we are anticipating "replout" lines;
-- that is, lines that should be compared to the output of the repl once the
-- already-processed replin lines have been issued to the REPL. When we see a
-- \begin{reploutVerb}, we transition to ReploutMode. When we see a
-- \begin{replinVerb}, we have come to the end of this particular ReplData
-- segment, so we package up the replin and replout lines into a ReplData, add
-- that new object to the growing list of ReplData objects to be validated, and
-- transition to ReplinMode to start reading in lines for the next ReplData.
-- When we see a \replout{..} command, we add the content to the list of replout
-- lines without changing modes. When we see an inline \replin{..} command, we
-- treat it like a \begin{replinVerb}, except we also add the contents as the
-- first line of replin, and we transition to AwaitingReplinMode rather than
-- ReplinMode.

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

-- | Latex processing state
data PState = PState { pMode              :: PMode
                       -- ^ current mode
                     , pCompletedReplData :: Seq.Seq ReplData
                       -- ^ list of all completed REPL input/output pairs to be
                       -- validated (thus far)
                     , pReplin            :: Seq.Seq Line
                       -- ^ list of replin lines (so far) for unfinished ReplData
                     , pReplout           :: Seq.Seq Line
                       -- ^ list of replout lines (so far) for unfinished ReplData
                     , pCurrentLine       :: Natural
                     }
  deriving (Eq, Show)

initPState :: PState
initPState = PState AwaitingReplinMode Seq.empty Seq.empty Seq.empty 1

-- | P monad for reading in lines
type P = State PState

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

data InlineRepl = InlineReplin | InlineReplout

-- | Extracts the first inline repl command returns the type of command, its
-- contents, and the remainder of the string.
inlineRepl :: String -> Maybe (InlineRepl, String, String)
inlineRepl s
  | Just (_, ir, s1) <- stripInfixOneOf [ "\\replin|"
                                        , "\\replout|"
                                        , "\\hidereplin|"
                                        , "\\hidereplout|"] s
  , (s2, s3) <- break (=='|') s1 = case ir of
      "\\replin|" -> Just (InlineReplin, s2, s3)
      "\\replout|" -> Just (InlineReplout, s2, s3)
      "\\hidereplin|" -> Just (InlineReplin, s2, s3)
      "\\hidereplout|" -> Just (InlineReplout, s2, s3)
      _ -> error "PANIC: CheckExercises.inlineRepl"
  | otherwise = Nothing

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

nextLine :: P ()
nextLine = modify' $ \st -> st { pCurrentLine = pCurrentLine st + 1 }

-- | The main function for our monad. Input is a single line.
processLine :: String -> P ()
processLine s = do
  let s_nocomment = takeWhile (not . (== '%')) s
      s_nowhitespace = filter (not . isSpace) s_nocomment
  m <- gets pMode
  ln <- gets pCurrentLine
  case m of
    AwaitingReplinMode
      | "\\begin{replinVerb}" `isInfixOf` s_nowhitespace -> do
          -- Switching from awaiting to ingesting repl input.
          modify' $ \st -> st { pMode = ReplinMode }
          nextLine
      | "\\begin{reploutVerb}" `isInfixOf` s_nowhitespace -> do
          -- Switching from awaiting repl input to ingesting repl output.
          modify' $ \st -> st { pMode = ReploutMode }
          nextLine
      | "\\restartrepl" `isInfixOf` s_nowhitespace -> do
          -- Commit the input with no accompanying output, indicating it should
          -- be checked for errors but that the result can be discarded.
          addReplData
          nextLine
      | Just (InlineReplin, cmd, rst) <- inlineRepl s -> do
          -- Ingest an inline replin command.
          addReplin cmd
          processLine rst
      | Just (InlineReplout, cmd, rst) <- inlineRepl s -> do
          -- Ingest an inline replout command, switching to replout mode.
          modify' $ \st -> st { pMode = AwaitingReploutMode }
          addReplout cmd
          processLine rst
      | otherwise -> nextLine
    ReplinMode
      | "\\end{replinVerb}" `isInfixOf` s_nowhitespace -> do
          -- Switching from ingesting repl input to awaiting repl input.
          modify' $ \st -> st { pMode = AwaitingReplinMode }
          nextLine
      | otherwise -> do
          -- Ingest the current line, and stay in ReplinMode.
          replin <- gets pReplin
          let replin' = replin Seq.|> Line ln s -- use the full input since %
                                                -- isn't a comment in verbatim
                                                -- mode.
          modify' $ \st -> st { pReplin = replin' }
          nextLine
    AwaitingReploutMode
      | "\\begin{reploutVerb}" `isInfixOf` s_nowhitespace -> do
          -- Switching from awaiting to ingesting repl output.
          modify' $ \st -> st { pMode = ReploutMode }
          nextLine
      | "\\begin{replinVerb}" `isInfixOf` s_nowhitespace -> do
          -- Switching from awaiting repl output to ingesting repl input. This
          -- indicates we have finished building the current repl data, so
          -- commit it by appending it to the end of the list of completed repl
          -- data and start a fresh one.
          addReplData
          modify' $ \st -> st { pMode = ReplinMode }
          nextLine
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
      | otherwise -> nextLine
    ReploutMode
      | "\\end{reploutVerb}" `isInfixOf` s_nowhitespace -> do
          -- Switching from ingesting repl output to awaiting repl output.
          modify' $ \st -> st { pMode = AwaitingReploutMode }
          nextLine
      | otherwise -> do
          -- Ingest the current line, and stay in ReploutMode.
          replout <- gets pReplout
          let replout' = replout Seq.|> Line ln s -- use the full input since %
                                                  -- isn't a comment in verbatim
                                                  -- mode.
          modify' $ \st -> st { pReplout = replout' }
          nextLine

main :: IO ()
main = do
  opts <- execParser p
  allLines <- lines <$> readFile (latexFile opts)
  let PState {..} = flip execState initPState $ do
        -- Process every line
        traverse_ processLine allLines
        -- Insert the final ReplData upon completion
        addReplData
  let allReplData = toList pCompletedReplData
      dir = fromMaybe "." (tempDir opts)

  forM_ allReplData $ \rd -> do
    let inText = unlines $ fmap (trim . lineText) $ toList $ rdReplin rd
        inFileNameTemplate = "in.icry"
    inFile <- writeTempFile dir inFileNameTemplate inText

    let exe = fromMaybe "./cry run" (cryptolExe opts)

    if Seq.null (rdReplout rd)
      then do let cryCmd = (P.shell (exe ++ " --interactive-batch " ++ inFile ++ " -e"))
              (cryEC, cryOut, _) <- P.readCreateProcessWithExitCode cryCmd ""


              Line lnReplinStart _ Seq.:<| _ <- return $ rdReplin rd
              _ Seq.:|> Line lnReplinEnd _ <- return $ rdReplin rd
              case cryEC of
                ExitFailure _ -> do
                  putStrLn $ "REPL error (replin lines " ++
                    show lnReplinStart ++ "-" ++ show lnReplinEnd ++ ")."
                  putStr cryOut
                  exitFailure
                ExitSuccess -> do
                  -- remove temporary input file
                  removeFile inFile
      else do let outExpectedText = unlines $ filter (not . null) $
                    fmap (trim . lineText) $ toList $ rdReplout rd
                  outExpectedFileNameTemplate = "out-expected.icry"
                  outFileNameTemplate = "out.icry"
                  cryCmd = (P.shell (exe ++ " --interactive-batch " ++ inFile))
              outExpectedFile <- writeTempFile dir outExpectedFileNameTemplate outExpectedText
              outFile <- emptyTempFile dir outFileNameTemplate

              (_, cryOut, _) <- P.readCreateProcessWithExitCode cryCmd ""

              -- remove temporary input file
              removeFile inFile

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
                  Line lnReplinStart _ Seq.:<| _ <- return $ rdReplin rd
                  _ Seq.:|> Line lnReplinEnd _ <- return $ rdReplin rd
                  Line lnReploutStart _ Seq.:<| _ <- return $ rdReplout rd
                  _ Seq.:|> Line lnReploutEnd _ <- return $ rdReplout rd

                  putStrLn $ "REPL output mismatch."
                  putStrLn $ "  (replin lines " ++
                    show lnReplinStart ++ "-" ++ show lnReplinEnd ++
                    ", replout lines " ++ show lnReploutStart ++ "-" ++
                    show lnReploutEnd ++ ")."
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
