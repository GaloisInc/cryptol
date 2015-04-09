{-# LANGUAGE CPP #-}
-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

module Main where

import Control.Monad (when,foldM)
import Data.List (isPrefixOf,partition,nub)
import Data.Monoid (Endo(..))
import System.Console.GetOpt
    (getOpt,usageInfo,ArgOrder(..),OptDescr(..),ArgDescr(..))
import System.Directory
    (getDirectoryContents,doesDirectoryExist,createDirectoryIfMissing
    ,canonicalizePath)
import System.Environment (getArgs,withArgs,getProgName)
import System.Exit (exitFailure,exitSuccess)
import System.FilePath
    ((</>),(<.>),takeExtension,splitFileName,splitDirectories,pathSeparator
    ,isRelative)
import System.Process
    (createProcess,CreateProcess(..),StdStream(..),proc,waitForProcess
    ,readProcessWithExitCode)
import System.IO
    (IOMode(..),withFile,Handle,hSetBuffering,BufferMode(..))
import Test.Framework (defaultMain,Test,testGroup)
import Test.Framework.Providers.HUnit (testCase)
import Test.HUnit (assertFailure)
import qualified Control.Exception as X
import qualified Data.Map as Map

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative ((<$>))
import Data.Monoid (Monoid(..))
#endif

#if defined(mingw32_HOST_OS) || defined(__MINGW32__)
import Text.Regex
#endif

main :: IO ()
main  = do
  opts <- parseOptions
  createDirectoryIfMissing True (optResultDir opts)
  resultsDir <- canonicalizePath (optResultDir opts)
  let opts' = opts { optResultDir = resultsDir }
  files <- findTests (optTests opts')
  withArgs (optOther opts') (defaultMain (generateTests opts' files))


-- Command Line Options --------------------------------------------------------

data Options = Options
  { optCryptol   :: String
  , optOther     :: [String]
  , optHelp      :: Bool
  , optResultDir :: FilePath
  , optTests     :: [FilePath]
  , optDiff      :: Maybe String
  , optIgnoreExpected :: Bool
  } deriving (Show)

defaultOptions :: Options
defaultOptions  = Options
  { optCryptol   = "cryptol-2"
  , optOther     = []
  , optHelp      = False
  , optResultDir = "output"
  , optTests     = []
  , optDiff      = Nothing
  , optIgnoreExpected = False
  }

setHelp :: Endo Options
setHelp  = Endo (\ opts -> opts { optHelp = True } )

setDiff :: String -> Endo Options
setDiff diff = Endo (\opts -> opts { optDiff = Just diff })

setCryptol :: String -> Endo Options
setCryptol path = Endo (\ opts -> opts { optCryptol = path } )

addOther :: String -> Endo Options
addOther arg = Endo (\ opts -> opts { optOther = optOther opts ++ [arg] } )

setResultDir :: String -> Endo Options
setResultDir path = Endo (\ opts -> opts { optResultDir = path })

addTestFile :: String -> Endo Options
addTestFile path =
  Endo (\ opts -> opts { optTests = path : optTests opts })

setIgnoreExpected :: Endo Options
setIgnoreExpected  =
  Endo (\ opts -> opts { optIgnoreExpected = True })

options :: [OptDescr (Endo Options)]
options  =
  [ Option "c" ["cryptol"] (ReqArg setCryptol "PATH")
    "the cryptol executable to use"
  , Option "r" ["result-dir"] (ReqArg setResultDir "PATH")
    "the result directory for test runs"
  , Option "p" ["diff-prog"] (ReqArg setDiff "PROG")
    "use this diffing program on failures"
  , Option "T" [] (ReqArg addOther "STRING")
    "add an argument to pass to the test-runner main"
  , Option "i" ["ignore-expected"] (NoArg setIgnoreExpected)
    "ignore expected failures"
  , Option "h" ["help"] (NoArg setHelp)
    "display this message"
  ]

parseOptions :: IO Options
parseOptions  = do
  args <- getArgs
  case getOpt (ReturnInOrder addTestFile) options args of

    (es,_,[]) -> do
      let opts = appEndo (mconcat es) defaultOptions
      when (optHelp opts) $ do
        displayUsage []
        exitSuccess

      -- canonicalize the path to cryptol, if it's relative
      cryptol' <- if pathSeparator `elem` optCryptol opts
                     && isRelative (optCryptol opts)
                     then canonicalizePath (optCryptol opts)
                     else return (optCryptol opts)

      return opts
        { optCryptol = cryptol'
        , optTests   = reverse (optTests opts)
        }

    (_,_,errs) -> do
      displayUsage errs
      exitFailure

displayUsage :: [String] -> IO ()
displayUsage errs = do
  prog <- getProgName
  let banner = unlines (errs ++ ["Usage: " ++ prog ++ " [OPTIONS] [FILES]"])
  putStrLn (usageInfo banner options)


-- Test Generation -------------------------------------------------------------

-- | Write the output of a run of cryptol-2 to this handle.  Stdin and stderr
-- will both be given the handle provided.
cryptol2 :: Options -> Handle -> FilePath -> [String] -> IO ()
cryptol2 opts hout path args = do
  (_, _, _, ph) <- createProcess (proc (optCryptol opts) args)
                     { cwd     = Just path
                     , std_out = UseHandle hout
                     , std_in  = Inherit
                     , std_err = UseHandle hout
                     }
  _ <- waitForProcess ph
  return ()

generateTests :: Options -> TestFiles -> [Test]
generateTests opts = loop ""
  where
  loop dir (TestFiles m fs) = as ++ grouped
    where
    as      = map (generateAssertion opts dir) fs
    grouped = [ testGroup path (loop (dir </> path) t)
              | (path,t) <- Map.toList m ]


generateAssertion :: Options -> FilePath -> FilePath -> Test
generateAssertion opts dir file = testCase file $ do

  createDirectoryIfMissing True resultDir

  withFile resultOut WriteMode $ \ hout ->
    do hSetBuffering hout NoBuffering
       cryptol2 opts hout dir ["-b",file]

  out      <- fixPaths <$> readFile resultOut
  expected <- readFile goldFile
  mbKnown  <- X.try (readFile knownFailureFile)
  checkOutput mbKnown expected out
  where
  knownFailureFile = dir </> file <.> "fails"
  goldFile  = dir </> file <.> "stdout"
  resultOut = resultDir </> file <.> "stdout"
  resultDir  = optResultDir opts </> dir
  checkOutput mbKnown expected out
    | expected == out =
      case mbKnown of
        Left _  -> return ()
        Right _ -> assertFailure $
            "Test completed successfully.  Please remove " ++ knownFailureFile
    | otherwise =
      case mbKnown of

        Left (X.SomeException {})
          | Just prog <- optDiff opts ->
            do goldFile' <- canonicalizePath goldFile
               assertFailure (unwords [ prog, goldFile', "\\\n    ", resultOut ])

          | otherwise ->
            do goldFile' <- canonicalizePath goldFile
               (_,diffOut,_) <- readProcessWithExitCode "diff" [ goldFile', resultOut ] ""
               assertFailure diffOut

        Right fail_msg | optIgnoreExpected opts -> return ()
                       | otherwise              -> assertFailure fail_msg

-- Test Discovery --------------------------------------------------------------

findTests :: [FilePath] -> IO TestFiles
findTests  = foldM step mempty
  where
  step tests path = do
    tests' <- evalStrategy path
    return (tests `mappend` tests')

  evalStrategy path =
    do isDir <- doesDirectoryExist path
       if isDir
         then testDiscovery path
         else let (dir,file) = splitFileName path
                  dirs       = splitDirectories dir
                  insert d t = TestFiles (Map.singleton d t) []
              in return $! foldr insert (TestFiles Map.empty [file]) dirs


-- | Files that end in .icry are cryptol test cases.
isTestCase :: FilePath -> Bool
isTestCase path = takeExtension path == ".icry"

-- | Directory structure of the discovered tests.  Each entry in the map
-- represents a single folder, with the top-level list representing tests
-- inside the base directory.
data TestFiles = TestFiles (Map.Map FilePath TestFiles) [FilePath]
    deriving (Show)

instance Monoid TestFiles where
  mempty      = TestFiles Map.empty []
  mappend (TestFiles lt lf) (TestFiles rt rf) = TestFiles mt mf
    where
    mt = Map.unionWith mappend lt rt
    mf = nub (lf ++ rf)

nullTests :: TestFiles -> Bool
nullTests (TestFiles m as) = null as && Map.null m

-- | Find test cases to run.
testDiscovery :: FilePath -> IO TestFiles
testDiscovery from = do
  subTests <- process from =<< getDirectoryContents from
  let insert d t = TestFiles (Map.singleton d t) []
  return (foldr insert subTests (splitDirectories from))

  where
  process base contents = do
    let (tests,files) = partition isTestCase
                      $ filter (not . isDotFile) contents
    subdirs <- mapM (resolve base) files
    let subTests = Map.fromList [ (p,m) | (p,m) <- subdirs
                                        , not (nullTests m) ]

    return (TestFiles subTests tests)

  loop base = do
    isDir <- doesDirectoryExist base
    if isDir
       then do subTests <- process base =<< getDirectoryContents base
               return (TestFiles (Map.singleton base subTests) [])
       else return mempty

  resolve base p = do
    let path = base </> p
    tests <- loop path
    return (p,tests)


-- Utilities -------------------------------------------------------------------

-- | Screen out dotfiles.
isDotFile :: FilePath -> Bool
isDotFile path = "." `isPrefixOf` path

-- | Normalize to unix-style paths with forward slashes when on
-- Windows. This is pretty crude; it just looks for any non-whitespace
-- strings that contain a blackslash and end in @.cry@ or @.icry@.
fixPaths :: String -> String
#if defined(mingw32_HOST_OS) || defined(__MINGW32__)
fixPaths str = go str
  where
  go str
    | Just (pre, match, post, _) <- matchCryFile str
    = pre ++ (subst match) ++ go post
    | otherwise
    = str
  subst match = subRegex (mkRegex "\\\\") match "/"
  matchCryFile = matchRegexAll (mkRegex "\\\\([^[:space:]]*\\.i?cry)")
#else
fixPaths = id
#endif
