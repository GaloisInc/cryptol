-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

module Main where

import Control.Monad (when,unless,foldM)
import Data.List (isPrefixOf,partition,nub)
import Data.Monoid (Monoid(..),Endo(..))
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
    (createProcess,CreateProcess(..),StdStream(..),proc,waitForProcess)
import System.IO
    (hGetContents,IOMode(..),withFile,SeekMode(..),Handle,hSetBuffering
    ,BufferMode(..))
import Test.Framework (defaultMain,Test,testGroup)
import Test.Framework.Providers.HUnit (testCase)
import Test.HUnit (assertFailure)
import qualified Control.Exception as X
import qualified Data.Map as Map


main :: IO ()
main  = do
  opts <- parseOptions
  createDirectoryIfMissing True (optResultDir opts)
  resultsDir <- canonicalizePath (optResultDir opts)
  let opts' = opts { optResultDir = resultsDir }
  files <- findTests (optTests opts')
  withArgs (optOther opts') (defaultMain (generateTests opts' files))


-- Command Line Options --------------------------------------------------------

data TestStrategy
  = TestDiscover FilePath
  | TestFile FilePath
    deriving (Show)

data Options = Options
  { optCryptol   :: String
  , optOther     :: [String]
  , optHelp      :: Bool
  , optResultDir :: FilePath
  , optTests     :: [TestStrategy]
  , optDiff      :: String
  } deriving (Show)

defaultOptions :: Options
defaultOptions  = Options
  { optCryptol   = "cryptol-2"
  , optOther     = []
  , optHelp      = False
  , optResultDir = "output"
  , optTests     = []
  , optDiff      = "meld"
  }

setHelp :: Endo Options
setHelp  = Endo (\ opts -> opts { optHelp = True } )

setDiff :: String -> Endo Options
setDiff diff = Endo (\opts -> opts { optDiff = diff })

setCryptol :: String -> Endo Options
setCryptol path = Endo (\ opts -> opts { optCryptol = path } )

addOther :: String -> Endo Options
addOther arg = Endo (\ opts -> opts { optOther = optOther opts ++ [arg] } )

setResultDir :: String -> Endo Options
setResultDir path = Endo (\ opts -> opts { optResultDir = path })

addDiscover :: String -> Endo Options
addDiscover path =
  Endo (\ opts -> opts { optTests = TestDiscover path : optTests opts })

addTestFile :: String -> Endo Options
addTestFile path =
  Endo (\ opts -> opts { optTests = TestFile path : optTests opts })

options :: [OptDescr (Endo Options)]
options  =
  [ Option "c" ["cryptol"] (ReqArg setCryptol "PATH")
    "the cryptol executable to use"
  , Option "d" ["base"] (ReqArg addDiscover "PATH")
    "the base directory for test discovery"
  , Option "r" ["result-dir"] (ReqArg setResultDir "PATH")
    "the result directory for test runs"
  , Option "p" ["diff-prog"] (ReqArg setDiff "PROG")
    "use this diffing program on failures"
  , Option "T" [] (ReqArg addOther "STRING")
    "add an argument to pass to the test-runner main"
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

  out      <- readFile resultOut
  expected <- readFile goldFile
  checkOutput expected out
  where
  goldFile  = dir </> file <.> "stdout"
  resultOut = resultDir </> file <.> "stdout"
  resultDir  = optResultDir opts </> dir
  indent str = unlines (map ("  " ++) (lines str))
  checkOutput expected out
    | expected == out = return ()
    | otherwise = assertFailure $ unwords [ optDiff opts, goldFile, resultOut ]

-- Test Discovery --------------------------------------------------------------

findTests :: [TestStrategy] -> IO TestFiles
findTests  = foldM step mempty
  where
  step tests strategy = do
    tests' <- evalStrategy strategy
    return (tests `mappend` tests')

  evalStrategy strategy = case strategy of

    TestDiscover path -> testDiscovery path

    TestFile path ->
      let (dir,file) = splitFileName path
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
