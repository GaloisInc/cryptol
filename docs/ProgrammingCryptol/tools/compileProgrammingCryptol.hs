-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# OPTIONS -Wall #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE ImplicitParams #-}

module Main(main) where

import Control.Parallel.Strategies
import Data.Char
import Data.List
import Numeric
import System.Exit
import System.IO
import System.Timeout
import System.Directory
import System.FilePath
import System.Process
import System.Time


---------------------------------------------------------------
-- Configuration

targetName :: String
targetName = "Cryptol"

topDir       :: FilePath
topDir       = "/Volumes/Galois/Projects/CTK/Cryptol/teardrop/Documentation/ProgrammingCryptol"

fullTriggers :: [FilePath] -- these trigger full compile
fullTriggers = [ "bib"  </> "cryptol.bib"
               , "utils" </> "Indexes.tex"
               , "utils" </> "GlossaryItems.tex"
               ]

-- rest is derived or should be glacial, but better checkout
tmpDir :: FilePath
tmpDir = "/tmp"

logFile :: FilePath   -- latex log
logFile = tmpDir </> targetName <.> "log"

target :: FilePath    -- final pdf
target = targetName <.> "pdf"

title :: String  -- growl title
title = targetName
---------------------------------------------------------------
-- utils
ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM t tb fb = t >>= \b -> if b then tb else fb

whenM :: Monad m => m Bool -> m () -> m ()
whenM t a = ifM t a (return ())

ignore :: Monad m => m a -> m ()
ignore m = m >> return ()

modTime :: FilePath -> IO (Maybe ClockTime)
modTime fn = fmap Just (getModificationTime fn) `catch` const (return Nothing)

safeSys :: IO () -> IO ()
safeSys a = a `catch` die
  where die e = do putStrLn $ "\nException: " ++ show e
                   exitWith (ExitFailure 1)

instance NFData ExitCode

timeIt :: NFData a => IO a -> IO (String, a)
timeIt m = do start <- getClockTime
              r <- m
              end <- rnf r `seq` getClockTime
              let elapsed  = diffClockTimes end start
                  elapsedS = "Elapsed:" ++ showTDiff elapsed
              rnf elapsedS `seq` return (elapsedS, r)
  where showTDiff :: TimeDiff -> String
        showTDiff itd = et
          where td = normalizeTimeDiff itd
                vals = dropWhile (\(v, _) -> v == 0) (zip [tdYear td, tdMonth td, tdDay td, tdHour td, tdMin td] "YMDhm")
                sec = ' ' : show (tdSec td) ++ dropWhile (/= '.') pico
                pico = showFFloat (Just 3) (((10**(-12))::Double) * fromIntegral (tdPicosec td)) "s"
                et = concatMap (\(v, c) -> ' ':show v ++ [c]) vals ++ sec

growl :: (?curId :: Id) => Bool -> String -> [String] -> IO ()
growl goaway t s = ignore $ readProcess "growlnotify" (stickyArg ++ [title, t] ++ ["-d", "Cryptol" ++ show ?curId] ++ ["-m", args]) ""
  where stickyArg | goaway = []
                  | True   = ["-s"]
        args = concat $ intersperse "\n" s
---------------------------------------------------------------

type Id = Integer

main :: IO ()
main = do hSetBuffering stdin NoBuffering
          hSetBuffering stdout NoBuffering
          hSetEcho stdout False
          safeSys $ setCurrentDirectory topDir
          let ?curId = 0 in prompt True

prompt :: (?curId :: Id) => Bool -> IO ()
prompt tout = do
      let curId'  = ?curId+1
          prompt' = let ?curId = curId' in prompt
      putStr $ "\r" ++ replicate 60 ' ' ++ "\r" ++ if tout then promptS else promptWS
      mbc <- (if tout then timeout 1000000 else (fmap Just)) getChar
      case fmap toUpper mbc of
        Nothing  -> whenM need (ifM needFull full quick) >> prompt' True
        Just 'L' -> quick >> prompt' True
        Just 'F' -> full  >> prompt' True
        Just 'C' -> prompt' True
        Just 'W' -> prompt' False
        Just 'Q' -> do putStrLn "\nTerminating.."
                       exitWith ExitSuccess
        _        -> prompt' True
  where promptS, promptWS :: String
        promptS  = "Action (l[atex] f[ull] w[ait] q[uit])? "
        promptWS = "Action (l[atex] f[ull] w[ait] q[uit] c[ontinue])? "

needFull :: IO Bool
needFull = do mtt  <- modTime target
              mtts <- mapM modTime fullTriggers
              return $ any (> mtt) mtts

quick :: (?curId :: Id) => IO ()
quick = do whenM (doesFileExist target) $ removeFile target
           make "quick" ["quick"]

full  :: (?curId :: Id) => IO ()
full = do _ <- readProcess "make" ["superClean"] ""
          make "full" []

need :: IO Bool
need = do r <- readProcess "make" ["-n"] ""
          return $ dropWhile (/= ':') r /= ": Nothing to be done for `all'.\n"

make :: (?curId :: Id) => String -> [String] -> IO ()
make how args = do
    growl False "" $ ["Starting " ++ how ++ " compilation"]
    (d, ec) <- timeIt $ system $ unwords $ "make" : args
    case ec of
      ExitFailure _ -> dieErrors
      ExitSuccess   -> checkWarnings d

dieErrors :: (?curId :: Id) => IO ()
dieErrors = do logCts <- readFile logFile >>= return . filter (not . all isSpace) . lines
               let process (x:y:z:rest) sofar
                     | take 2 y == "l." = process rest (z:y:x:sofar)
                     | True             = process (y:z:rest) sofar
                   process _ sofar  = sofar
                   badLines = process logCts []
               growl False "(FAILED)" badLines

checkWarnings :: (?curId :: Id) => String -> IO ()
checkWarnings d = do logLines <- readFile logFile >>= return . lines
                     let badLines = filter isEither logLines
                     case badLines of
                       [] -> checkSpelling d
                       _  -> growl False "(FAILED)" $ badLines
  where (lw, w) = (length w, "LaTeX Warning")
        (lu, u) = (length u, "undefined")
        isWarning   s = any (\l -> take lw l == w) $ tails s
        isUndefined s = any (\l -> take lu l == u) $ tails s
        isEither s = isWarning s || isUndefined s

checkSpelling :: (?curId :: Id) => String -> IO ()
checkSpelling d = do logCts <- readProcessWithExitCode "make" ["quickSpell"] "" >>= \(_, out, err) -> return (lines (out ++ err))
                     let new = map (drop 2) $ filter (\l -> take 1 l == "<") logCts
                         old = map (drop 2) $ filter (\l -> take 1 l == ">") logCts
                     case new of
                       [] -> case old of
                               [] -> growl True "(SUCCESS)" [d]
                               _  -> growl False "(SUCCESS, Fixed words)" $ old
                       _  -> growl False "(FAILED Spell check)" $ new
