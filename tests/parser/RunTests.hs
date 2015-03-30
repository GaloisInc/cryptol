-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

module Main(main) where

import Cryptol.Parser
import Cryptol.Parser.PP(pp)
import Cryptol.Parser.AST

import System.Directory(getDirectoryContents,doesFileExist,doesDirectoryExist)
import Data.List(isSuffixOf)
import System.Exit(exitFailure)
import System.FilePath((</>),takeExtension)
import Control.Monad(unless)

main :: IO ()
main =
  do ok <- runTestsIn "tests"
     unless ok exitFailure

roundTrip :: FilePath -> IO Bool
roundTrip file =
  delimit $
  do putStrLn $ "File: " ++ file
     txt1 <- readFile file
     putStr "Trip 1: "
     case parseProgram Layout txt1 of
       Left err    -> print (ppError err) >> return False
       Right prog1 ->
         do let txt2 = show (pp prog1)
            putStrLn "OK"
            line
            putStrLn txt2
            line
            putStr "Trip 2: "
            case parseProgram Layout txt2 of
              Left err    -> print (ppError err) >> return False
              Right prog2 ->
                do putStr "OK "
                   if noPos prog1 == noPos prog2
                      then putStrLn "(same)" >> return True
                      else do putStrLn "(DIFFERENT)"
                              line
                              putStrLn $ show $ pp prog2
                              return False

--------------------------------------------------------------------------------
runTestsIn :: FilePath -> IO Bool
runTestsIn dir =
  do fs <- getDirectoryContents dir
     and `fmap` mapM (runTest dir) fs

runTest :: FilePath -> FilePath -> IO Bool
runTest dir fileName | takeExtension fileName == ".cry" =
  do let file = dir </> fileName
     ok <- doesFileExist file
     if ok
       then roundTrip file
       else return True

runTest dir dirName =
  do let subDir = dir </> dirName
     ok <- doesDirectoryExist subDir
     if ok && dirName /= "." && dirName /= ".." then runTestsIn subDir
                                                else return True

line :: IO ()
line = putStrLn (replicate 80 '-')

delimit :: IO a -> IO a
delimit io = do line
                a <- io
                line
                return a


