#!/usr/bin/env runhaskell

-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

import Cryptol.Parser
import Cryptol.Parser.AST(noPos)
import System.Process(readProcess)

main :: IO ()
main =
  do txt <- getContents
     putStrLn =<< readProcess "ppsh" ["--html"]
                    (show $ dropLoc $ parseProgram Layout txt)

dropLoc (Right a) = Right (noPos a)
dropLoc (Left a)  = Left a

