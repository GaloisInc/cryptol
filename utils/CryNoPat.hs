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
import Cryptol.Parser.NoPat
import Cryptol.Utils.PP

import System.Process(readProcess)
import System.IO(hPrint,stderr)

main :: IO ()
main =
  do txt <- getContents
     let mb = parseProgram Layout txt
     case mb of
       Left err -> hPrint stderr $ ppError err
       Right p  ->
         case removePatterns p of
           (p1,[])  -> print $ pp p1
           (_,errs) -> hPrint stderr $ vcat $ map pp errs



