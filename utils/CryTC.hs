#!/usr/bin/env runhaskell

-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

import Cryptol.Parser as Parser
import Cryptol.Parser.AST(noPos)
import Cryptol.Parser.Position(Range(..),start)
import Cryptol.Parser.NoPat
import Cryptol.Utils.PP
import Cryptol.TypeCheck as TC

import System.Process(readProcess)
import System.IO(hPrint,stderr)
import qualified Data.Map as Map
import qualified Data.IntMap as IMap

main :: IO ()
main =
  do txt <- getContents
     let mb = parseProgram Layout txt
     case mb of
       Left err -> hPrint stderr $ Parser.ppError err
       Right p  ->
         case removePatterns p of
           (p1,[])  ->
             tcProgram p1 inp >>= \res ->
             case res of
               InferOK ws _ prog ->
                  do mapM_ (print . TC.ppWarning IMap.empty) ws
                     print (pp prog)
               InferFailed ws errs ->
                  do mapM_ (print . TC.ppWarning IMap.empty) ws
                     mapM_ (print . TC.ppError IMap.empty) errs
           (_,errs) -> hPrint stderr $ vcat $ map pp errs

  where
  inp = InferInput { inpRange     = Range start start ""
                   , inpVars      = Map.empty
                   , inpTSyns     = Map.empty
                   , inpNameSeeds = nameSeeds
                   }





