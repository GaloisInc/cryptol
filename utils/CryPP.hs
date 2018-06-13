#!/usr/bin/env runhaskell

-- |
-- Module      :  Main
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

import Cryptol.Parser
import Cryptol.Utils.PP(pp)

main :: IO ()
main =
  do txt <- getContents
     print (sh $ parseProgram Layout txt)

sh (Right a) = pp a
sh (Left a)  = ppError a

