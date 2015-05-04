#!/usr/bin/env runhaskell

-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
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

