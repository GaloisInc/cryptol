-- |
-- Module      :  Cryptol.Prelude
-- Copyright   :  (c) 2015-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Compile the prelude into the executable as a last resort

{-# LANGUAGE Safe #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}

module Cryptol.Prelude
  ( preludeContents
  , preludeReferenceContents
  , floatContents
  , arrayContents
  , suiteBContents
  , primeECContents
  , cryptolTcContents
  ) where

import Data.ByteString(ByteString)
import qualified Data.ByteString.Char8 as B
import Text.Heredoc (there)


preludeContents :: ByteString
preludeContents = B.pack [there|lib/Cryptol.cry|]

preludeReferenceContents :: ByteString
preludeReferenceContents = B.pack [there|lib/Cryptol/Reference.cry|]

floatContents :: ByteString
floatContents = B.pack [there|lib/Float.cry|]

arrayContents :: ByteString
arrayContents = B.pack [there|lib/Array.cry|]

suiteBContents :: ByteString
suiteBContents = B.pack [there|lib/SuiteB.cry|]

primeECContents :: ByteString
primeECContents = B.pack [there|lib/PrimeEC.cry|]

cryptolTcContents :: String
cryptolTcContents = [there|lib/CryptolTC.z3|]
