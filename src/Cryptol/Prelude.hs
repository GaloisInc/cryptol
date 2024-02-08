-- |
-- Module      :  Cryptol.Prelude
-- Copyright   :  (c) 2015-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Compile the prelude into the executable as a last resort

{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Cryptol.Prelude
  ( preludeContents
  , preludeReferenceContents
  , floatContents
  , arrayContents
  , suiteBContents
  , primeECContents
  , cryptolTcContents
  ) where

import Data.ByteString (ByteString)
import Data.FileEmbed (embedFileRelative)
import qualified Data.ByteString.Char8 as B

preludeContents :: ByteString
preludeContents = $(embedFileRelative "lib/Cryptol.cry")

preludeReferenceContents :: ByteString
preludeReferenceContents = $(embedFileRelative "lib/Cryptol/Reference.cry")

floatContents :: ByteString
floatContents = $(embedFileRelative "lib/Float.cry")

arrayContents :: ByteString
arrayContents = $(embedFileRelative "lib/Array.cry")

suiteBContents :: ByteString
suiteBContents = $(embedFileRelative "lib/SuiteB.cry")

primeECContents :: ByteString
primeECContents = $(embedFileRelative "lib/PrimeEC.cry")

cryptolTcContents :: String
cryptolTcContents = B.unpack $(embedFileRelative "lib/CryptolTC.z3")
