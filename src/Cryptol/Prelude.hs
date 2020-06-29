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
  , floatContents
  , arrayContents
  , cryptolTcContents
  ) where

import Data.ByteString(ByteString)
import qualified Data.ByteString.Char8 as B
import Text.Heredoc (there)


preludeContents :: ByteString
preludeContents = B.pack [there|lib/Cryptol.cry|]

floatContents :: ByteString
floatContents = B.pack [there|lib/Float.cry|]

arrayContents :: ByteString
arrayContents = B.pack [there|lib/Array.cry|]

cryptolTcContents :: String
cryptolTcContents = [there|lib/CryptolTC.z3|]
