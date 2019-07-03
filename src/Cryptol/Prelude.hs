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

module Cryptol.Prelude (
  writePreludeContents,
  cryptolTcContents
  ) where

import System.Directory (getTemporaryDirectory)
import System.IO (hClose, hPutStr, openTempFile)
import Text.Heredoc (there)

preludeContents :: String
preludeContents = [there|lib/Cryptol.cry|]

-- | Write the contents of the Prelude to a temporary file so that
-- Cryptol can load the module.
writePreludeContents :: IO FilePath
writePreludeContents = do
  tmpdir <- getTemporaryDirectory
  (path, h) <- openTempFile tmpdir "Cryptol.cry"
  hPutStr h preludeContents
  hClose h
  return path

cryptolTcContents :: String
cryptolTcContents = [there|lib/CryptolTC.z3|]


