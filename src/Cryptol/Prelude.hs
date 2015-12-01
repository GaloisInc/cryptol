-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Compile the prelude into the executable as a last resort

{-# LANGUAGE CPP #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}

module Cryptol.Prelude (writePreludeContents) where

import Cryptol.ModuleSystem.Monad

import System.Directory (getTemporaryDirectory)
import System.IO (hClose, hPutStr, openTempFile)
import Text.Heredoc (there)

preludeContents :: String
preludeContents = [there|lib/Cryptol.cry|]

-- | Write the contents of the Prelude to a temporary file so that
-- Cryptol can load the module.
writePreludeContents :: ModuleM FilePath
writePreludeContents = io $ do
  tmpdir <- getTemporaryDirectory
  (path, h) <- openTempFile tmpdir "Cryptol.cry"
  hPutStr h preludeContents
  hClose h
  putStrLn $ "Wrote Prelude to " ++ path
  return path
