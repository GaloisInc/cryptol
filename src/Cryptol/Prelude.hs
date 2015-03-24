-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Include the prelude when building with -fself-contained

{-# LANGUAGE CPP #-}
{-# LANGUAGE QuasiQuotes #-}

module Cryptol.Prelude (writePreludeContents) where

import Cryptol.ModuleSystem.Monad

#ifdef SELF_CONTAINED

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
  return path

#else

import Cryptol.Parser.AST as P

-- | If we're not self-contained, the Prelude is just missing
writePreludeContents :: ModuleM FilePath
writePreludeContents = moduleNotFound (P.ModName ["Cryptol"]) =<< getSearchPath

#endif
