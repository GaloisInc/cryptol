-- |
-- Module      :  Cryptol.Version
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE CPP  #-}

module Cryptol.Version (
    commitHash
  , commitShortHash
  , commitBranch
  , commitDirty
  , ffiEnabled
  , version
  , displayVersion
  , displayVersionStr
  ) where

import Paths_cryptol
import qualified GitRev
import Data.List (intercalate)
import Data.Version (showVersion)
import Control.Monad (when)
import Control.Monad.Writer (MonadWriter(..), Writer, execWriter)

commitHash :: String
commitHash = GitRev.hash

commitShortHash :: String
commitShortHash = take 7 GitRev.hash

commitBranch :: String
commitBranch = GitRev.branch

commitDirty :: Bool
commitDirty = GitRev.dirty

ffiEnabled :: Bool
#ifdef FFI_ENABLED
ffiEnabled = True
#else
ffiEnabled = False
#endif

displayVersion :: Monad m => (String -> m ()) -> m ()
displayVersion putLn = do
    let ver = showVersion version
    putLn ("Cryptol " ++ ver)
    putLn ("Git commit " ++ commitHash)
    putLn ("    branch " ++ commitBranch ++ dirtyLab)
    when ffiEnabled $ putLn "FFI enabled"
      where
      dirtyLab | commitDirty = " (non-committed files present during build)"
               | otherwise   = ""

-- | A pure version of 'displayVersion' that renders the displayed version
-- directly to a 'String'.
displayVersionStr :: String
displayVersionStr = intercalate "\n" $ execWriter $ displayVersion putLn
  where
    putLn :: String -> Writer [String] ()
    putLn str = tell [str]
