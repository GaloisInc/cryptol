-- |
-- Module      :  Cryptol.Version
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Trustworthy #-}

module Cryptol.Version (
    commitHash
  , commitShortHash
  , commitBranch
  , commitDirty
  , version
  , displayVersion
  ) where

import Paths_cryptol
import qualified GitRev
import Data.Version (showVersion)

commitHash :: String
commitHash = GitRev.hash

commitShortHash :: String
commitShortHash = take 7 GitRev.hash

commitBranch :: String
commitBranch = GitRev.branch

commitDirty :: Bool
commitDirty = GitRev.dirty

displayVersion :: Monad m => (String -> m ()) -> m ()
displayVersion putLn = do
    let ver = showVersion version
    putLn ("Cryptol " ++ ver)
    putLn ("Git commit " ++ commitHash)
    putLn ("    branch " ++ commitBranch ++ dirtyLab)
      where
      dirtyLab | commitDirty = " (non-committed files present during build)"
               | otherwise   = ""
