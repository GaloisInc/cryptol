-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe #-}

module Cryptol.Version where

import qualified GitRev

commitHash :: String
commitHash = GitRev.hash

commitShortHash :: String
commitShortHash = take 7 GitRev.hash

commitBranch :: String
commitBranch = GitRev.branch

commitDirty :: Bool
commitDirty = GitRev.dirty
