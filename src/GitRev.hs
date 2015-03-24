-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2014-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Include information about the current git status for use in error
-- messages and version info output

{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE Trustworthy #-}

module GitRev (hash, branch, dirty) where

import Development.GitRev

hash :: String
hash = $(gitHash)

branch :: String
branch = $(gitBranch)

dirty :: Bool
dirty = $(gitDirty)
