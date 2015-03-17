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
