{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE Trustworthy #-}

module GitRev (hash, branch, dirty) where

import GitRev.TH

hash :: String
hash = $(getHash)

branch :: String
branch = $(getBranch)

dirty :: Bool
dirty = $(getDirty)
