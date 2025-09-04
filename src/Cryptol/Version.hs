-- |
-- Module      :  Cryptol.Version
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE CPP  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

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

import Control.Monad (when)
import Control.Monad.Writer (MonadWriter(..), Writer, execWriter)
import qualified Data.Aeson as Aeson
import qualified Data.Aeson.KeyMap as KeyMap
import qualified Data.ByteString as BS
import Data.FileEmbed (embedFileRelative)
import Data.List (intercalate)
import qualified Data.Text as Text
import Data.Version (showVersion)
import qualified GitRev
import Paths_cryptol

commitHash :: String
commitHash
  | hash /= unknown =
      hash
  -- See Note [cryptol.buildinfo.json]
  | Just buildinfoVal <- Aeson.decodeStrict buildinfo
  , Just (Aeson.String buildinfoHash) <- KeyMap.lookup "hash" buildinfoVal =
      Text.unpack buildinfoHash
  | otherwise =
      unknown
 where
  hash = GitRev.hash

commitShortHash :: String
commitShortHash = take 7 GitRev.hash

commitBranch :: String
commitBranch
  | branch /= unknown =
      branch
  -- See Note [cryptol.buildinfo.json]
  | Just buildinfoVal <- Aeson.decodeStrict buildinfo
  , Just (Aeson.String buildinfoCommit) <- KeyMap.lookup "branch" buildinfoVal =
      Text.unpack buildinfoCommit
  | otherwise =
      unknown
 where
  branch = GitRev.branch

commitDirty :: Bool
commitDirty
  | dirty =
      dirty
  -- See Note [cryptol.buildinfo.json]
  | Just buildinfoVal <- Aeson.decodeStrict buildinfo
  , Just (Aeson.Bool buildinfoDirty) <- KeyMap.lookup "dirty" buildinfoVal =
      buildinfoDirty
  | otherwise =
      False
 where
  dirty = GitRev.dirty

-- Helper, not exported
--
-- What to report if we are unable to determine git-related information. This
-- intentionally matches what the @gitrev@ library prints in such a scenario.
unknown :: String
unknown = "UNKNOWN"

-- Helper, not exported
--
-- See Note [cryptol.buildinfo.json]
buildinfo :: BS.ByteString
buildinfo = $(embedFileRelative "cryptol.buildinfo.json")

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

{-
Note [cryptol.buildinfo.json]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
By default, we determine the git commit hash, branch, and dirty information
using the gitrev library, which invokes git at compile time to query the
relevant information in the .git subdirectory. This works well for local
developments where the git binary and the .git subdirectory are both readily
available. It does not work so well for building in a Docker image, as we
intentionally do not copy over the .git subdirectory into the image to prevent
spurious cache invalidations caused by the contents of .git changing (which
they do, quite often).

As an alternative to gitrev, we also employ a convention where a build system
can create a cryptol.buildinfo.json file locally which contains the necessary
git-related information. The schema for this file is:

  {
    "hash": <string>,
    "branch": <string>,
    "dirty": <bool>
  }

This way, a build system (which has access to git/.git) can write this
information to a file, proceed to build the Docker image (which does not have
access to git/.git), and then have all of the expected information embedded
into the output of --version.
-}
