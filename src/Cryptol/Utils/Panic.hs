-- |
-- Module      :  Cryptol.Utils.Panic
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Trustworthy, TemplateHaskell #-}
module Cryptol.Utils.Panic
  (HasCallStack, CryptolPanic, Cryptol, Panic, panic, xxxTODO) where

import Panic hiding (panic)
import qualified Panic as Panic

data Cryptol = Cryptol

type CryptolPanic = Panic Cryptol

panic :: HasCallStack => String -> [String] -> a
panic = Panic.panic Cryptol

xxxTODO :: HasCallStack => String -> a
xxxTODO x = panic "TODO" [x]

instance PanicComponent Cryptol where
  panicComponentName _ = "Cryptol"
  panicComponentIssues _ = "https://github.com/GaloisInc/cryptol/issues"

  {-# Noinline panicComponentRevision #-}
  panicComponentRevision = $useGitRevision


