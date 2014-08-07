---------------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Internals
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Low level functions to access the SBV infrastructure, for developers who
-- want to build further tools on top of SBV. End-users of the library
-- should not need to use this module.
---------------------------------------------------------------------------------

module Data.SBV.Internals (
  -- * Running symbolic programs /manually/
  Result, SBVRunMode(..), runSymbolic, runSymbolic'
  -- * Other internal structures useful for low-level programming
  , SBV(..), slet, CW(..), Kind(..), CWVal(..), AlgReal(..), mkConstCW, genVar, genVar_
  , liftQRem, liftDMod
  -- * Compilation to C
  , mkUninterpreted, compileToC', compileToCLib', CgPgmBundle(..), CgPgmKind(..)
  ) where

import Data.SBV.BitVectors.Data   (Result, SBVRunMode(..), runSymbolic, runSymbolic', SBV(..), CW(..), Kind(..), CWVal(..), AlgReal(..), mkConstCW)
import Data.SBV.BitVectors.Model  (genVar, genVar_, slet, liftQRem, liftDMod, mkUninterpreted)
import Data.SBV.Compilers.C       (compileToC', compileToCLib')
import Data.SBV.Compilers.CodeGen (CgPgmBundle(..), CgPgmKind(..))
