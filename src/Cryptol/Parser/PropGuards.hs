-- |
-- Module      :  Cryptol.Parser.PropGuards
-- Copyright   :  (c) 2022 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Expands PropGuards into a top-level definition for each case, and rewrites
-- the body of each case to be an appropriate call to the respectively generated
-- function.
--

module Cryptol.Parser.PropGuards where

import Cryptol.Parser.AST
import Cryptol.Parser.Position (Range(..), emptyRange, start, at)
import Cryptol.Parser.Names (namesP)
import Cryptol.Utils.PP
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.RecordMap

import           MonadLib hiding (mapM)
import           Data.Maybe (maybeToList)
import qualified Data.Map as Map
import           Data.Text (Text)

import GHC.Generics (Generic)
import Control.DeepSeq

class ExpandPropGuards t where
  expandPropGuards :: t -> (t, [Error])
