{-# Language BlockArguments #-}
{-# Language OverloadedStrings #-}
-- | Concrete evaluations for floating point primitives.
module Cryptol.Eval.Concrete.Float where

import Data.Map(Map)
import qualified Data.Map as Map
import LibBF

import Cryptol.Eval.Value(GenValue(..),nlam)
import Cryptol.Eval.Concrete.Value
import Cryptol.Utils.Ident(Ident, floatPrimIdent)

floatPrims :: Map Ident Value
floatPrims = Map.fromList [ (floatPrimIdent i,v) | (i,v) <- table ]
  where
  table =
    [ ("fpNaN", nlam \_ -> nlam \_ -> VFloat bfNaN)
    ]



