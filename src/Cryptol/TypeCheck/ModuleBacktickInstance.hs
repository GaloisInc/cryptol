module Cryptol.TypeCheck.ModuleBacktickInstance where

import Data.Map(Map)
import qualified Data.Map as Map

import Cryptol.Parser.Position (Located(..), thing)
import qualified Cryptol.Parser.AST as P
import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Monad

-- | Rewrite declarations to add the given module parameters.
-- Assumes the renaming due to the instantiation has already happened.
doBacktickInstance ::
  [TParam] ->
  [Prop] ->
  Map Name Type ->
  ModuleG name ->
  InferM (ModuleG name)
doBacktickInstance = undefined
