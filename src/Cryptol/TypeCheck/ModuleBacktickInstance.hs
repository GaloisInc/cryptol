module Cryptol.TypeCheck.ModuleBacktickInstance where

import Data.Map(Map)
import qualified Data.Map as Map

import Cryptol.Parser.Position (Located(..), thing)
import qualified Cryptol.Parser.AST as P
import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Monad

doBacktickInstance ::
  Located (P.ImpName Name)    {- ^ Name for the new module -} ->
  ModuleG ()                  {- ^ The functor -} ->
  Map Name Name {- ^ The instantiation: functor name -> instance name -} ->
  InferM (ModuleG (Located (P.ImpName Name)))
doBacktickInstance m mf inst = undefined
