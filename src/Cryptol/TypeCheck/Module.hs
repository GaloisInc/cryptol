module Cryptol.TypeCheck.Module where

import Data.Map(Map)
import qualified Data.Map as Map

import Cryptol.Utils.Panic(xxxTODO)
import Cryptol.Parser.Position (Located, thing)
import qualified Cryptol.Parser.AST as P
import Cryptol.ModuleSystem.Exports(exportedDecls)
import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Monad


doFunctorInst ::
  Located (P.ImpName Name)    {- ^ Functor being instantiation -} ->
  P.ModuleInstanceArgs Name   {- ^ Instance arguments -} ->
  Map Name Name               {- ^ Basic instantiation -} ->
  InferM ()
doFunctorInst f as inst = xxxTODO "functor instance"




