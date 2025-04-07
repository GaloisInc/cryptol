-- | How to call foreign function, following the "abstract" calling convention
module Cryptol.Eval.FFI.Abstract where

import Cryptol.ModuleSystem.Name(Name)
import Cryptol.TypeCheck.Type(Type)
import Cryptol.TypeCheck.FFI.FFIType
import Cryptol.Eval.FFI.ForeignSrc(ForeignImpl(..))
import Cryptol.Eval.Type(TypeEnv,evalNumType,finNat', TValue(..))
import Cryptol.Eval.Value
import Cryptol.Backend.Monad
import Cryptol.Backend.Concrete

-- | Call a foreign function that follows the "abstract" calling convetion.
callForeignAbstract ::
  Name                           {- ^ Name of foregin function -} ->
  FFIFunType Type                {- ^ FFI type -} ->
  ForeignImpl                    {- ^ Address of foreign worker -} ->
  TypeEnv                        {- ^ Values for numeric type parametres -} ->
  [(Type, GenValue Concrete)]    {- ^ Function arguments -} ->
  Eval (GenValue Concrete)
callForeignAbstract nm ty impl tenv args = undefined
   where
   evalFinType = finNat' . evalNumType tenv


 