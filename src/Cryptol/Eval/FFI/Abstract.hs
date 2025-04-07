-- | How to call foreign function, following the "abstract" calling convention
module Cryptol.Eval.FFI.Abstract where

import Cryptol.Utils.Panic(panic)
import Cryptol.ModuleSystem.Name(Name)
import Cryptol.TypeCheck.Type(Type(..), TVar(..))
import Cryptol.TypeCheck.FFI.FFIType
import Cryptol.Eval.FFI.ForeignSrc(ForeignImpl)
import Cryptol.Eval.Type(TypeEnv,evalType,evalNumType,finNat')
import Cryptol.Eval.Value
import Cryptol.Backend.Monad
import Cryptol.Backend.Concrete
import Cryptol.Eval.FFI.Abstract.Export(exportSizes,exportValues)
import Cryptol.Eval.FFI.Abstract.Call(runFFI)


-- | Call a foreign function that follows the "abstract" calling convetion.
callForeignAbstract ::
  Name                           {- ^ Name of foregin function -} ->
  FFIFunType Type                {- ^ FFI type -} ->
  ForeignImpl                    {- ^ Address of foreign worker -} ->
  TypeEnv                        {- ^ Values for numeric type parametres -} ->
  [(Type, GenValue Concrete)]    {- ^ Function arguments -} ->
  Eval (GenValue Concrete)
callForeignAbstract nm ty impl tenv args =
  case evalType tenv (ffiRetType ty) of
    Right resT ->
      do let targs = exportSizes (map evalFinType (ffiTParams ty)) []
         allArgs <- exportValues (map (pure . snd) args) targs
         mb <- io (runFFI allArgs resT impl)
         case mb of
           Right a -> a
           Left err -> raiseError Concrete (FFIImportError err)
    Left _ -> panic "callForeginAbstract" ["Result type is a number"]


   where
   evalFinType = finNat' . evalNumType tenv . TVar . TVBound


 