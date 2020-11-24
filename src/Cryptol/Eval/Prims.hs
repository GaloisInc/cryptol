{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
module Cryptol.Eval.Prims where

import Cryptol.Backend
import Cryptol.Eval.Type
import Cryptol.Eval.Value
import Cryptol.ModuleSystem.Name
import Cryptol.Parser.Position
import Cryptol.TypeCheck.Solver.InfNat(Nat'(..))
import Cryptol.Utils.Panic

data Prim sym
  = PFun (SEval sym (GenValue sym) -> Prim sym)
  | PStrict (GenValue sym -> Prim sym)
  | PWordFun (SWord sym -> Prim sym)
  | PFloatFun (SFloat sym -> Prim sym)
  | PTyPoly (TValue -> Prim sym)
  | PNumPoly (Nat' -> Prim sym)
  | PFinPoly (Integer -> Prim sym)
  | PRange (Range -> Prim sym)
  | PPrim (SEval sym (GenValue sym))
  | PVal (GenValue sym)

evalPrim :: (?range :: Range, Backend sym) => sym -> Name -> Prim sym -> SEval sym (GenValue sym)
evalPrim sym nm p = case p of
  PFun f      -> pure (lam (evalPrim sym nm . f))
  PStrict f   -> pure (lam (\x -> evalPrim sym nm . f =<< x))
  PWordFun f  -> pure (lam (\x -> evalPrim sym nm . f =<< (fromVWord sym (show nm) =<< x)))
  PFloatFun f -> pure (flam (evalPrim sym nm . f))
  PTyPoly f   -> pure (VPoly (evalPrim sym nm . f))
  PNumPoly f  -> pure (VNumPoly (evalPrim sym nm . f))
  PFinPoly f  -> pure (VNumPoly (\case Inf -> panic "PFin" ["Unexpected `inf`", show nm];
                                        Nat n -> evalPrim sym nm (f n)))
  PRange f    -> evalPrim sym nm (f ?range)
  PPrim m     -> m
  PVal v      -> pure v
