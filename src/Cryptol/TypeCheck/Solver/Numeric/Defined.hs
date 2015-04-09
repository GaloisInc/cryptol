{-# LANGUAGE Safe #-}
module Cryptol.TypeCheck.Solver.Numeric.Defined where

import Cryptol.TypeCheck.Solver.Numeric.AST
import Cryptol.Utils.Panic ( panic )

-- | A condition ensure that the given *basic* proposition makes sense.
cryDefinedProp :: Prop -> Prop
cryDefinedProp prop =
  case prop of
    Fin x   -> cryDefined x
    x :== y -> cryDefined x :&& cryDefined y
    x :>= y -> cryDefined x :&& cryDefined y
    _ -> panic "cryDefinedProp" [ "Not a simple property:"
                                , show (ppProp prop)
                                ]


-- | Generate a property ensuring that the expression is well-defined.
-- This might be a bit too strict.  For example, we reject things like
-- @max inf (0 - 1)@, which one might think would simplify to @inf@.
cryDefined :: Expr -> Prop
cryDefined expr =
  case expr of
    K _       -> PTrue
    Var _     -> PTrue    -- Variables are always assumed to be OK.
                      -- The idea is that we are going to check for
                      -- defined-ness before instantiating variables.
    x :+ y    -> cryDefined x :&& cryDefined y
    x :- y    -> cryDefined x :&& cryDefined y :&&
                 Fin y :&& x :>= y
    x :* y    -> cryDefined x :&& cryDefined y
    Div x y   -> cryDefined x :&& cryDefined y :&&
                 Fin x :&& y :>= K (Nat 1)
    Mod x y   -> cryDefined x :&& cryDefined y :&&
                 Fin x :&& y :>= K (Nat 1)
    x :^^ y   -> cryDefined x :&& cryDefined y
    Min x y   -> cryDefined x :&& cryDefined y
    Max x y   -> cryDefined x :&& cryDefined y
    Lg2 x     -> cryDefined x
    Width x   -> cryDefined x
    LenFromThen x y w ->
      cryDefined x :&& cryDefined y :&& cryDefined w :&&
      Fin x :&& Fin y :&& Fin w :&& Not (x :== y) :&& w :>= Width x
    LenFromThenTo x y z ->
      cryDefined x :&& cryDefined y :&& cryDefined z :&&
      Fin x :&& Fin y :&& Fin z :&& Not (x :== y)



