{-# LANGUAGE Safe #-}
-- | Separate Non-Linear Constraints
--
-- TODO: When naming non-linear terms,
-- use the same name for the same expression.
module Cryptol.TypeCheck.Solver.Numeric.NonLin
  ( nonLinProp
  ) where

import Cryptol.TypeCheck.Solver.Numeric.AST
import Cryptol.Utils.Panic(panic)

import MonadLib


-- | Is the top-level operator a non-linear one.
isNonLinOp :: Expr -> Bool
isNonLinOp expr =
  case expr of
    K _   -> False
    Var _ -> False

    _ :+ _ -> False

    _ :- _ -> False

    x :* y ->
      case (x,y) of
        (K _, _)  -> False
        (_, K _)  -> False
        _         -> True

    Div _ y ->
      case y of
        K _       -> False
        _         -> True

    Mod _ y ->
      case y of
        K _       -> False
        _         -> True

    _ :^^ _       -> True

    Min _ _       -> False

    Max _ _       -> False

    Lg2 _         -> True

    Width _       -> True

    LenFromThen _ _ _ -> True -- See also comment on `LenFromThenTo`

    LenFromThenTo x y _ ->
      case (x,y) of
        (K _, K _) -> False
        _          -> True    -- Actually, as long as the difference bettwen
                              -- `x` and `y` is constant we'd be OK, but not
                              -- sure how to do that...


-- | Factor-out non-linear terms, by naming them
nonLinProp :: Int -> Prop -> ([(Name,Expr)], Prop, Int)
nonLinProp name prop = case runId $ runStateT s0 $ nonLinPropM prop of
                         (p, sFin) -> (nonLinExprs sFin, p, nextName sFin)
  where
  s0 = NonLinS { nextName = name, nonLinExprs = [] }


nonLinPropM :: Prop -> NonLinM Prop
nonLinPropM prop =
  case prop of
    PFalse      -> return PFalse
    PTrue       -> return PTrue
    Not p       -> Not   `fmap` nonLinPropM p
    p :&& q     -> (:&&) `fmap` nonLinPropM p `ap` nonLinPropM q
    p :|| q     -> (:||) `fmap` nonLinPropM p `ap` nonLinPropM q
    Fin (Var _) -> return prop
    Fin _       -> unexpected
    x :==: y    -> (:==:) `fmap` nonLinExprM x `ap` nonLinExprM y
    x :>: y     -> (:>:)  `fmap` nonLinExprM x `ap` nonLinExprM y

    _ :== _     -> unexpected
    _ :>= _     -> unexpected
    _ :> _      -> unexpected

  where
  unexpected = panic "nonLinPropM" [ show (ppProp prop) ]



nonLinExprM :: Expr -> NonLinM Expr
nonLinExprM expr
  | isNonLinOp expr = nameExpr expr
  | otherwise = cryRebuildExpr expr `fmap` mapM nonLinExprM (cryExprExprs expr)



type NonLinM = StateT NonLinS Id

data NonLinS = NonLinS
  { nextName    :: !Int
  , nonLinExprs :: [(Name,Expr)]
  }

nameExpr :: Expr -> NonLinM Expr
nameExpr e = sets $ \s ->
  case [ x | (x,e1) <- nonLinExprs s, e == e1 ] of    -- XXX: inefficient!
    x : _ -> (Var x,s)
    [] ->
      let x  = nextName s
          n  = sysName x
          s1 = NonLinS { nextName = 1 + x
                       , nonLinExprs = (n,e) : nonLinExprs s
                       }
      in s1 `seq` (Var n, s1)




