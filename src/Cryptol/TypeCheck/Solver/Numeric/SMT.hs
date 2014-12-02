{-# LANGUAGE Safe #-}
-- | Desugar into SMTLIB Terminology
module Cryptol.TypeCheck.Solver.Numeric.SMT
  ( desugarProp
  , smtName
  , smtFinName
  , ifPropToSmtLib
  , cryGetModel
  , cryImproveModel
  ) where

import           Cryptol.TypeCheck.Solver.InfNat
import           Cryptol.TypeCheck.Solver.Numeric.AST
import           Cryptol.Utils.Panic ( panic )

import           Control.Monad ( ap, guard )
import           Data.Map ( Map )
import qualified Data.Map as Map
import           Data.Ratio ( (%), denominator, numerator )
import           SimpleSMT ( SExpr )
import qualified SimpleSMT as SMT


-- XXX: Expanding the if-then-elses could make things large.
-- Perhaps keep them as first class things, in hope that the solver
-- can do something more clever with that?


-- | Assumes simplified, linear, finite, defined expressions.
desugarExpr :: Expr -> IfExpr Expr
desugarExpr expr =
  do es <- mapM desugarExpr (cryExprExprs expr)
     case (expr,es) of
       (Min {}, [x,y]) -> If (x :>: y) (return y) (return x)
       (Max {}, [x,y]) -> If (x :>: y) (return x) (return y)
       (LenFromThenTo {}, [ x@(K (Nat a)), K (Nat b), z ])
          | a > b -> If (z :>: x) (return zero)
                                  (return (Div (z :- x) step :+ one))
          | b < a -> If (x :>: z) (return zero)
                                  (return (Div (x :- z) step :+ one))

          where step = K (Nat (abs (a - b)))

       _ -> return (cryRebuildExpr expr es)


-- | Assumes simplified, linear, defined.
desugarProp :: Prop -> IfExpr Prop
desugarProp prop =
  case prop of
    PFalse      -> return PFalse
    PTrue       -> return PTrue
    Not p       -> Not   `fmap` desugarProp p
    p :&& q     -> (:&&) `fmap` desugarProp p `ap` desugarProp q
    p :|| q     -> (:||) `fmap` desugarProp p `ap` desugarProp q
    Fin (Var _) -> return prop
    Fin _       -> unexpected
    x :==: y    -> (:==:) `fmap` desugarExpr x `ap` desugarExpr y
    x :>: y     -> (:>:)  `fmap` desugarExpr x `ap` desugarExpr y

    _ :== _   -> unexpected
    _ :>= _   -> unexpected
    _ :> _    -> unexpected

  where
  unexpected = panic "desugarProp" [ show (ppProp prop) ]


ifPropToSmtLib :: IfExpr Prop -> SExpr
ifPropToSmtLib ifProp =
  case ifProp of
    Impossible -> SMT.bool False -- Sholdn't really matter
    Return p   -> propToSmtLib p
    If p q r   -> SMT.ite (propToSmtLib p) (ifPropToSmtLib q) (ifPropToSmtLib r)

propToSmtLib :: Prop -> SExpr
propToSmtLib prop =
  case prop of
    PFalse      -> SMT.bool False
    PTrue       -> SMT.bool True
    Not p       -> SMT.not (propToSmtLib p)
    p :&& q     -> SMT.and (propToSmtLib p) (propToSmtLib q)
    p :|| q     -> SMT.or  (propToSmtLib p) (propToSmtLib q)
    Fin (Var x) -> SMT.const (smtFinName x)
    x :==: y    -> SMT.eq (exprToSmtLib x) (exprToSmtLib y)
    x :>: y     -> SMT.gt (exprToSmtLib x) (exprToSmtLib y)

    Fin _       -> unexpected
    _ :== _     -> unexpected
    _ :>= _     -> unexpected
    _ :> _      -> unexpected

  where
  unexpected = panic "desugarProp" [ show (ppProp prop) ]


exprToSmtLib :: Expr -> SExpr
exprToSmtLib expr =

  case expr of
    K (Nat n)           -> SMT.int n
    K Inf               -> unexpected
    Var a               -> SMT.const (smtName a)
    x :+ y              -> SMT.add (exprToSmtLib x) (exprToSmtLib y)
    x :- y              -> SMT.sub (exprToSmtLib x) (exprToSmtLib y)
    x :* y              -> SMT.mul (exprToSmtLib x) (exprToSmtLib y)
    Div x y             -> SMT.div (exprToSmtLib x) (exprToSmtLib y)
    Mod x y             -> SMT.mod (exprToSmtLib x) (exprToSmtLib y)
    _ :^^ _             -> unexpected
    Min {}              -> unexpected
    Max {}              -> unexpected
    Lg2 {}              -> unexpected
    Width {}            -> unexpected
    LenFromThen {}      -> unexpected
    LenFromThenTo {}    -> unexpected

  where
  unexpected = panic "exprToSmtLib" [ show (ppExpr expr) ]


-- | The name of a variable in the SMT translation.
smtName :: Name -> String
smtName = show . ppName

-- | The name of a boolean variable, representing `fin x`.
smtFinName :: Name -> String
smtFinName x = "fin_" ++ show (ppName x)






-- | Is this the only possible value for the constant, under the current
-- assumptions.
-- Assumes that we are in a 'Sat' state.
cryMustEqualK :: SMT.Solver -> Name -> Expr -> IO Bool
cryMustEqualK solver x expr =
  case expr of
    K Inf     -> do SMT.push solver
                    SMT.assert solver $ SMT.const (smtFinName x)
                    res <- SMT.check solver
                    SMT.pop solver
                    return (res == SMT.Unsat)
    K (Nat n) -> do SMT.push solver
                    SMT.assert solver $
                      SMT.not $
                      SMT.and
                        (SMT.const $ smtFinName x)
                        (SMT.eq (SMT.const (smtName x)) (SMT.int n))
                    res <- SMT.check solver
                    SMT.pop solver
                    return (res == SMT.Unsat)
    _ -> panic "cryMustEqualK" [ "Not a constant", show (ppExpr expr) ]


-- | Do these two variables need to always be the same, under the current
-- assumptions.
-- Assumes that we are in a 'Sat' state.
cryMustEqualV :: SMT.Solver -> Name -> Name -> IO Bool
cryMustEqualV solver x y =
  do SMT.push solver
     let fin a = SMT.const (smtFinName a)
         var a = SMT.const (smtName a)
     SMT.assert solver $
        SMT.or (SMT.not (fin x) `SMT.and` SMT.not (fin y))
               (fin x `SMT.and` fin y `SMT.and` SMT.eq (var x) (var y))
     res <- SMT.check solver
     SMT.pop solver
     return (res == SMT.Unsat)

-- | Compute a linear relation through two concrete points.
-- Try to find a relation of the form `y = a * x + b`, where both `a` and `b`
-- are naturals.
linRel :: Name -> Name -> (Integer,Integer) -> (Integer,Integer) -> Maybe Prop
linRel x y (x1,y1) (x2,y2) =
  do guard (x1 /= x2)
     let a' = (y1 - y2) % abs (x1 - x2)
     guard (denominator a' == 1)
     let a = numerator a'
         b = y1 - a * x1
     undefined x y a b"XXX: Finish this, rewriting equations to work with Nats"



-- | Given a model, compute a set of equations of the form `x = e`,
-- that are impleied by the model.
cryImproveModel :: SMT.Solver -> Map Name Expr -> IO (Map Name Expr)
cryImproveModel solver m = go Map.empty (Map.toList m)
  where
  go done [] = return done
  go done ((x,e) : rest) =
    do yesK <- cryMustEqualK solver x e
       if yesK
         then go (Map.insert x e done) rest
         else goV done [] x e rest

  goV done todo x e ((y,e') : more)
    | e == e' = do yesK <- cryMustEqualV solver x y
                   if yesK then goV (Map.insert x (Var y) done) todo x e more
                           else goV done ((y,e'):todo) x e more
    | otherwise = goV done ((y,e') : todo) x e more
  goV done todo _ _ [] = go done todo


-- | Extract the values of the given variables.
-- Assumes that we are in a 'Sat' state.
cryGetModel :: SMT.Solver -> [Name] -> IO (Map Name Expr)
cryGetModel p = fmap Map.fromList . mapM getVal
  where
  getVal a =
    do yes <- isInf a
       if yes then return (a, K Inf)
              else do v <- SMT.getConst p (smtName a)
                      case v of
                        SMT.Int x | x >= 0 -> return (a, K (Nat x))
                        _ -> panic "cryCheck.getVal"
                                [ "Not a natural number", show v ]

  isInf a = do yes <- SMT.getConst p (smtFinName a)
               case yes of
                 SMT.Bool ans -> return (not ans)
                 _            -> panic "cryCheck.isInf"
                                       [ "Not a boolean value", show yes ]




