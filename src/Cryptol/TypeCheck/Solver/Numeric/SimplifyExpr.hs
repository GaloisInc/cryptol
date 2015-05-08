{-# LANGUAGE Safe, BangPatterns #-}
{- | Simplification of expressions.
The result of simplifying an expression `e`, is a new expression `e'`,
which satisfies the property:

    if e is well-defined then e and e' will evaluate to the same type.

-}
module Cryptol.TypeCheck.Solver.Numeric.SimplifyExpr where

import           Cryptol.TypeCheck.Solver.Numeric.AST
import qualified Cryptol.TypeCheck.Solver.InfNat as IN
import           Cryptol.Utils.Misc ( anyJust )

import           Control.Monad ( guard )
import           Data.Maybe ( fromMaybe, maybeToList )
import qualified Data.Map as Map


-- | Simplify an expression, if possible.
crySimpExpr :: Expr -> Expr
crySimpExpr expr = fromMaybe expr (crySimpExprMaybe expr)

-- | Perform simplification from the leaves up.
-- Returns `Nothing` if there were no changes.
crySimpExprMaybe :: Expr -> Maybe Expr
crySimpExprMaybe expr =
  case crySimpExprStep (fromMaybe expr mbE1) of
    Nothing -> mbE1
    Just e2 -> Just (fromMaybe e2 (crySimpExprMaybe e2))
  where
  mbE1 = cryRebuildExpr expr `fmap` anyJust crySimpExprMaybe (cryExprExprs expr)



-- XXX: Add rules to group together occurances of variables


data Sign = Pos | Neg deriving Show

otherSign :: Sign -> Sign
otherSign s = case s of
                Pos -> Neg
                Neg -> Pos

signed :: Sign -> Integer -> Integer
signed s = case s of
             Pos -> id
             Neg -> negate


splitSum :: Expr -> [(Sign,Expr)]
splitSum e0 = go Pos e0 []
  where go s (e1 :+ e2) es = go s e1 (go s e2 es)
        go s (e1 :- e2) es = go s e1 (go (otherSign s) e2 es)
        go s e es          = (s,e) : es

normSum :: Expr -> Expr
normSum = posTerm . go 0 Map.empty Nothing . splitSum
  where

  -- constants, variables, other terms
  go !_ !_  !_ ((Pos,K Inf) : _) = (Pos, K Inf)

  go k xs t ((s, K (Nat n)) : es) = go (k + signed s n) xs t es

  go k xs t ((s, Var x) : es) = go k (Map.insertWith (+) x (signed s 1) xs) t es

  go k xs t ((s, K (Nat n) :* Var x) : es)
    | n == 0     = go k xs t es
    | otherwise  = go k (Map.insertWith (+) x (signed s n) xs) t es

  go k xs Nothing (e : es) = go k xs (Just e) es

  go k xs (Just e1) (e2 : es) = go k xs (Just (add e1 e2)) es

  go k xs t [] =
    let terms     = constTerm k
                 ++ concatMap varTerm (Map.toList xs)
                 ++ maybeToList t

    in case terms of
         [] -> (Pos, K (Nat 0))
         ts -> foldr1 add ts

  constTerm k
    | k == 0    = []
    | k >  0    = [ (Pos, K (Nat k)) ]
    | otherwise = [ (Neg, K (Nat (negate k))) ]

  varTerm (x,k)
    | k == 0    = []
    | k == 1    = [ (Pos, Var x) ]
    | k > 0     = [ (Pos, K (Nat k) :* Var x) ]
    | k == (-1) = [ (Neg, Var x) ]
    | otherwise = [ (Neg, K (Nat (negate k)) :* Var x) ]

  add (s1,t1) (s2,t2) =
    case (s1,s2) of
      (Pos,Pos) -> (Pos, t1 :+ t2)
      (Pos,Neg) -> (Pos, t1 :- t2)
      (Neg,Pos) -> (Pos, t2 :- t1)
      (Neg,Neg) -> (Neg, t1 :+ t2)

  posTerm (Pos,x) = x
  posTerm (Neg,x) = K (Nat 0) :- x




crySimpExprStep :: Expr -> Maybe Expr
crySimpExprStep e =
  case crySimpExprStep1 e of
    Just e1 -> Just e1
    Nothing -> do let e1 = normSum e
                  guard (e /= e1)
                  return e1

-- | Make a simplification step, assuming the expression is well-formed.
crySimpExprStep1 :: Expr -> Maybe Expr
crySimpExprStep1 expr =
  case expr of
    K _                   -> Nothing
    Var _                 -> Nothing

    _ :+ _                -> Nothing
    _ :- _                -> Nothing

    x :* y ->
      case (x,y) of
        (K (Nat 0), _)    -> Just zero
        (K (Nat 1), _)    -> Just y
        (K a, K b)        -> Just (K (IN.nMul a b))
        (_,   K _)        -> Just (y :* x)

        (K a, K b :* z)   -> Just (K (IN.nMul a b) :* z)

        -- Normalize, somewhat
        (a :* b, _)       -> Just (a :* (b :* y))
        (Var a, Var b)
          | b > a         -> Just (y :* x)

        _                 -> Nothing

    Div x y ->
      case (x,y) of
        (K (Nat 0), _)    -> Just zero
        (_, K (Nat 1))    -> Just x
        (_, K Inf)        -> Just zero
        (K a, K b)        -> K `fmap` IN.nDiv a b
        _ | x == y        -> Just one
        _                 -> Nothing

    Mod x y ->
      case (x,y) of
        (K (Nat 0), _)    -> Just zero
        (_, K Inf)        -> Just x
        (_, K (Nat 1))    -> Just zero
        (K a, K b)        -> K `fmap` IN.nMod a b
        _                 -> Nothing

    x :^^ y ->
      case (x,y) of
        (_, K (Nat 0))    -> Just one
        (_, K (Nat 1))    -> Just x
        (K (Nat 1), _)    -> Just one
        (K a, K b)        -> Just (K (IN.nExp a b))
        _                 -> Nothing

    Min x y ->
      case (x,y) of
        (K (Nat 0), _)    -> Just zero
        (K Inf, _)        -> Just y
        (_, K (Nat 0))    -> Just zero
        (_, K Inf)        -> Just x
        (K a, K b)        -> Just (K (IN.nMin a b))
        _ | x == y        -> Just x
        _                 -> Nothing

    Max x y ->
      case (x,y) of
        (K (Nat 0), _)    -> Just y
        (K Inf, _)        -> Just inf
        (_, K (Nat 0))    -> Just x
        (_, K Inf)        -> Just inf
        _ | x == y        -> Just x
        _                 -> Nothing

    Lg2 x ->
      case x of
        K a               -> Just (K (IN.nLg2 a))
        K (Nat 2) :^^ e   -> Just e
        _                 -> Nothing

    -- Width x               -> Just (Lg2 (x :+ one))
    Width x ->
      case x of
        K a                           -> Just (K (IN.nWidth a))
        K (Nat 2) :^^ e               -> Just (one :+ e)
        K (Nat 2) :^^ e :- K (Nat 1)  -> Just e
        _                             -> Nothing

    LenFromThen x y w ->
      case (x,y,w) of
        (K a, K b, K c)   -> K `fmap` IN.nLenFromThen a b c
        _                 -> Nothing

    LenFromThenTo x y z ->
      case (x,y,z) of
        (K a, K b, K c)   -> K `fmap` IN.nLenFromThenTo a b c
        _                 -> Nothing



