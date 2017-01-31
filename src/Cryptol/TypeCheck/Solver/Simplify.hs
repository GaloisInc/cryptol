-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2015-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE MultiWayIf #-}

module Cryptol.TypeCheck.Solver.Simplify (
    tryRewritePropAsSubst
  ) where


import Cryptol.TypeCheck.Type(Type(..),Prop,TVar,TCon(..),TFun(..)
                             ,pIsEq,isFreeTV,tAdd,tSub)
import Cryptol.TypeCheck.Solver.Numeric.Interval (Interval,iIsFin,typeInterval)
import Cryptol.TypeCheck.Subst (fvs)

import           Control.Monad (msum,guard,mzero)
import           Data.Function (on)
import           Data.List (sortBy)
import           Data.Maybe (catMaybes,listToMaybe)
import           Data.Map (Map)
import qualified Data.Set as Set


-- | When given an equality constraint, attempt to rewrite it to the form `?x =
-- ...`, by moving all occurrences of `?x` to the LHS, and any other variables
-- to the RHS.  This will only work when there's only one unification variable
-- present in the prop.
tryRewritePropAsSubst :: Map TVar Interval -> Prop -> Maybe (TVar,Type)
tryRewritePropAsSubst fins p =
  do (x,y) <- pIsEq p

     let vars = Set.toList (Set.filter isFreeTV (fvs p))

     listToMaybe $ sortBy (flip compare `on` rank)
                 $ catMaybes [ tryRewriteEq fins var x y | var <- vars ]


-- | Rank a rewrite, favoring expressions that have fewer subtractions than
-- additions.
rank :: (TVar,Type) -> Int
rank (_,ty) = go ty
  where

  go (TCon (TF TCAdd) ts) = sum (map go ts) + 1
  go (TCon (TF TCSub) ts) = sum (map go ts) - 1
  go (TCon (TF TCMul) ts) = sum (map go ts) + 1
  go (TCon (TF TCDiv) ts) = sum (map go ts) - 1
  go (TCon _          ts) = sum (map go ts)
  go _                    = 0


-- | Rewrite an equation with respect to a unification variable ?x, into the
-- form `?x = t`.  There are two interesting cases to consider (four with
-- symmetry):
--
--  * ?x = ty
--  * expr containing ?x = expr
--
-- In the first case, we just return the type variable and the type, but in the
-- second we try to rewrite the equation until it's in the form of the first
-- case.
tryRewriteEq :: Map TVar Interval -> TVar -> Type -> Type -> Maybe (TVar,Type)
tryRewriteEq fins uvar l r =
  msum [ do guard (uvarTy == l && uvar `Set.notMember` rfvs)
            return (uvar, r)

       , do guard (uvarTy == r && uvar `Set.notMember` lfvs)
            return (uvar, l)

       , do guard (uvar `Set.notMember` rfvs)
            ty <- rewriteLHS fins uvar l r
            return (uvar,ty)

       , do guard (uvar `Set.notMember` lfvs)
            ty <- rewriteLHS fins uvar r l
            return (uvar,ty)
       ]

  where

  uvarTy = TVar uvar

  lfvs   = fvs l
  rfvs   = fvs r


-- | Check that a type contains only finite type variables.
allFin :: Map TVar Interval -> Type -> Bool
allFin ints ty = iIsFin (typeInterval ints ty)


-- | Rewrite an equality until the LHS is just `uvar`. Return the rewritten RHS.
--
-- There are a few interesting cases when rewriting the equality:
--
--  A o B = R  when `uvar` is only present in A
--  A o B = R  when `uvar` is only present in B
--
-- In the first case, as we only consider addition and subtraction, the
-- rewriting will continue on the left, after moving the `B` side to the RHS of
-- the equation.  In the second case, if the operation is addition, the `A` side
-- will be moved to the RHS, with rewriting continuing in `B`. However, in the
-- case of subtraction, the `B` side is moved to the RHS, and rewriting
-- continues on the RHS instead.
--
-- In both cases, if the operation is addition, rewriting will only continue if
-- the operand being moved to the RHS is known to be finite. If this check was
-- not done, we would end up violating the well-definedness condition for
-- subtraction (for a, b: well defined (a - b) iff fin b).
rewriteLHS :: Map TVar Interval -> TVar -> Type -> Type -> Maybe Type
rewriteLHS fins uvar = go
  where

  go (TVar tv) rhs | tv == uvar = return rhs

  go (TCon (TF tf) [x,y]) rhs =
    do let xfvs = fvs x
           yfvs = fvs y

           inX  = Set.member uvar xfvs
           inY  = Set.member uvar yfvs

       if | inX && inY -> mzero
          | inX        -> balanceR x tf y rhs
          | inY        -> balanceL x tf y rhs
          | otherwise  -> mzero


  -- discard type synonyms, the rewriting will make them no longer apply
  go (TUser _ _ l) rhs =
       go l rhs

  -- records won't work here.
  go _ _ =
       mzero


  -- invert the type function to balance the equation, when the variable occurs
  -- on the LHS of the expression `x tf y`
  balanceR x TCAdd y rhs = do guardFin y
                              go x (tSub rhs y)
  balanceR x TCSub y rhs = go x (tAdd rhs y)
  balanceR _ _     _ _   = mzero


  -- invert the type function to balance the equation, when the variable occurs
  -- on the RHS of the expression `x tf y`
  balanceL x TCAdd y rhs = do guardFin y
                              go y (tSub rhs x)
  balanceL x TCSub y rhs = go (tAdd rhs y) x
  balanceL _ _     _ _   = mzero


  -- guard that the type is finite
  --
  -- XXX this ignores things like `min x inf` where x is finite, and just
  -- assumes that it won't work.
  guardFin ty = guard (allFin fins ty)
