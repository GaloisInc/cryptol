{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE MultiWayIf #-}

module Cryptol.TypeCheck.Solver.Simplify (
    Fins, filterFins,
    tryRewritePropAsSubst
  ) where


import Cryptol.Prims.Syntax (TFun(..))
import Cryptol.TypeCheck.AST (Type(..),Prop,TVar,pIsEq,isFreeTV,TCon(..),pIsFin)
import Cryptol.TypeCheck.InferTypes (Goal(..))
import Cryptol.TypeCheck.Subst (fvs)

import           Control.Monad (msum,guard,mzero)
import           Data.Function (on)
import           Data.List (sortBy)
import           Data.Maybe (catMaybes,listToMaybe)
import qualified Data.Set as Set


-- | Type variables that are known to have a `fin` constraint. This set is used
-- to justify the addition of a subtraction on the rhs of an equality
-- constraint.
type Fins = Set.Set TVar

filterFins :: [Goal] -> Fins
filterFins gs = Set.unions [ fvs ty | Goal { .. } <- gs
                                    , Just ty     <- [pIsFin goal] ]


-- | When given an equality constraint, attempt to rewrite it to the form `?x =
-- ...`, by moving all occurrences of `?x` to the LHS, and any other variables
-- to the RHS.  This will only work when there's only one unification variable
-- present in the prop.
tryRewritePropAsSubst :: Fins -> Prop -> Maybe (TVar,Type)
tryRewritePropAsSubst fins p =
  do (x,y) <- pIsEq p

     let vars = Set.toList (Set.filter isFreeTV (fvs p))

     listToMaybe $ sortBy (flip compare `on` rank)
                 $ catMaybes [ tryRewriteEq fins var x y | var <- vars ]


-- | Rank a rewrite.
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
-- form `?x = t`.
tryRewriteEq :: Fins -> TVar -> Type -> Type -> Maybe (TVar,Type)
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
allFin :: Fins -> Type -> Bool
allFin fins ty = fvs ty `Set.isSubsetOf` fins


-- | Rewrite an equality until the LHS is just uvar. Return the rewritten RHS.
rewriteLHS :: Fins -> TVar -> Type -> Type -> Maybe Type
rewriteLHS fins uvar = go
  where

  go (TVar tv) rhs | tv == uvar = return rhs

  go (TCon (TF tf) [x,y]) rhs =
    do let xfvs = fvs x
           yfvs = fvs y

           inX  = Set.member uvar xfvs
           inY  = Set.member uvar yfvs

       -- for now, don't handle the complicated case where the variable shows up
       -- multiple times in an expression
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
  balanceR x TCAdd y rhs = do guardSubtract y
                              go x (TCon (TF TCSub) [rhs,y])
  balanceR x TCSub y rhs = go x (TCon (TF TCAdd) [rhs,y])
  balanceR _ _     _ _   = mzero


  -- invert the type function to balance the equation, when the variable occurs
  -- on the RHS of the expression `x tf y`
  balanceL x TCAdd y rhs = do guardSubtract y
                              go y (TCon (TF TCSub) [rhs,x])
  balanceL x TCSub y rhs = go (TCon (TF TCAdd) [rhs,y]) x
  balanceL _ _     _ _   = mzero


  -- guard that it's OK to subtract this type from something else.
  --
  -- XXX this ignores things like `min x inf` where x is finite, and just
  -- assumes that it won't work.
  guardSubtract ty = guard (allFin fins ty)
