{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE MultiWayIf #-}

module Cryptol.TypeCheck.Solver.Simplify (
    tryRewritePropAsSubst
  ) where


import Cryptol.Prims.Syntax (TFun(..))
import Cryptol.TypeCheck.AST (Type(..),Prop,TVar,pIsEq,isFreeTV,TCon(..))
import Cryptol.TypeCheck.Subst (fvs)

import           Control.Monad (msum,guard,mzero)
import qualified Data.Set as Set


-- | When given an equality constraint, attempt to rewrite it to the form `?x =
-- ...`, by moving all occurrences of `?x` to the LHS, and any other variables
-- to the RHS.  This will only work when there's only one unification variable
-- present in the prop.
tryRewritePropAsSubst :: Prop -> Maybe (TVar,Type)
tryRewritePropAsSubst p =
  do (x,y) <- pIsEq p

     -- extract the single unification variable from the prop (there can be
     -- bound variables remaining)
     let xfvs = fvs x
         yfvs = fvs y
         vars = Set.toList (Set.filter isFreeTV (Set.union xfvs yfvs))
     [uvar] <- return vars

     rhs <- msum [ simpleCase uvar x y yfvs
                 , simpleCase uvar y x xfvs
                 , oneSided   uvar x y yfvs
                 , oneSided   uvar y x xfvs
                 ]

     return (uvar,rhs)

  where

  -- Check for the case where l is a free variable, and the rhs doesn't mention
  -- it.
  simpleCase uvar l r rfvs =
    do guard (TVar uvar == l && uvar `Set.notMember` rfvs)
       return r

  -- Check for the case where the unification variable only occurs on one side
  -- of the constraint.
  oneSided uvar l r rfvs =
    do guard (uvar `Set.notMember` rfvs)
       rewriteLHS uvar l r

-- | Rewrite an equality until the LHS is just uvar. Return the rewritten RHS.
rewriteLHS :: TVar -> Type -> Type -> Maybe Type
rewriteLHS uvar = go
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
          | inX        -> applyR x tf y rhs
          | inY        -> applyL x tf y rhs


  -- discard type synonyms, the rewriting will make them no longer apply
  go (TUser _ _ l) rhs =
       go l rhs

  -- records won't work here.
  go _ _ =
       mzero


  -- invert the type function to balance the equation, when the variable occurs
  -- on the LHS of the expression `x tf y`
  applyR x TCAdd y rhs = go x (TCon (TF TCSub) [rhs,y])
  applyR x TCSub y rhs = go x (TCon (TF TCAdd) [rhs,y])
  applyR x TCMul y rhs = go x (TCon (TF TCDiv) [rhs,y])
  applyR x TCDiv y rhs = go x (TCon (TF TCMul) [rhs,y])
  applyR _ _     _ _   = mzero

  -- invert the type function to balance the equation, when the variable occurs
  -- on the RHS of the expression `x tf y`
  applyL x TCAdd y rhs = go y (TCon (TF TCSub) [rhs,x])
  applyL x TCMul y rhs = go y (TCon (TF TCDiv) [rhs,x])
  applyL x TCSub y rhs = go (TCon (TF TCAdd) [rhs,y]) x
  applyL x TCDiv y rhs = go (TCon (TF TCMul) [rhs,y]) x
  applyL _ _     _ _   = mzero
