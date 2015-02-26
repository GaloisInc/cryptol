-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE Safe #-}
module Cryptol.TypeCheck.Defaulting where

import Cryptol.Parser.Position(Range)
import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.InferTypes
          (Solved(..),Goal(..),ConstraintSource(..), Warning(..))
import Cryptol.TypeCheck.Solver.Eval (assumedOrderModel,simpType)
import Cryptol.TypeCheck.Solver.FinOrd(noFacts,OrdFacts,ordFactsToGoals)
import Cryptol.TypeCheck.Solver.Numeric(numericStep,goalOrderModel)
import Cryptol.TypeCheck.Subst
  (Subst,apSubst,listSubst,fvs,emptySubst,singleSubst)
import Cryptol.Utils.Panic(panic)

import Control.Monad(guard,msum)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List(nubBy)
import Data.Maybe(fromMaybe)





--------------------------------------------------------------------------------
-- This is used when we just want to instantiate things in the REPL.

-- | Try to pick a reasonable instantiation for an expression, with
-- the given type.  This is useful when we do evaluation at the REPL.
-- The resaulting types should satisfy the constraints of the schema.
defaultExpr :: Range -> Expr -> Schema -> Maybe ([(TParam,Type)], Expr)
defaultExpr r e s =
  do let vs = sVars s
     guard $ all (\v -> kindOf v == KNum) vs  -- only defautl numerics.
     ps <- simplify [] $ map toGoal $ sProps s
     soln <- go [] vs ps
     tys  <- mapM (`lookup` soln) vs
     return (soln, foldl (\e1 _ -> EProofApp e1) (foldl ETApp e tys) (sProps s))

  where
  candidate :: Goal -> Maybe (TVar,Integer)
  candidate p = do (t1,t2) <- pIsGeq $ simpType noFacts $ goal p
                   a <- tIsVar t1
                   n <- tIsNum t2
                   return (a,n)

  go done [] [] = return done
  go done ts [] = return (done ++ [ (tp, tNum (0::Integer)) | tp <- ts ])
  go _    [] _  = Nothing

  go done as@(tp0:_) ps =
    do let (a,n) = fromMaybe (tpVar tp0, 0) $ msum (map candidate ps)
       -- If no candidate works, we try to set the variable to 0
       -- This handles a case when all we have letft are fin constraints.

       (tp,tps) <- getParam a as
       let ty = tNum n
           su = singleSubst a ty
       ps1 <- simplify [] (apSubst su ps)
       go ((tp,ty) : done) tps ps1

  getParam _ [] = Nothing
  getParam v (tp : tps)
    | tpVar tp == v = Just (tp,tps)
    | otherwise     = do (a,more) <- getParam v tps
                         return (a,tp:more)

  simplify done [] = return done
  simplify done (p : ps) =
    case assumedOrderModel noFacts $ map goal (done ++ ps) of
      Left _      -> Nothing
      Right (m,_) ->
        case numericStep m p of
          Solved Nothing ps1   -> simplify done (ps1 ++ ps)
          Solved (Just su) ps1 ->
            simplify [] (ps1 ++ apSubst su done ++ apSubst su ps)
          Unsolved -> simplify (p : done) ps
          Unsolvable -> Nothing

  toGoal p = Goal { goal       = p
                  , goalSource = CtDefaulting
                  , goalRange  = r
                  }

