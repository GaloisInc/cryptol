-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE PatternGuards, BangPatterns #-}
{-# LANGUAGE Safe #-}
module Cryptol.TypeCheck.Solve
  ( simplifyAllConstraints
  , proveImplication
  , assumedOrderModel
  , checkTypeFunction
  ) where

import           Cryptol.Parser.AST(LQName,thing)
import           Cryptol.TypeCheck.AST
import           Cryptol.TypeCheck.Monad
import           Cryptol.TypeCheck.Subst(apSubst,fvs,emptySubst,Subst)
import           Cryptol.TypeCheck.Solver.Eval
import           Cryptol.TypeCheck.Solver.FinOrd
import           Cryptol.TypeCheck.Solver.Numeric
import           Cryptol.TypeCheck.Solver.Class
import           Cryptol.TypeCheck.Solver.Selector(tryHasGoal)
import qualified Cryptol.TypeCheck.Solver.Smtlib as SMT
import           Cryptol.TypeCheck.Defaulting(tryDefaultWith)

import           Control.Monad(unless)
import           Data.List(partition)
import qualified Data.Set as Set

-- Add additional constraints that ensure validity of type function.
checkTypeFunction :: TFun -> [Type] -> [Prop]
checkTypeFunction TCSub [a,b]             = [ a >== b, pFin b]
checkTypeFunction TCDiv [a,b]             = [ b >== tOne, pFin a ]
checkTypeFunction TCMod [a,b]             = [ b >== tOne, pFin a ]
checkTypeFunction TCLenFromThen   [a,b,c] = [ pFin a, pFin b, pFin c, a =/= b ]
checkTypeFunction TCLenFromThenTo [a,b,c] = [ pFin a, pFin b, pFin c, a =/= b ]
checkTypeFunction _ _                     = []

-- XXX at the moment, we try to solve class constraints before solving fin
-- constraints, as they could yield fin constraints.  At some point, it would
-- probably be good to try solving all of these in one big loop.
simplifyAllConstraints :: InferM ()
simplifyAllConstraints =
  do mapM_  tryHasGoal     =<< getHasGoals
     simplifyGoals noFacts =<< getGoals


proveImplication :: LQName -> [TParam] -> [Prop] -> [Goal] -> InferM Subst
proveImplication lname as asmps0 goals =
  case assumedOrderModel noFacts (concatMap expandProp asmps0) of
    Left (_m,p) -> do recordError (UnusableFunction (thing lname) p)
                      return emptySubst
    Right (m,asmps) ->
      do let gs = [ g { goal = q } | g <- goals
                                   , let p = goal g
                                         q = simpType m p
                                   , p `notElem` asmps
                                   , q `notElem` asmps
                  ]

         (_,gs1) <- collectGoals (simplifyGoals m gs)

         let numAsmps = filter pIsNumeric asmps
             (numGs,otherGs) = partition (pIsNumeric . goal) gs1

         gs2 <- io $ SMT.simpDelayed as m numAsmps numGs
         case otherGs ++ gs2 of
           [] -> return emptySubst
           unsolved ->
            -- Last resort, let's try to default something.
             do let vs = Set.filter isFreeTV $ fvs $ map goal unsolved
                evars <- varsWithAsmps
                let candidates = vs `Set.difference` evars
                if Set.null vs
                  then reportErr unsolved >> return emptySubst
                  else do let (_,uns,su,ws) =
                               tryDefaultWith m (Set.toList candidates) unsolved
                          mapM_ recordWarning ws
                          unless (null uns) (reportErr uns)
                          return su

  where
  reportErr us = recordError $ UnsolvedDelcayedCt
                               DelayedCt { dctSource = lname
                                         , dctForall = as
                                         , dctAsmps  = asmps0
                                         , dctGoals  = us
                                         }



-- | Assumes that the substitution has been applied to the goals
simplifyGoals :: OrdFacts -> [Goal] -> InferM ()
simplifyGoals initOrd gs1 = solveSomeGoals [] False gs1
  where
  solveSomeGoals others !changes [] =
    if changes
      then solveSomeGoals [] False others
      else addGoals others

  solveSomeGoals others !changes (g : gs) =
    do let (m, bad, _) = goalOrderModel initOrd (others ++ gs)

       if not (null bad)
         then mapM_ (recordError . UnsolvedGoal) bad
         else
           case makeStep m g of
             Unsolved -> solveSomeGoals (g : others) changes gs
             Unsolvable ->
               do recordError (UnsolvedGoal g)
                  solveSomeGoals others changes gs

             Solved Nothing []     -> solveSomeGoals others changes gs
             Solved Nothing subs   -> solveSomeGoals others True (subs ++ gs)
             Solved (Just su) subs ->
               do extendSubst su
                  solveSomeGoals (apSubst su others) True
                                            (subs ++ apSubst su gs)

  makeStep m g = case numericStep m g of
                   Unsolved -> classStep g
                   x        -> x
