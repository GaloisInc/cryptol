-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE PatternGuards, BangPatterns #-}
{-# LANGUAGE Safe #-}
module Cryptol.TypeCheck.Solve
  ( simplifyAllConstraints
  , proveImplication
  , checkTypeFunction
  ) where

import           Cryptol.Parser.AST(LQName, thing)
import           Cryptol.TypeCheck.AST
import           Cryptol.TypeCheck.Monad
import           Cryptol.TypeCheck.Subst(apSubst,fvs,emptySubst,Subst)
import           Cryptol.TypeCheck.Solver.Class
import           Cryptol.TypeCheck.Solver.Selector(tryHasGoal)
import qualified Cryptol.TypeCheck.Solver.Numeric.AST as Num
import qualified Cryptol.TypeCheck.Solver.CrySAT as Num

import           Cryptol.TypeCheck.Defaulting(tryDefaultWith)

import           Data.Either(partitionEithers)

-- Add additional constraints that ensure validity of type function.
checkTypeFunction :: TFun -> [Type] -> [Prop]
checkTypeFunction TCSub [a,b]             = [ a >== b, pFin b]
checkTypeFunction TCDiv [a,b]             = [ b >== tOne, pFin a ]
checkTypeFunction TCMod [a,b]             = [ b >== tOne, pFin a ]
checkTypeFunction TCLenFromThen   [a,b,c] = [ pFin a, pFin b, pFin c, a =/= b ]
checkTypeFunction TCLenFromThenTo [a,b,c] = [ pFin a, pFin b, pFin c, a =/= b ]
checkTypeFunction _ _                     = []


--------------------------------------------------------------------------------

-- XXX at the moment, we try to solve class constraints before solving fin
-- constraints, as they could yield fin constraints.  At some point, it would
-- probably be good to try solving all of these in one big loop.
simplifyAllConstraints :: InferM ()
simplifyAllConstraints =
  do mapM_  tryHasGoal =<< getHasGoals
     gs <- getGoals
     addGoals =<< io (Num.withSolver (`simpGoals` gs))


proveImplication :: LQName -> [TParam] -> [Prop] -> [Goal] -> InferM Subst
proveImplication lnam as ps gs =
  do mbErr <- io (proveImplication' lnam as ps gs)
     case mbErr of
       Nothing  -> return ()
       Just err -> recordError err
     return emptySubst

proveImplication' :: LQName -> [TParam] -> [Prop] -> [Goal] -> IO (Maybe Error)
proveImplication' lname as ps gs =
  Num.withSolver $ \s ->

  do Num.assumeProps s ps
     (possible,imps) <- Num.check s
     if not possible
       then return $ Just $ UnusableFunction (thing lname) ps
       else do let gs1 = filter ((`notElem` ps) . goal) gs
               gs2 <- simpGoals s gs1
               case gs2 of
                 [] -> return Nothing
                 us -> return $ Just $ UnsolvedDelcayedCt
                                     $ DelayedCt { dctSource = lname
                                                 , dctForall = as
                                                 , dctAsmps  = ps
                                                 , dctGoals  = us
                                                 }

-- | Class goals go on the left, numeric goals go on the right.
numericRight :: Goal -> Either Goal (Goal, Num.Prop)
numericRight g  = case Num.exportProp (goal g) of
                    Just p  -> Right (g, p)
                    Nothing -> Left g

-- | Assumes that the substitution has been applied to the goals.
simpGoals :: Num.Solver -> [Goal] -> IO [Goal]
simpGoals s gs0 =
  do let (unsolvedClassCts,numCts) = solveClassCts gs0
     case numCts of
       [] -> return unsolvedClassCts
       _  -> do (nonDef,def) <- Num.checkDefined s numCts
                def1         <- Num.simplifyProps s def
                return (nonDef ++ unsolvedClassCts ++ def1)
  where
  solveClassRight g = case classStep g of
                        Just gs -> Right gs
                        Nothing -> Left g

  -- returns (unsolved class constraints, numeric constraints)
  solveClassCts [] = ([], [])
  solveClassCts gs =
     let (classCts,numCts)    = partitionEithers (map numericRight gs)
         (unsolved,solveds)   = partitionEithers (map solveClassRight classCts)
         (unsolved',numCts')  = solveClassCts (concat solveds)
     in (unsolved ++ unsolved', numCts ++ numCts')





