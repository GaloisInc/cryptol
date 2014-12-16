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
import           Cryptol.TypeCheck.Subst
                    (FVS,apSubst,fvs,emptySubst,Subst,listSubst)
import           Cryptol.TypeCheck.Solver.Class
import           Cryptol.TypeCheck.Solver.Selector(tryHasGoal)
import qualified Cryptol.TypeCheck.Solver.Numeric.AST as Num
import qualified Cryptol.TypeCheck.Solver.Numeric.ImportExport as Num
import qualified Cryptol.TypeCheck.Solver.CrySAT as Num
import           Cryptol.Utils.Panic(panic)
import           Cryptol.Parser.Position(rCombs)

import           Cryptol.TypeCheck.Defaulting(tryDefaultWith)

import           Data.Either(partitionEithers)
import           Data.Map ( Map )
import qualified Data.Map as Map
import           Data.Maybe ( fromMaybe )
import           Data.Set ( Set )
import qualified Data.Set as Set

import Cryptol.TypeCheck.Solver.Numeric.AST(ppProp)
import Text.PrettyPrint (vcat, text)

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
     mb <- io (Num.withSolver (`simpGoals` gs))
     case mb of
       Just (gs1,su) -> extendSubst su >> addGoals gs1
       Nothing -> -- XXX: Minimize the goals involved in the conflict
                  mapM_ (recordError . UnsolvedGoal) gs


proveImplication :: LQName -> [TParam] -> [Prop] -> [Goal] -> InferM Subst
proveImplication lnam as ps gs =
  do mbErr <- io (proveImplication' lnam as ps gs)
     case mbErr of
       Right su -> return su
       Left err -> recordError err >> return emptySubst

proveImplication' :: LQName -> [TParam] -> [Prop] -> [Goal] ->
                                              IO (Either Error Subst)
proveImplication' lname as ps gs =
  Num.withSolver $ \s ->

  do varMap <- Num.assumeProps s ps

     (possible,imps) <- Num.check s (uniVars (ps,gs))
     let su  = importImps varMap imps
         gs0 = apSubst su gs

     if not possible
       then return $ Left $ UnusableFunction (thing lname) ps
       else -- XXX: Use imps
            do let gs1 = filter ((`notElem` ps) . goal) gs0
               gs2 <- simpGoals s gs1

               -- XXX: Minimize the goals invovled in the conflict
               let gs3 = fromMaybe (gs1,emptySubst) gs2
               case gs3 of
                 ([],su1) -> return (Right su1)

                 -- XXX: Do we need the su?
                 (us,_) -> return $ Left
                                  $ UnsolvedDelcayedCt
                                  $ DelayedCt { dctSource = lname
                                              , dctForall = as
                                              , dctAsmps  = ps
                                              , dctGoals  = us
                                              }

uniVars :: FVS a => a -> Set Num.Name
uniVars = Set.map Num.exportVar . Set.filter isUni . fvs
  where
  isUni (TVFree _ k _ _) = k == KNum
  isUni _                = False



-- | Class goals go on the left, numeric goals go on the right.
numericRight :: Goal -> Either Goal ((Goal, Num.VarMap), Num.Prop)
numericRight g  = case Num.exportProp (goal g) of
                    Just (p,vm)  -> Right ((g,vm), p)
                    Nothing -> Left g

-- | Assumes that the substitution has been applied to the goals.
simpGoals :: Num.Solver -> [Goal] -> IO (Maybe ([Goal],Subst))
simpGoals s gs0 =
  do let (unsolvedClassCts,numCts) = solveClassCts gs0
         varMap = Map.unions [ vm | ((_,vm),_) <- numCts ]
     case numCts of
       [] -> return $ Just (unsolvedClassCts, emptySubst)
       _  -> do mbOk <- Num.checkDefined s uvs numCts
                case mbOk of
                  Nothing -> return Nothing
                  Just (nonDef,def,imps) ->
                    do let (su,extraProps) = importSplitImps varMap imps
                           def' = [ (a,p) | (a,_,p) <- eliminateRedundant def ]
                           toGoal =
                             case map (fst . fst) def' of
                               [g] -> \p -> g { goal = p }
                               ds -> \p ->
                                 Goal { goalRange = rCombs (map goalRange ds)
                                      , goalSource = CtImprovement
                                      , goal = p }

{-
                       print $ vcat $ text "Simplifying: "
                                      : [ ppProp x | (_,x,_) <- def ]
-}
                       def1 <- Num.simplifyProps s def'

                       -- XXX: Apply subst to class constraints and go again?
                       return $ Just ( map toGoal extraProps ++
                                       map fst nonDef ++
                                       apSubst su unsolvedClassCts ++
                                       map fst def1
                                     , su
                                     )
  where
  uvs         = uniVars gs0

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


-- | Improt an improving substitutin into a Cryptol substitution.
-- The substituitn will contain only unification variables.
-- "Improvements" on skolem variables become additional constraints.
importSplitImps :: Num.VarMap -> Map Num.Name Num.Expr -> (Subst, [Prop])
importSplitImps varMap = mk . partitionEithers . map imp . Map.toList
  where
  mk (uni,props) = (listSubst uni, props)

  imp (x,e) = case (Map.lookup x varMap, Num.importType varMap e) of
                (Just tv, Just ty) ->
                  case tv of
                    TVFree {}  -> Left (tv,ty)
                    TVBound {} -> Right (TVar tv =#= ty)
                _ -> panic "importImps" [ "Failed to import:", show x, show e ]



-- | Improt an improving substitutin into a Cryptol substitution.
-- The substituitn will contain both unification and skolem variables,
-- so this should be used when processing *givens*.
importImps :: Num.VarMap -> Map Num.Name Num.Expr -> Subst
importImps varMap = listSubst . map imp . Map.toList
  where
  imp (x,e) = case (Map.lookup x varMap, Num.importType varMap e) of
                (Just tv, Just ty) -> (tv,ty)
                _ -> panic "importImps" [ "Failed to import:", show x, show e ]



-- | Reduce goals of the form (a >= k1, a >= k2, a >= k3, ...) into one of the
-- form (a >= max (k1, k2, k3, ...)), when all the k's are constant.  Otherwise,
-- return goals unchanged.
eliminateRedundant :: [(a,Num.Prop,Num.SMTProp)] -> [(a,Num.Prop,Num.SMTProp)]
eliminateRedundant  = go Map.empty []
  where

  go geqs other ( g@(_,prop,_) : rest) =
    case prop of
      Num.Var v Num.:>= Num.K n -> go (addUpperBound v (n,g) geqs)   other  rest
      _                         -> go                        geqs (g:other) rest

  go geqs other [] = [ g | (_,g) <- Map.elems geqs ] ++ other

  -- add in a possible upper bound for var
  addUpperBound var g = Map.insertWith cmp var g
    where
    cmp a b | fst a > fst b = a
            | otherwise     = b
