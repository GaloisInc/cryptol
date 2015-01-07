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
import           Cryptol.Utils.PP(pp)

import           Cryptol.TypeCheck.Defaulting(tryDefaultWith)

import           Data.Either(partitionEithers)
import           Data.Map ( Map )
import qualified Data.Map as Map
import           Data.Maybe ( fromMaybe )
import           Data.Set ( Set )
import qualified Data.Set as Set
import qualified SimpleSMT as SMT

import           Text.PrettyPrint(text)

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

debugBlock :: Num.Solver -> String -> IO a -> IO a
debugBlock s name m =
  do let logger = Num.logger s
     debugLog s name
     SMT.logTab logger
     a <- m
     SMT.logUntab logger
     return a

debugLog :: Num.Solver -> String -> IO ()
debugLog s x = SMT.logMessage (Num.logger s) x

proveImplication' :: LQName -> [TParam] -> [Prop] -> [Goal] ->
                                              IO (Either Error Subst)
proveImplication' lname as ps gs =
  Num.withSolver $ \s ->

  debugBlock s "proveImplication'" $
  do debugBlock s "assumes" $
       mapM_ (debugLog s . show . pp) ps
     debugBlock s "shows" $
       mapM_ (debugLog s . show . pp . goal) gs


     varMap <- Num.assumeProps s ps

     (possible,imps) <- Num.check s (uniVars (ps,gs))
     let su  = importImps varMap imps
         gs0 = apSubst su gs

     debugBlock s "substitution" $ debugLog s (show (pp su))

     if not possible
       then return $ Left $ UnusableFunction (thing lname) ps
       else -- XXX: Use imps
            do let gs1 = filter ((`notElem` ps) . goal) gs0
               mb <- simpGoals s gs1

               -- XXX: Minimize the goals invovled in the conflict
               let gs3 = fromMaybe (gs1,emptySubst) mb
               case gs3 of
                 ([],su1) -> return (Right su1)

                 -- XXX: Do we need the su?
                 (us,su2) -> 
                    do debugBlock s "2nd su:" (debugLog s . show . pp $ su2)
                       return $ Left
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

_testSimpGoals :: IO ()
_testSimpGoals = Num.withSolver $ \s ->
  do mb <- simpGoals s gs
     case mb of
       Just (gs1,su) ->
          do debugBlock s "Simplified goals"
                $ mapM_ (debugLog s . show . pp . goal) gs1
             debugLog s (show (pp su))
       Nothing -> debugLog s "Impossible"
  where
  gs = map fakeGoal [ tv 0 =#= num 5 ]
    -- [ tv 0 =#= tInf, tMod (num 3) (tv 0) =#= num 4 ]

  fakeGoal p = Goal { goalSource = undefined, goalRange = undefined, goal = p }
  tv n = TVar (TVFree n KNum Set.empty (text "test var"))
  num x = tNum (x :: Int)

-- | Assumes that the substitution has been applied to the goals.
simpGoals :: Num.Solver -> [Goal] -> IO (Maybe ([Goal],Subst))
simpGoals s gs0 =
  do let (unsolvedClassCts,numCts) = solveClassCts gs0

         varMap = Map.unions [ vm | ((_,vm),_) <- numCts ]
         updCt prop (g,vs) = case Num.importProp varMap prop of
                               Just [g1] -> (g { goal = g1 }, vs)

                               r -> panic "simpGoals"
                                      [ "Unexpected import results"
                                      , show r
                                      ]
     case numCts of
       [] -> return $ Just (unsolvedClassCts, emptySubst)
       _  -> do mbOk <- Num.checkDefined s updCt uvs numCts
                case mbOk of
                  Nothing -> return Nothing
                  Just (nonDef,def,imps) ->
                    do debugBlock s ("simpGoals results") $
                         do debugBlock s "possibly not defined" $
                              mapM_ (debugLog s . show . pp . goal . fst) nonDef
                            debugBlock s "defined" $
                              mapM_ (debugLog s . show . Num.ppProp . Num.dpSimpExprProp) def

                       let (su,extraProps) = importSplitImps varMap imps

                       let def1 = eliminateSimpleGEQ def
                           toGoal =
                             case map (fst . Num.dpData) def1 of
                               [g] -> \p -> g { goal = p }
                               gs  -> \p ->
                                 Goal { goalRange = rCombs (map goalRange gs)
                                      , goalSource = CtImprovement
                                      , goal = p }

                       def2 <- Num.simplifyProps s def1

                       -- XXX: Apply subst to class constraints and go again?
                       return $ Just ( apSubst su $ map toGoal extraProps ++
                                       map fst nonDef ++
                                       unsolvedClassCts ++
                                       map fst def2
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



{- | Simplify easy less-than-or-equal-to goals.  Those are common with long
lists of literals, so we have special handling for them.  In particular:

  * Reduce goals of the form @(a >= k1, a >= k2, a >= k3, ...)@ to
   @a >= max (k1, k2, k3, ...)@, when all the k's are constant.

  * Eliminate goals of the form @ki >= k2@, when @k2@ is leq than @k1@.

  * Eliminate goals of the form @a >= 0@.

NOTE:  This assumes that the goals are well-defined.
-}
eliminateSimpleGEQ :: [Num.DefinedProp a] -> [Num.DefinedProp a]
eliminateSimpleGEQ = go Map.empty []
  where

  go geqs other (g : rest) =
    case Num.dpSimpExprProp g of
      _ Num.:>= Num.K (Num.Nat 0) ->
          go geqs  other rest

      Num.K (Num.Nat k1) Num.:>= Num.K (Num.Nat k2)
        | k1 >= k2 -> go geqs other rest

      Num.Var v Num.:>= Num.K (Num.Nat k2) ->
        go (addUpperBound v (k2,g) geqs) other rest

      _ -> go geqs (g:other) rest

  go geqs other [] = [ g | (_,g) <- Map.elems geqs ] ++ other

  -- add in a possible upper bound for var
  addUpperBound var g = Map.insertWith cmp var g
    where
    cmp a b | fst a > fst b = a
            | otherwise     = b



