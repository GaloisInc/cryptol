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
  , improveByDefaulting
  ) where

import           Cryptol.Parser.AST(LQName, thing)
import           Cryptol.TypeCheck.AST
import           Cryptol.TypeCheck.Monad
import           Cryptol.TypeCheck.Subst
                    (FVS,apSubst,fvs,singleSubst,
                          emptySubst,Subst,listSubst, (@@))
import           Cryptol.TypeCheck.Solver.Class
import           Cryptol.TypeCheck.Solver.Selector(tryHasGoal)
import qualified Cryptol.TypeCheck.Solver.Numeric.AST as Num
import qualified Cryptol.TypeCheck.Solver.Numeric.ImportExport as Num
import qualified Cryptol.TypeCheck.Solver.CrySAT as Num
import           Cryptol.TypeCheck.Solver.CrySAT (debugBlock, DebugLog(..))
import           Cryptol.Utils.Panic(panic)
import           Cryptol.Parser.Position(rCombs)

import           Data.Either(partitionEithers)
import           Data.Maybe(catMaybes)
import           Data.Map ( Map )
import qualified Data.Map as Map
import           Data.Set ( Set )
import qualified Data.Set as Set

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
     mb <- io (Num.withSolver False (`simpGoals` gs))
     case mb of
       Right (gs1,su) -> extendSubst su >> addGoals gs1
       Left badGs     -> mapM_ (recordError . UnsolvedGoal) badGs


proveImplication :: LQName -> [TParam] -> [Prop] -> [Goal] -> InferM Subst
proveImplication lnam as ps gs =
  do evars <- varsWithAsmps
     mbErr <- io (proveImplicationIO lnam evars as ps gs)
     case mbErr of
       Right (su,ws) ->
          do mapM_ recordWarning ws
             return su
       Left err -> recordError err >> return emptySubst


proveImplicationIO :: LQName   -> -- ^ Checking this function
                      Set TVar -> -- ^ These appear in the env., and we should
                                  -- not try to default them.
                     [TParam]  -> -- ^ Type parameters
                     [Prop]    -> -- ^ Assumed constraints
                     [Goal]    -> -- ^ Collected constraints
                     IO (Either Error (Subst,[Warning]))
proveImplicationIO _ _ _ [] [] = return (Right (emptySubst,[]))
proveImplicationIO lname varsInEnv as ps gs =
  Num.withSolver False $ \s ->
  debugBlock s "proveImplicationIO" $

  do debugBlock s "assumes" (debugLog s ps)
     debugBlock s "shows"   (debugLog s gs)
     debugLog s "------------------"


     varMap <- Num.assumeProps s ps

     (possible,imps) <- Num.check s (uniVars (ps,gs))
     let su  = importImps varMap imps
         gs0 = apSubst su gs

     debugBlock s "improvement from assumptions:" $ debugLog s su

     if not possible
       then do debugLog s "(contradiction in assumptions)"
               return $ Left $ UnusableFunction (thing lname) ps

       else -- XXX: Use su
            do let gs1 = filter ((`notElem` ps) . goal) gs0
               mb <- simpGoals s gs1

               case mb of
                 Left badGs     -> reportUnsolved badGs
                 Right ([],su1) -> return (Right (su1,[]))

                 Right (us,su1) -> 
                    -- Last hope: try to default stuff
                    do let vs    = Set.filter isFreeTV $ fvs $ map goal us
                           dVars = Set.toList (vs `Set.difference` varsInEnv)
                       (_,us1,su2,ws) <- improveByDefaultingWith s dVars us
                       case us1 of
                          [] -> return (Right (su2 @@ su1, ws))
                          _  -> reportUnsolved us1
  where
  reportUnsolved us =
    return $ Left $ UnsolvedDelcayedCt
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
_testSimpGoals = Num.withSolver True $ \s ->
  do _ <- Num.assumeProps s asmps
     mb <- simpGoals s gs
     case mb of
       Right _  -> debugLog s "End of test"
       Left _   -> debugLog s "Impossible"
  where
  asmps = [ tv 0 >== num 1, num 2 >== tv 0 ]
--   gs = map fakeGoal [ num 32 =#= tv 1 .+. (num 16 .*. tv 0) ]
  gs = map fakeGoal [ num 32 =#= tv 1 .+. (num 16 .*. tv 0) ]

    -- [ tv 0 =#= tInf, tMod (num 3) (tv 0) =#= num 4 ]

  fakeGoal p = Goal { goalSource = undefined, goalRange = undefined, goal = p }
  tv n = TVar (TVFree n KNum Set.empty (text "test var"))
  num x = tNum (x :: Int)

{- | Try to simplify a bunch of goals.
Assumes that the substitution has been applied to the goals.
The result:
  * Left gs:  the original goals were contradictory; here a subset that
              leads to the contradiction.
  * Right (gs,su): here is the simplified set of goals,
                   and an improving substitution. -}
simpGoals :: Num.Solver -> [Goal] -> IO (Either [Goal] ([Goal],Subst))
simpGoals _ []  = return (Right ([],emptySubst))
simpGoals s gs0 =
  debugBlock s "Simplifying goals" $
  do debugBlock s "goals:" (debugLog s gs0)

     let (unsolvedClassCts,numCts) = solveClassCts gs0

         varMap = Map.unions [ vm | ((_,vm),_) <- numCts ]
         updCt prop (g,vs) = case Num.importProp varMap prop of
                               Just [g1] -> (g { goal = g1 }, vs)

                               r -> panic "simpGoals"
                                      [ "Unexpected import results"
                                      , show r
                                      ]

     case numCts of
       [] -> do debugBlock s "After simplification (no numerics):"
                  $ debugLog s unsolvedClassCts
                return $ Right (unsolvedClassCts, emptySubst)

       _  -> do mbOk <- Num.checkDefined s updCt uvs numCts
                case mbOk of

                  Nothing ->
                    do badGs <- Num.minimizeContradiction s numCts
                       return (Left (map fst badGs))

                  Just (nonDef,def,imps) ->

                    -- XXX: What should we do with the extra props...
                    do let (su,extraProps) = importSplitImps varMap imps

                           def1 = eliminateSimpleGEQ def
                           toGoal =
                             case map (fst . Num.dpData) def1 of
                               []  -> case gs0 of
                                        g : _ -> \p -> g { goal = p }
                                        [] -> panic "simplification"
                                                [ "Goals out of no goals." ]

                               [g] -> \p -> g { goal = p }
                               gs  -> \p ->
                                 Goal { goalRange = rCombs (map goalRange gs)
                                      , goalSource = CtImprovement
                                      , goal = p }

                       def2 <- Num.simplifyProps s def1
                       let allCts = apSubst su $ map toGoal extraProps ++
                                    map fst nonDef ++
                                    unsolvedClassCts ++
                                    map fst def2

                       debugBlock s "After simplification:" $
                          do debugLog s allCts
                             debugLog s su

                       -- XXX: Apply subst to class constraints and go again?
                       return $ Right ( allCts, su )
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


-- | Import an improving substitutin (i.e., a bunch of equations)
-- into a Cryptol substitution (which is idempotent).
-- The substitution will contain only unification variables.
-- "Improvements" on skolem variables become additional constraints.
importSplitImps :: Num.VarMap -> Map Num.Name Num.Expr -> (Subst, [Prop])
importSplitImps varMap = mk . partitionEithers . map imp . Map.toList
  where
  mk (uni,props) = (listSubst (catMaybes uni), props)

  imp (x,e) = case (Map.lookup x varMap, Num.importType varMap e) of
                (Just tv, Just ty) ->
                  case tv of
                    TVFree {}  -> Left (Just (tv,ty))
                    TVBound {} -> Right (TVar tv =#= ty)

                {- This may happen if we are working on an implication,
                and we have an improvement about a variable in the
                assumptions that is not in any og the goals.
                XXX: Perhaps, we should mark these variable, so we don't waste
                time to "improve" them. -}

                _ -> Left Nothing



-- | Import an improving substitution into a Cryptol substitution.
-- The substitution will contain both unification and skolem variables,
-- so this should be used when processing *givens*.
importImps :: Num.VarMap -> Map Num.Name Num.Expr -> Subst
importImps varMap = listSubst . map imp . Map.toList
  where
  imp (x,e) = case (Map.lookup x varMap, Num.importType varMap e) of
                (Just tv, Just ty) -> (tv,ty)
                _ -> panic "importImps" [ "Failed to import:", show x, show e ]



{- | Simplify easy less-than-or-equal-to and equal-to goals.
Those are common with long lists of literals, so we have special handling
for them.  In particular:

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
      Num.K a Num.:== Num.K b
        | a == b -> go geqs other rest

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




--------------------------------------------------------------------------------

-- This is what we use to avoid ambiguity when generalizing.

{- If a variable, `a`, is:
    1. Of kind KNum
    2. Generic (i.e., does not appear in the environment)
    3. It appears only in constraints but not in the resulting type
       (i.e., it is not on the RHS of =>)
    4. It (say, the variable 'a') appears only in constraints like this:
        3.1 `a >= t` with (`a` not in `fvs t`)
        3.2 in the `s` of `fin s`

  Then we replace `a` with `max(t1 .. tn)` where the `ts`
  are from the constraints `a >= t`.

  If `t1 .. tn` is empty, then we replace `a` with 0.

  This function assumes that 1-3 have been checked, and implements the rest.
  So, given some variables and constraints that are about to be generalized,
  we return:
      1. a new (same or smaller) set of variables to quantify,
      2. a new set of constraints,
      3. a substitution which indicates what got defaulted.
-}

improveByDefaulting ::
  [TVar] ->   -- candidates for defaulting
  [Goal] ->   -- constraints
    IO  ( [TVar]    -- non-defaulted
        , [Goal]    -- new constraints
        , Subst     -- improvements from defaultign
        , [Warning] -- warnings about defaulting
        )
improveByDefaulting xs gs = Num.withSolver False $ \s ->
  improveByDefaultingWith s xs gs

improveByDefaultingWith ::
  Num.Solver ->
  [TVar] ->   -- candidates for defaulting
  [Goal] ->   -- constraints
    IO  ( [TVar]    -- non-defaulted
        , [Goal]    -- new constraints
        , Subst     -- improvements from defaultign
        , [Warning] -- warnings about defaulting
        )
improveByDefaultingWith s as ps =
  classify (Map.fromList [ (a,([],Set.empty)) | a <- as ]) [] [] ps

  where
  -- leq: candidate definitions (i.e. of the form x >= t, x `notElem` fvs t)
  --      for each of these, we keep the list of `t`, and the free vars in them.
  -- fins: all `fin` constraints
  -- others: any other constraints
  classify leqs fins others [] =
    do let -- First, we use the `leqs` to choose some definitions.
           (defs, newOthers)  = select [] [] (fvs others) (Map.toList leqs)
           su                 = listSubst defs

       -- Do this to simplify the instantiated "fin" constraints.
       mb <- simpGoals s (newOthers ++ others ++ apSubst su fins)
       case mb of
         Right (gs1,su1) ->
           let warn (x,t) =
                 case x of
                   TVFree _ _ _ d -> DefaultingTo d t
                   TVBound {} -> panic "Crypto.TypeCheck.Infer"
                     [ "tryDefault attempted to default a quantified variable."
                     ]

            in return ( [ a | a <- as, a `notElem` map fst defs ]
                      , gs1
                      , su1 @@ su    -- XXX: is that right?
                      , map warn defs
                      )



         -- Something went wrong, don't default.
         Left _ -> return (as,ps,emptySubst,[])


  classify leqs fins others (prop : more) =
      case tNoUser (goal prop) of

        -- We found a `fin` constraint.
        TCon (PC PFin) [ _ ] -> classify leqs (prop : fins) others more

        -- Things of the form: x >= T(x) are not defaulted.
        TCon (PC PGeq) [ TVar x, t ]
          | x `elem` as && x `Set.notMember` freeRHS ->
           classify leqs' fins others more
           where freeRHS = fvs t
                 add (xs1,vs1) (xs2,vs2) = (xs1 ++ xs2, Set.union vs1 vs2)
                 leqs' = Map.insertWith add x ([(t,prop)],freeRHS) leqs

        _ -> classify leqs fins (prop : others) more


  -- Pickout which variables may be defaulted and how.
    -- XXX: simpType t
  select yes no _ [] = ([ (x, t) | (x,t) <- yes ] ,no)
  select yes no otherFree ((x,(rhsG,vs)) : more) =
    select newYes newNo newFree newMore

    where
    (ts,gs) = unzip rhsG

    -- `x` selected only if appears nowehere else.
    -- this includes other candidates for defaulting.
    (newYes,newNo,newFree,newMore)

        -- Mentioned in other constraints, definately not defaultable.
        | x `Set.member` otherFree = noDefaulting

        | otherwise =
            let deps = [ y | (y,(_,yvs)) <- more, x `Set.member` yvs ]
                recs = filter (`Set.member` vs) deps
            in if not (null recs) || isBoundTV x -- x >= S(y), y >= T(x)
                                 then noDefaulting

                                  -- x >= S,    y >= T(x)   or
                                  -- x >= S(y), y >= S
                                  else yesDefaulting

        where
        noDefaulting = ( yes, gs ++ no, vs `Set.union` otherFree, more )

        yesDefaulting =
          let ty  = case ts of
                      [] -> tNum (0::Int)
                      _  -> foldr1 tMax ts
              su1 = singleSubst x ty
          in ( (x,ty) : [ (y,apSubst su1 t) | (y,t) <- yes ]
             , no         -- We know that `x` does not appear here
             , otherFree  -- We know that `x` did not appear here either

             -- No need to update the `vs` because we've already
             -- checked that there are no recursive dependencies.
             , [ (y, (apSubst su1 ts1, vs1)) | (y,(ts1,vs1)) <- more ]
             )




