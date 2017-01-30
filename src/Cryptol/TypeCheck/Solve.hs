-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE PatternGuards, BangPatterns, RecordWildCards #-}
{-# LANGUAGE Safe #-}
module Cryptol.TypeCheck.Solve
  ( simplifyAllConstraints
  , proveImplication
  , wfType
  , wfTypeFunction
  , improveByDefaultingWith
  , defaultReplExpr
  , simpType
  , simpTypeMaybe
  ) where

import           Cryptol.Parser.Position (emptyRange)
import           Cryptol.TypeCheck.PP(pp)
import           Cryptol.TypeCheck.AST
import           Cryptol.TypeCheck.Monad
import           Cryptol.TypeCheck.Subst
                    (apSubst,fvs,singleSubst, isEmptySubst,
                          emptySubst,Subst,listSubst, (@@), Subst,
                           apSubstMaybe, substBinds)
import           Cryptol.TypeCheck.Solver.Class
import           Cryptol.TypeCheck.Solver.Selector(tryHasGoal)
import qualified Cryptol.TypeCheck.Solver.Numeric.AST as Num
import qualified Cryptol.TypeCheck.Solver.Numeric.ImportExport as Num
import           Cryptol.TypeCheck.Solver.Numeric.Interval (Interval)
import qualified Cryptol.TypeCheck.Solver.Numeric.SimplifyExpr as Num
import qualified Cryptol.TypeCheck.Solver.CrySAT as Num
import           Cryptol.TypeCheck.Solver.CrySAT (debugBlock, DebugLog(..))
import           Cryptol.TypeCheck.Solver.Simplify (tryRewritePropAsSubst)
import           Cryptol.Utils.PP (text)
import           Cryptol.Utils.Panic(panic)
import           Cryptol.Utils.Misc(anyJust)

import           Control.Monad (unless, guard)
import           Data.Either(partitionEithers)
import           Data.Maybe(catMaybes, fromMaybe, mapMaybe)
import           Data.Map ( Map )
import qualified Data.Map as Map
import           Data.Set ( Set )
import qualified Data.Set as Set


{- | Add additional constraints that ensure validity of type function.
Note that these constraints do not introduce additional malformed types,
so the well-formedness constraints are guaranteed to be well-formed.
This assumes that the parameters are well-formed. -}
wfTypeFunction :: TFun -> [Type] -> [Prop]
wfTypeFunction TCSub [a,b]             = [ a >== b, pFin b]
wfTypeFunction TCDiv [a,b]             = [ b >== tOne, pFin a ]
wfTypeFunction TCMod [a,b]             = [ b >== tOne, pFin a ]
wfTypeFunction TCLenFromThen   [a,b,w] =
         [ pFin a, pFin b, pFin w, a =/= b, w >== tWidth a ]
wfTypeFunction TCLenFromThenTo [a,b,c] = [ pFin a, pFin b, pFin c, a =/= b ]
wfTypeFunction _ _                     = []

-- | Add additional constraints that ensure the validity of a type.
wfType :: Type -> [Prop]
wfType t =
  case t of
    TCon c ts ->
      let ps = concatMap wfType ts
      in case c of
           TF f -> wfTypeFunction f ts ++ ps
           _    -> ps

    TVar _      -> []
    TUser _ _ s -> wfType s
    TRec fs     -> concatMap (wfType . snd) fs




--------------------------------------------------------------------------------

simplifyAllConstraints :: InferM ()
simplifyAllConstraints =
  do mapM_  tryHasGoal =<< getHasGoals
     gs <- getGoals
     case gs of
       [] -> return ()
       _ ->
         do r <- curRange
            let n = length gs
            io $ putStrLn $ "simplifyAllConstraints " ++ show (length gs) ++ " goals." ++ show r
            if (n > 400) then io $ writeFile "GS" $ unlines $ map (show.pp.goal) gs else return ()
            solver <- getSolver
            (mb,su) <- io (simpGoals' solver gs)
            extendSubst su
            case mb of
              Right gs1  -> addGoals gs1
              Left badGs -> mapM_ (recordError . UnsolvedGoal True) badGs


proveImplication :: Name -> [TParam] -> [Prop] -> [Goal] -> InferM Subst
proveImplication lnam as ps gs =
  do evars <- varsWithAsmps
     solver <- getSolver
     (mbErr,su) <- io (proveImplicationIO solver lnam evars as ps gs)
     case mbErr of
       Right ws -> mapM_ recordWarning ws
       Left err -> recordError err
     return su


proveImplicationIO :: Num.Solver
                   -> Name     -- ^ Checking this function
                   -> Set TVar -- ^ These appear in the env., and we should
                               -- not try to default the
                   -> [TParam] -- ^ Type parameters
                   -> [Prop]   -- ^ Assumed constraint
                   -> [Goal]   -- ^ Collected constraints
                   -> IO (Either Error [Warning], Subst)
proveImplicationIO _   _     _         _  [] [] = return (Right [], emptySubst)
proveImplicationIO s lname varsInEnv as ps gs =
  debugBlock s "proveImplicationIO" $

  do debugBlock s "assumes" (debugLog s ps)
     debugBlock s "shows"   (debugLog s gs)
     debugLog s "1. ------------------"


     _simpPs <- Num.assumeProps s ps

     mbImps <- Num.check s
     debugLog s "2. ------------------"


     case mbImps of

       Nothing ->
         do debugLog s "(contradiction in assumptions)"
            return (Left $ UnusableFunction lname ps, emptySubst)

       Just (imps,extra) ->
         do let su  = importImps imps
                gs0 = apSubst su gs

            debugBlock s "improvement from assumptions:" $ debugLog s su

            let (scs,invalid) = importSideConds extra
            unless (null invalid) $
              panic "proveImplicationIO" ( "Unable to import all side conditions:"
                                              : map (show . Num.ppProp) invalid )

            let gs1 = filter ((`notElem` ps) . goal) gs0

            debugLog s "3. ---------------------"
            (mb,su1) <- simpGoals' s (scs ++ gs1)

            case mb of
              Left badGs  -> reportUnsolved badGs (su1 @@ su)
              Right []    -> return (Right [], su1 @@ su)

              Right us ->
                 -- Last hope: try to default stuff
                 do let vs    = Set.filter isFreeTV $ fvs $ map goal us
                        dVars = Set.toList (vs `Set.difference` varsInEnv)
                    (_,us1,su2,ws) <- improveByDefaultingWith s dVars us
                    case us1 of
                       [] -> return (Right ws, su2 @@ su1 @@ su)
                       _  -> reportUnsolved us1 (su2 @@ su1 @@ su)
  where
  reportUnsolved us su =
    return ( Left $ UnsolvedDelayedCt
                  $ DelayedCt { dctSource = lname
                              , dctForall = as
                              , dctAsmps  = ps
                              , dctGoals  = us
                              }, su)





{- Constraints and satisfiability:

  1. [Satisfiable] A collection of constraints is _satisfiable_, if there is an
     assignment for the variables that make all constraints true.

  2. [Valid] If a constraint is satisfiable for any assignment of its free
     variables, then it is _valid_, and may be ommited.

  3. [Partial] A constraint may _partial_, which means that under some
     assignment it is neither true nor false.  For example:
     `x - y > 5` is true for `{ x = 15, y = 3 }`, it is false for
     `{ x = 5, y = 4 }`, and it is neither for `{ x = 1, y = 2 }`.

     Note that constraints that are always true or undefined are NOT
     valid, as there are assignemntes for which they are not true.
     An example of such constraint is `x - y >= 0`.

  4. [Provability] Instead of thinking of three possible values for
     satisfiability (i.e., true, false, and unknown), we could instead
     think of asking: "Is constraint C provable".  This essentailly
     maps "true" to "true", and "false,unknown" to "false", if we
     treat constraints with malformed parameters as unprovable.
-}


{-
The plan:
  1. Start with a set of constraints, CS
  2. Compute its well-defined closure, DS.
  3. Simplify constraints: evaluate terms in constraints as much as possible
  4. Solve: eliminate constraints that are true
  5. Check for consistency
  6. Compute improvements
  7. For each type in the improvements, add well-defined constraints
  8. Instantiate constraints with substitution
  9. Goto 3
-}

simpGoals' :: Num.Solver -> [Goal] -> IO (Either [Goal] [Goal], Subst)
simpGoals' s gs0 = go emptySubst [] (wellFormed gs0 ++ gs0)
  where
  -- Assumes that the well-formed constraints are themselves well-formed.
  wellFormed gs = [ g { goal = p } | g <- gs, p <- wfType (goal g) ]

  go su old [] = return (Right old, su)
  go su old gs =
    do gs1  <- simplifyConstraintTerms s gs
       res  <- solveConstraints s old gs1
       case res of
         Left err -> return (Left err, su)
         Right gs2 ->
           do let gs3 = gs2 ++ old
              mb <- computeImprovements s gs3
              case mb of
                Left err -> return (Left err, su)
                Right impSu ->
                  let (unchanged,changed) =
                                    partitionEithers (map (applyImp impSu) gs3)
                      new = wellFormed changed
                  in go (impSu @@ su) unchanged (new ++ changed)

  applyImp su g = case apSubstMaybe su (goal g) of
                    Nothing -> Left g
                    Just p  -> Right g { goal = p }


{- Note:
It is good to consider the other goals when evaluating terms.
For example, consider the constraints:

    P (x * inf), x >= 1

We cannot simplify `x * inf` on its own, because we do not know if `x`
might be 0.  However, in the contxt of `x >= 1`, we know that this is
impossible, and we can simplify the constraints to:

    P inf, x >= 1

However, we should be careful to avoid circular reasoning, as we wouldn't
want to use the fact that `x >= 1` to simplify `x >= 1` to true.
-}

-- XXX: currently simplify individually
simplifyConstraintTerms :: Num.Solver -> [Goal] -> IO [Goal]
simplifyConstraintTerms s gs =
  debugBlock s "Simplifying terms" $ return (map simpGoal gs)
  where simpGoal g = g { goal = simpProp (goal g) }


solveConstraints :: Num.Solver ->
                    [Goal] {- We may use these, but don't try to solve,
                              we already tried and failed. -} ->
                    [Goal] {- Need to solve these -} ->
                    IO (Either [Goal] [Goal])
                    -- ^ Left: contradiciting goals,
                    --   Right: goals that were not solved, or sub-goals
                    --          for solved goals.  Does not include "old"
solveConstraints s otherGs gs0 =
  debugBlock s "Solving constraints" $ solveClassCts [] [] gs0

  where
  otherNumerics = [ g | Right g <- map Num.numericRight otherGs ]

  solveClassCts unsolvedClass numerics [] =
    do unsolvedNum <- solveNumerics s otherNumerics numerics
       return (Right (unsolvedClass ++ unsolvedNum))

  solveClassCts unsolved numerics (g : gs) =
    case Num.numericRight g of
      Right n -> solveClassCts unsolved (n : numerics) gs
      Left c  ->
        case classStep c of
          Unsolvable          -> return (Left [g])
          Unsolved            -> solveClassCts (g : unsolved) numerics gs
          Solved Nothing subs -> solveClassCts unsolved numerics (subs ++ gs)
          Solved (Just su) _  -> panic "solveClassCts"
                                          [ "Unexpected substituion", show su ]


solveNumerics :: Num.Solver ->
                 [(Goal,Num.Prop)] {- ^ Consult these -} ->
                 [(Goal,Num.Prop)] {- ^ Solve these -}   ->
                 IO [Goal]
solveNumerics s consultGs solveGs =
  Num.withScope s $
    do _   <- Num.assumeProps s (map (goal . fst) consultGs)
       Num.simplifyProps s (map Num.knownDefined solveGs)


computeImprovements :: Num.Solver -> [Goal] -> IO (Either [Goal] Subst)
computeImprovements s gs =
  debugBlock s "Computing improvements" $
  do let nums = [ g | Right g <- map Num.numericRight gs ]
     res <- Num.withScope s $
        do _  <- Num.assumeProps s (map (goal . fst) nums)
           mb <- Num.check s
           case mb of
             Nothing       -> return Nothing
             Just (suish,_ps1) ->
               do let (su,_ps2) = importSplitImps suish
                  -- Num.check has already checked that the intervals are sane,
                  -- so we don't need to check for a broken interval here
                  Right ints <- Num.getIntervals s
                  return (Just (ints,su))
     case res of
       Just (ints,su)
         | isEmptySubst su
         , (x,t) : _ <- mapMaybe (improveByDefn ints) gs ->
           do let su' = singleSubst x t
              debugLog s ("Improve by definition: " ++ show (pp su'))
              return (Right su')

         | otherwise -> return (Right su)

       Nothing ->
         do bad <- Num.minimizeContradictionSimpDef s
                                                (map Num.knownDefined nums)
            return (Left bad)


improveByDefn :: Map TVar Interval -> Goal -> Maybe (TVar,Type)
improveByDefn ints Goal { .. } =
  do (var,ty) <- tryRewritePropAsSubst ints goal
     return (var,simpType ty)



-- | Import an improving substitutin (i.e., a bunch of equations)
-- into a Cryptol substitution (which is idempotent).
-- The substitution will contain only unification variables.
-- "Improvements" on skolem variables become additional constraints.
importSplitImps :: Map Num.Name Num.Expr -> (Subst, [Prop])
importSplitImps = mk . partitionEithers . map imp . Map.toList
  where
  mk (uni,props) = (listSubst (catMaybes uni), props)

  imp (x,e) = case (x, Num.importType e) of
                (Num.UserName tv, Just ty) ->
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
importImps :: Map Num.Name Num.Expr -> Subst
importImps = listSubst . map imp . Map.toList
  where
  imp (x,e) = case (x, Num.importType e) of
                (Num.UserName tv, Just ty) -> (tv,ty)
                _ -> panic "importImps" [ "Failed to import:", show x, show e ]



importSideConds :: [Num.Prop] -> ([Goal],[Num.Prop])
importSideConds = go [] []
  where
  go ok bad []     = ([ Goal CtImprovement emptyRange g | g <- ok], bad)
  go ok bad (p:ps) = case Num.importProp p of
                       Just p' -> go (p' ++ ok)    bad  ps
                       Nothing -> go        ok  (p:bad) ps






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

improveByDefaultingWith ::
  Num.Solver ->
  [TVar] ->   -- candidates for defaulting
  [Goal] ->   -- constraints
    IO  ( [TVar]    -- non-defaulted
        , [Goal]    -- new constraints
        , Subst     -- improvements from defaulting
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
       (mb,su1) <- simpGoals' s (newOthers ++ others ++ apSubst su fins)
       case mb of
         Right gs1 ->
           let warn (x,t) =
                 case x of
                   TVFree _ _ _ d -> DefaultingTo d t
                   TVBound {} -> panic "Crypto.TypeCheck.Infer"
                     [ "tryDefault attempted to default a quantified variable."
                     ]

               newSu = su1 @@ su     -- XXX: is that right?
               names = substBinds newSu

            in return ( [ a | a <- as, not (a `Set.member` names) ]
                      , gs1
                      , newSu
                      , map warn defs
                      )



         -- Something went wrong, don't default.
         Left _ -> return (as,ps,su1 @@ su,[])


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


-- | Try to pick a reasonable instantiation for an expression, with
-- the given type.  This is useful when we do evaluation at the REPL.
-- The resulting types should satisfy the constraints of the schema.
defaultReplExpr :: Num.Solver -> Expr -> Schema
             -> IO (Maybe ([(TParam,Type)], Expr))
defaultReplExpr so e s =
  if all (\v -> kindOf v == KNum) (sVars s)
     then do let params = map tpVar (sVars s)
             mbSubst <- tryGetModel so params (sProps s)
             case mbSubst of
               Just su ->
                 do (res,su1) <- simpGoals' so (map (makeGoal su) (sProps s))
                    return $
                      case res of
                        Right [] | isEmptySubst su1 ->
                         do tys <- mapM (bindParam su) params
                            return (zip (sVars s) tys, appExpr tys)
                        _ -> Nothing
               _ -> return Nothing

     else return Nothing
  where
  makeGoal su p = Goal { goalSource = error "goal source"
                       , goalRange  = error "goal range"
                       , goal       = apSubst su p
                       }

  bindParam su tp =
    do let ty  = TVar tp
           ty' = apSubst su ty
       guard (ty /= ty')
       return ty'

  appExpr tys = foldl (\e1 _ -> EProofApp e1) (foldl ETApp e tys) (sProps s)



-- | Attempt to default the given constraints by asserting them in the SMT
-- solver, and asking it for a model.
tryGetModel ::
  Num.Solver ->
  [TVar] ->   -- variables to try defaulting
  [Prop] ->   -- constraints
    IO (Maybe Subst)
tryGetModel s xs ps =
  -- We are only interested in finite instantiations
  Num.getModel s (map (pFin . TVar) xs ++ ps)

--------------------------------------------------------------------------------

simpType :: Type -> Type
simpType ty = fromMaybe ty (simpTypeMaybe ty)

simpProp :: Prop -> Prop
simpProp p = case p of
              TUser f ts q -> TUser f (map simpType ts) (simpProp q)
              TCon c ts    -> TCon c (map simpType ts)
              TVar {}      -> panic "simpProp" ["variable", show p]
              TRec {}      -> panic "simpProp" ["record", show p]




simpTypeMaybe :: Type -> Maybe Type
simpTypeMaybe ty =
  case ty of
    TCon c ts ->
      case c of
        TF {}    -> do e  <- Num.exportType ty
                       e1 <- Num.crySimpExprMaybe e
                       Num.importType e1

        _        -> TCon c `fmap` anyJust simpTypeMaybe ts

    TVar _       -> Nothing
    TUser x ts t -> TUser x ts `fmap` simpTypeMaybe t
    TRec fs      ->
      do let (ls,ts) = unzip fs
         ts' <- anyJust simpTypeMaybe ts
         return (TRec (zip ls ts'))



--------------------------------------------------------------------------------
_testSimpGoals :: IO ()
_testSimpGoals = Num.withSolver cfg $ \s ->
  do _ <- Num.assumeProps s asmps
     _mbImps <- Num.check s


     (mb,_) <- simpGoals' s gs
     case mb of
       Right _  -> debugLog s "End of test"
       Left _   -> debugLog s "Impossible"
  where
  cfg = SolverConfig { solverPath = "z3"
                     , solverArgs = [ "-smt2", "-in" ]
                     , solverVerbose = 1
                     }

  asmps = []

  gs    = map fakeGoal [ tv 0 =#= tMin (num 10) (tv 1)
                       , tv 1 =#= num 10
                       ]


  fakeGoal p = Goal { goalSource = undefined, goalRange = undefined, goal = p }
  tv n  = TVar (TVFree n KNum Set.empty (text "test var"))
  _btv n = TVar (TVBound n KNum)
  num x = tNum (x :: Int)




