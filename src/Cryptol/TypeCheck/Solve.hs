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
  , wfType
  , wfTypeFunction
  , improveByDefaulting
  , defaultReplExpr
  , simpType
  , simpTypeMaybe
  ) where

import           Cryptol.Parser.AST(LQName, thing)
import           Cryptol.Parser.Position (emptyRange)
import           Cryptol.TypeCheck.AST
import           Cryptol.TypeCheck.Monad
import           Cryptol.TypeCheck.Subst
                    (apSubst,fvs,singleSubst,
                          emptySubst,Subst,listSubst, (@@), Subst)
import           Cryptol.TypeCheck.Solver.Class
import           Cryptol.TypeCheck.Solver.Selector(tryHasGoal)
import qualified Cryptol.TypeCheck.Solver.Numeric.AST as Num
import qualified Cryptol.TypeCheck.Solver.Numeric.ImportExport as Num
import qualified Cryptol.TypeCheck.Solver.Numeric.Simplify1 as Num
import qualified Cryptol.TypeCheck.Solver.Numeric.SimplifyExpr as Num
import qualified Cryptol.TypeCheck.Solver.CrySAT as Num
import           Cryptol.TypeCheck.Solver.CrySAT (debugBlock, DebugLog(..))
import           Cryptol.Utils.Panic(panic)
import           Cryptol.Utils.Misc(anyJust)
import           Cryptol.Parser.Position(rCombs)

import           Control.Monad (unless, guard)
import           Data.Either(partitionEithers)
import           Data.Maybe(catMaybes, fromMaybe)
import           Data.Map ( Map )
import qualified Data.Map as Map
import           Data.Set ( Set )
import qualified Data.Set as Set

import           Text.PrettyPrint(text)

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

-- XXX at the moment, we try to solve class constraints before solving fin
-- constraints, as they could yield fin constraints.  At some point, it would
-- probably be good to try solving all of these in one big loop.
simplifyAllConstraints :: InferM ()
simplifyAllConstraints =
  do mapM_  tryHasGoal =<< getHasGoals
     gs <- getGoals
     cfg <- getSolverConfig
     mb <- io (Num.withSolver cfg (`simpGoals` gs))
     case mb of
       Right (gs1,su) -> extendSubst su >> addGoals gs1
       Left badGs     -> mapM_ (recordError . UnsolvedGoal) badGs


proveImplication :: LQName -> [TParam] -> [Prop] -> [Goal] -> InferM Subst
proveImplication lnam as ps gs =
  do evars <- varsWithAsmps
     cfg <- getSolverConfig
     mbErr <- io (proveImplicationIO cfg lnam evars as ps gs)
     case mbErr of
       Right (su,ws) ->
          do mapM_ recordWarning ws
             return su
       Left err -> recordError err >> return emptySubst


proveImplicationIO :: SolverConfig
                   -> LQName   -- ^ Checking this functi
                   -> Set TVar -- ^ These appear in the env., and we should
                               -- not try to default the
                   -> [TParam] -- ^ Type parameters
                   -> [Prop]   -- ^ Assumed constraint
                   -> [Goal]   -- ^ Collected constraints
                   -> IO (Either Error (Subst,[Warning]))
proveImplicationIO _   _     _         _  [] [] = return (Right (emptySubst,[]))
proveImplicationIO cfg lname varsInEnv as ps gs =
  Num.withSolver cfg $ \s ->
  debugBlock s "proveImplicationIO" $

  do debugBlock s "assumes" (debugLog s ps)
     debugBlock s "shows"   (debugLog s gs)
     debugLog s "------------------"


     _simpPs <- Num.assumeProps s ps

     mbImps <- Num.check s
     case mbImps of

       Nothing ->
         do debugLog s "(contradiction in assumptions)"
            return $ Left $ UnusableFunction (thing lname) ps

       Just (imps,extra) ->
         do let su  = importImps imps
                gs0 = apSubst su gs

            debugBlock s "improvement from assumptions:" $ debugLog s su

            let (scs,invalid) = importSideConds extra
            unless (null invalid) $
              panic "proveImplicationIO" ( "Unable to import all side conditions:"
                                              : map (show . Num.ppProp) invalid )

            let gs1 = filter ((`notElem` ps) . goal) gs0
            mb <- simpGoals s (scs ++ gs1)

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




-- | Class goals go on the left, numeric goals go on the right.
numericRight :: Goal -> Either Goal (Goal, Num.Prop)
numericRight g  = case Num.exportProp (goal g) of
                    Just p  -> Right (g, p)
                    Nothing -> Left g

_testSimpGoals :: IO ()
_testSimpGoals = Num.withSolver cfg $ \s ->
  do mapM_ dump asmps
     mapM_ (dump .goal) gs

     _ <- Num.assumeProps s asmps
     mb <- simpGoals s gs
     case mb of
       Right _  -> debugLog s "End of test"
       Left _   -> debugLog s "Impossible"
  where
  cfg = SolverConfig { solverPath = "cvc4"
                     , solverArgs = [ "--lang=smt2", "--incremental" ]
                     , solverVerbose = 1
                     }

  asmps = [] -- [ pFin (tv 0) ]
  gs = map fakeGoal [ pFin (num 2 .^. tv 0 .-. num 1) ]

    -- [ tv 0 =#= tInf, tMod (num 3) (tv 0) =#= num 4 ]

  fakeGoal p = Goal { goalSource = undefined, goalRange = undefined, goal = p }
  tv n = TVar (TVFree n KNum Set.empty (text "test var"))
  num x = tNum (x :: Int)

  dump a = do putStrLn "-------------------_"
              case Num.exportProp a of
                Just b     -> do print $ Num.ppProp' $ Num.propToProp' b
                                 putStrLn "-------------------"
                Nothing    -> print "can't export"


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

         updCt prop g = case Num.importProp prop of
                               Just [g1] -> g { goal = g1 }

                               r -> panic "simpGoals"
                                      [ "Unexpected import results"
                                      , show r
                                      ]

     case numCts of
       [] -> do debugBlock s "After simplification (no numerics):"
                  $ debugLog s unsolvedClassCts
                return $ Right (unsolvedClassCts, emptySubst)

       _  -> do mbOk <- Num.prepareConstraints s updCt numCts
                case mbOk of
                  Left bad -> return (Left bad)
                  Right (nonDef,def,imps,wds) ->

                    -- XXX: What should we do with the extra props...
                    do let (su,extraProps) = importSplitImps imps

                           (sideConds,invalid) = importSideConds wds


                           inIfForm =
                              Num.ppProp' $
                              Num.propToProp' $
                              case def of
                                [] -> Num.PTrue
                                _  -> foldr1 (Num.:&&)
                                    $ map Num.dpSimpExprProp def

                           def1 = eliminateSimpleGEQ def
                           toGoal =
                             case map Num.dpData def1 of
                               []  -> case gs0 of
                                        g : _ -> \p -> g { goal = p }
                                        [] -> panic "simplification"
                                                [ "Goals out of no goals." ]

                               [g] -> \p -> g { goal = p }
                               gs  -> \p ->
                                 Goal { goalRange = rCombs (map goalRange gs)
                                      , goalSource = CtImprovement
                                      , goal = p }

                       unless (null invalid) $
                           panic "simpGoals" ( "Unable to import required well-definedness constraints:"
                                             : map (show . Num.ppProp) invalid )

                       if null nonDef
                         then do debugLog s "(all constraints are well-defined)"
                                 debugBlock s "In If-form:" $
                                    debugLog s inIfForm

                         else debugBlock s "Non-well defined constratins:" $
                                debugLog s nonDef

                       def2 <- Num.simplifyProps s def1
                       let allCts = apSubst su $ map toGoal extraProps ++
                                    nonDef ++
                                    unsolvedClassCts ++
                                    def2 ++
                                    sideConds

                       debugBlock s "After simplification:" $
                          do debugLog s allCts
                             debugLog s su

                       -- XXX: Apply subst to class constraints and go again?
                       return $ Right ( allCts, su )
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
  SolverConfig ->
  [TVar] ->   -- candidates for defaulting
  [Goal] ->   -- constraints
    IO  ( [TVar]    -- non-defaulted
        , [Goal]    -- new constraints
        , Subst     -- improvements from defaulting
        , [Warning] -- warnings about defaulting
        )
improveByDefaulting cfg xs gs = Num.withSolver cfg $ \s -> improveByDefaultingWith s xs gs

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


-- | Try to pick a reasonable instantiation for an expression, with
-- the given type.  This is useful when we do evaluation at the REPL.
-- The resulting types should satisfy the constraints of the schema.
defaultReplExpr :: SolverConfig -> Expr -> Schema
             -> IO (Maybe ([(TParam,Type)], Expr))
defaultReplExpr cfg e s =
  if all (\v -> kindOf v == KNum) (sVars s)
     then do let params = map tpVar (sVars s)
             mbSubst <- tryGetModel cfg params (sProps s)
             case mbSubst of
               Just su -> return $ do tys <- mapM (bindParam su) params
                                      return (zip (sVars s) tys, appExpr tys)
               Nothing -> return Nothing

     else return Nothing

  where

  bindParam su tp =
    do let ty  = TVar tp
           ty' = apSubst su ty
       guard (ty /= ty')
       return ty'

  appExpr tys = foldl (\e1 _ -> EProofApp e1) (foldl ETApp e tys) (sProps s)



-- | Attempt to default the given constraints by asserting them in the SMT
-- solver, and asking it for a model.
tryGetModel ::
  SolverConfig ->
  [TVar] ->   -- variables to try defaulting
  [Prop] ->   -- constraints
    IO (Maybe Subst)
tryGetModel cfg xs ps =
  Num.withSolver cfg $ \ s ->
    -- We are only interested in finite instantiations
    Num.getModel s (map (pFin . TVar) xs ++ ps)

--------------------------------------------------------------------------------

simpType :: Type -> Type
simpType ty = fromMaybe ty (simpTypeMaybe ty)

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



