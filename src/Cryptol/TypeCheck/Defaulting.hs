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

tryDefault :: [TVar] -> [Goal] -> ([TVar], [Goal], Subst, [Warning])
tryDefault = tryDefaultWith noFacts

tryDefaultWith :: OrdFacts -> [TVar] -> [Goal] ->
                                          ([TVar], [Goal], Subst, [Warning])
tryDefaultWith ordM0 as ps =
  classify (Map.fromList [ (a,([],Set.empty)) | a <- as ]) [] [] ps

  where
  -- leq: candidate definitions (i.e. of the form x >= t, x `notElem` fvs t)
  --      for each of these, we keep the list of `t`, and the free vars in them.
  -- fins: all `fin` constraints
  -- others: any other constraints
  classify leqs fins others [] =
    let -- First, we use the `leqs` to choose some definitions.
       (defs, newOthers)  = select [] [] (fvs others) (Map.toList leqs)
       su                 = listSubst defs

       -- Do this to simplify the instantiated "fin" constraints.
       (m, bad, oth)      = goalOrderModel ordM0
                                  (newOthers ++ others ++ apSubst su fins)
    in case bad of
         -- All good.
         [] ->
            let warn (x,t) =
                  case x of
                    TVFree _ _ _ d -> DefaultingTo d t
                    TVBound {} -> panic "Crypto.TypeCheck.Infer"
                      [ "tryDefault attempted to default a quantified variable."
                      ]

            in ( [ a | a <- as, a `notElem` map fst defs ]
               , ordFactsToGoals m ++ nubBy (\x y -> goal x == goal y) oth
               , su
               , map warn defs
               )


         -- Something went wrong, don't default.
         _  -> (as,ps,emptySubst,[])



  classify leqs fins others (prop : more) =
      case tNoUser (goal prop) of
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
  select yes no _ [] = ([ (x, simpType noFacts t) | (x,t) <- yes ] ,no)
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

