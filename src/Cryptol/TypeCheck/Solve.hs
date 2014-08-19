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
import           Cryptol.TypeCheck.Solver.CrySAT hiding (Expr,Name,Prop)
import qualified Cryptol.TypeCheck.Solver.CrySAT as SAT
import           Cryptol.TypeCheck.Defaulting(tryDefaultWith)
import qualified Cryptol.Utils.Panic as P

import           Control.Monad(unless)
import           Data.List(partition)
import qualified Data.Set as Set
import qualified Data.Map as Map
import           Data.Map (Map)

-- Add additional constraints that ensure validity of type function.
checkTypeFunction :: TFun -> [Type] -> [Prop]
checkTypeFunction TCSub [a,b]             = [ a >== b, pFin b]
checkTypeFunction TCDiv [a,b]             = [ b >== tOne, pFin a ]
checkTypeFunction TCMod [a,b]             = [ b >== tOne, pFin a ]
checkTypeFunction TCLenFromThen   [a,b,c] = [ pFin a, pFin b, pFin c, a =/= b ]
checkTypeFunction TCLenFromThenTo [a,b,c] = [ pFin a, pFin b, pFin c, a =/= b ]
checkTypeFunction _ _                     = []




{-
mkAsmpSet :: [Prop] -> Maybe ([Prop], PropSet, VarMap)
mkAsmpSet ps =
  case checkSat propSet of
    Unsat   -> Nothing
    Sat su  -> 

  where
  allPs        = concatMap expandProp ps
  (numPs,clPs) = allPs

  propSet      = foldr assert noProps $ map exportProp numPs

  numVars = filter ((KNum ==) . kindOf) $ Set.toList $ fvs allPs

  varMap  = map.fromList [ (exportVar x, x) | x <- numVars ]

mkAsmpSet :: [Prop] -> (VarMap, PropSet)


simpWFGoals :: [Prop] -> InferM ()
simpWFGoals givenProps =
  do 

go False [] =<< getGoals
  where
  givens = undefined
  varMap = undefined

  go chages done [] = do addGoals done
                         when changes =<< simpWFGoals (applySubst givenProps)

  go changes done (g : gs) =
    do (c,done') <- addWF varMap givens done g
       if c then go True done' gs
            else go changes done' gs
-}

-- Add a well-formed constraint to a set of goals.
-- Returns a boolean indicating if any unification occured, and a list of
-- updated goals.
addWF :: VarMap -> PropSet -> [Goal] -> Goal -> InferM (Bool,[Goal])
addWF vars givens otherWanteds g

  -- A class constraint
  | not $ pIsNumeric (goal g) =
    case classStep g of
      Unsolvable -> do recordError $ UnsolvedGoal g
                       return (False, otherWanteds)
      Unsolved   -> return (False, g : otherWanteds)
      Solved Nothing [] -> return (False, otherWanteds)
      Solved mbSu ps    -> do case mbSu of
                                Nothing -> return ()
                                Just su -> extendSubst su
                              return (True, ps ++ otherWanteds)

  -- A numeric constraint
  | otherwise =
  do let new       = getGoal g
         allOther  = addOthers numWanteds givens

     if prove allOther new
        then return (False, otherWanteds)
        else do let allFacts = assert new allOther
                case checkSat allFacts of
                  Unsat   -> do recordError (UnsolvedGoal g)
                                return (False, otherWanteds)
                  Sat m   -> tryImprove allFacts m
                  Unknown -> tryImprove allFacts []

  where
  (numWanteds,classWanted) = partition (pIsNumeric . goal) otherWanteds

  prove as b = case checkSat (assert (Not b) as) of
                 Unsat -> True
                 _     -> False

  getGoal w = exportProp (goal w)

  addOther :: Goal -> PropSet -> PropSet
  addOther w fs = assert (getGoal w) fs

  addOthers :: [Goal] -> PropSet -> PropSet
  addOthers ws fs = foldr addOther fs ws

  tryImprove fs concrete =
    do cs1 <- mapM (tryConcrete fs) concrete

       let pairs (x : xs) = [ (x,y) | y <- xs ] ++ pairs xs
           pairs []       = []

       cs2 <- mapM (tryVar fs) $ pairs $ Map.keys vars

       let ws = simpOthers (addOther g givens) [g] numWanteds
       return (or cs1 || or cs2, ws ++ classWanted)


  simpOthers :: PropSet -> [Goal] -> [Goal] -> [Goal]
  simpOthers fs stay (q:qs)
    | prove (addOthers qs fs) qF = simpOthers fs stay qs
    | otherwise                  = simpOthers (assert qF fs) (q : stay) qs
      where qF = getGoal q

  simpOthers _ stay [] = stay


  lkpVar :: Int -> Type
  lkpVar x = case Map.lookup x vars of
               Just tv -> TVar tv
               Nothing -> panic "addWF" [ "Missing variable", show x ]

  mkVar :: Int -> SAT.Expr
  mkVar x = Var (toName x)

  tryConcrete :: PropSet -> (Int,InfNat) -> InferM Bool
  tryConcrete m (x,v)
    | prove m (mkVar x :== K v) = bindVar x (fromVal v)
    | otherwise                 = return False

  tryVar :: PropSet -> (Int,Int) -> InferM Bool
  tryVar m (x,y)
    | prove m (mkVar x :== mkVar y) = bindVar x (lkpVar y)
    | otherwise                     = return False

  bindVar :: Int -> Type -> InferM Bool
  bindVar x right = do let left = lkpVar x
                       ps <- unify left right
                       case ps of
                         [] -> return True
                         _  -> return False

    {- The unification probelm we try to solve is of the form: `x = T`
       The only way for `unify` to return sub-constraints on such a type
       is if `x` was a rigid varible.  We are not interested in such
       improvements:  if this facts could be proved from the givens, we'd
       know it already.  Otherwise, we won't be abe to discharge the current
       goal, but we prefer to report the error in terms of the actual
       goal that we were trying to solve, rather than some implied constraint.
    -}



fromVal :: InfNat -> Type
fromVal Inf     = tInf
fromVal (Nat n) = tNum n


type VarMap = Map Int TVar

exportProp :: Prop -> SAT.Prop
exportProp ty =
  case ty of
    TUser _ _ t -> exportProp t
    TRec {}     -> err
    TVar {}     -> err
    TCon (PC pc) ts ->
      case (pc, map exportType ts) of
        (PFin, [t])       -> Fin t
        (PEqual, [t1,t2]) -> t1 :== t2
        (PNeq,   [t1,t2]) -> t1 :== t2
        (PGeq,   [t1,t2]) -> t1 :>= t2
        _                 -> err
    TCon _ _ -> err
  where
  err = panic "exportProp" [ "Unexpected type", show ty ]

exportType :: Type -> SAT.Expr
exportType ty =
  case ty of
    TUser _ _ t -> exportType t
    TRec {}     -> err
    TVar x      -> Var $ toName $ exportVar x
    TCon tc ts  ->
      case tc of
        TC TCInf     -> K Inf
        TC (TCNum x) -> K (Nat x)
        TC _         -> err

        TF f ->
          case (f, map exportType ts) of
            (TCAdd, [t1,t2]) -> t1 :+ t2
            (TCSub, [t1,t2]) -> t1 :- t2
            (TCMul, [t1,t2]) -> t1 :* t2
            (TCDiv, [t1,t2]) -> Div t1 t2
            (TCMod, [t1,t2]) -> Mod t1 t2
            (TCExp, [t1,t2]) -> t1 :^^ t2
            (TCMin, [t1,t2]) -> Min t1 t2
            (TCMax, [t1,t2]) -> Max t1 t2
            (TCLg2, [t1])    -> Lg2 t1
            (TCWidth, [t1])  -> Width t1
            (TCLenFromThen, [t1,t2,t3]) -> LenFromThen t1 t2 t3
            (TCLenFromThenTo, [t1,t2,t3]) -> LenFromThenTo t1 t2 t3

            _ -> err

        PC _ -> err


  where
  err = panic "exportType" [ "Unexpected type", show ty ]

exportVar :: TVar -> Int
exportVar (TVFree x _ _ _) = 2 * x        -- Free vars are even
exportVar (TVBound x _)    = 2 * x + 1    -- Bound vars are odd


--------------------------------------------------------------------------------

panic :: String -> [String] -> a
panic x m = P.panic ("Cryptol.TypeCheck.Solve." ++ x) m

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




