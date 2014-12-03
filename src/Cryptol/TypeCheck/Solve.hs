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
import           Cryptol.TypeCheck.Solver.InfNat(Nat'(..))
import qualified Cryptol.TypeCheck.Solver.CrySAT as CM

import           Cryptol.TypeCheck.Defaulting(tryDefaultWith)
import qualified Cryptol.Utils.Panic as P

import           Control.Monad(unless)
import           Data.List(partition)
import qualified Data.Set as Set
import qualified Data.Map as Map
import           Data.Map (Map)

import           Text.PrettyPrint

-- Add additional constraints that ensure validity of type function.
checkTypeFunction :: TFun -> [Type] -> [Prop]
checkTypeFunction TCSub [a,b]             = [ a >== b, pFin b]
checkTypeFunction TCDiv [a,b]             = [ b >== tOne, pFin a ]
checkTypeFunction TCMod [a,b]             = [ b >== tOne, pFin a ]
checkTypeFunction TCLenFromThen   [a,b,c] = [ pFin a, pFin b, pFin c, a =/= b ]
checkTypeFunction TCLenFromThenTo [a,b,c] = [ pFin a, pFin b, pFin c, a =/= b ]
checkTypeFunction _ _                     = []




fromVal :: Nat' -> Type
fromVal Inf     = tInf
fromVal (Nat n) = tNum n


type VarMap = Map Int TVar

exportProp :: Prop -> CM.Prop
exportProp ty =
  case ty of
    TUser _ _ t -> exportProp t
    TRec {}     -> err
    TVar {}     -> err
    TCon (PC pc) ts ->
      case (pc, map exportType ts) of
        (PFin, [t])       -> CM.Fin t
        (PEqual, [t1,t2]) -> t1 CM.:== t2
        (PNeq,   [t1,t2]) -> t1 CM.:== t2
        (PGeq,   [t1,t2]) -> t1 CM.:>= t2
        _                 -> err
    TCon _ _ -> err
  where
  err = panic "exportProp" [ "Unexpected type", show ty ]

exportType :: Type -> CM.Expr
exportType ty =
  case ty of
    TUser _ _ t -> exportType t
    TRec {}     -> err
    TVar x      -> CM.Var $ CM.toName $ exportVar x
    TCon tc ts  ->
      case tc of
        TC TCInf     -> CM.K Inf
        TC (TCNum x) -> CM.K (Nat x)
        TC _         -> err

        TF f ->
          case (f, map exportType ts) of
            (TCAdd, [t1,t2]) -> t1 CM.:+ t2
            (TCSub, [t1,t2]) -> t1 CM.:- t2
            (TCMul, [t1,t2]) -> t1 CM.:* t2
            (TCDiv, [t1,t2]) -> CM.Div t1 t2
            (TCMod, [t1,t2]) -> CM.Mod t1 t2
            (TCExp, [t1,t2]) -> t1 CM.:^^ t2
            (TCMin, [t1,t2]) -> CM.Min t1 t2
            (TCMax, [t1,t2]) -> CM.Max t1 t2
            (TCLg2, [t1])    -> CM.Lg2 t1
            (TCWidth, [t1])  -> CM.Width t1
            (TCLenFromThen, [t1,t2,t3])   -> CM.LenFromThen t1 t2 t3
            (TCLenFromThenTo, [t1,t2,t3]) -> CM.LenFromThenTo t1 t2 t3

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
  dump asmps0 goals >>
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
simplifyGoals initOrd gs1 = do dump [] gs1
                               solveSomeGoals [] False gs1
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



--------------------------------------------------------------------------------

-- A => B, NOT A \/ B
dump :: [Prop] -> [Goal] -> InferM()
dump asmps goals = io $ print doc
  where
  doc = vcat [ line "asmps"
             , vcat (map (CM.ppProp . CM.crySimplify . exportProp) asmps)
             , line "goals defined"
             , CM.ppProp $ CM.crySimplify
                         $ CM.cryAnds $ map CM.cryDefinedProp gs
             , line "goals"
             , CM.ppProp $ CM.crySimplify $ CM.cryAnds gs
             ]

  line msg  = text "--" <+> text msg <+>
              text (replicate (80 - 4 - length msg) '-')


  gs        = map (exportProp . goal) goals
