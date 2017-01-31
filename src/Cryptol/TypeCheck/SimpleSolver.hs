module Cryptol.TypeCheck.SimpleSolver (simplify) where

import Data.Map(Map)

import Cryptol.TypeCheck.Type
import Cryptol.TypeCheck.InferTypes(Solved(..))
import Cryptol.TypeCheck.Solver.Numeric.Fin(cryIsFinType)
import Cryptol.TypeCheck.Solver.Numeric.Interval(Interval)
import Cryptol.TypeCheck.Solver.Numeric(cryIsEqual, cryIsNotEqual, cryIsGeq)
import Cryptol.TypeCheck.Solver.Class(solveArithInst,solveCmpInst)

type Ctxt = Map TVar Interval

simplify :: Ctxt -> [Prop] -> Either TCErrorMessage [Prop]
simplify _ [] = Right []
simplify ctxt (p : ps) =
  case simplifyStep ctxt p of
    Unsolvable e -> Left e
    Unsolved     -> fmap (p :) (simplify ctxt ps)
    SolvedIf ps1 -> simplify ctxt (ps1 ++ ps)

simplifyStep :: Ctxt -> Prop -> Solved
simplifyStep ctxt prop =
  case tNoUser prop of
    TCon (PC PTrue)  []       -> SolvedIf []

    TCon (PC PArith) [ty]     -> solveArithInst ty
    TCon (PC PCmp)   [ty]     -> solveCmpInst   ty

    TCon (PC PFin)   [ty]     -> cryIsFinType ctxt ty

    TCon (PC PEqual) [t1,t2]  -> cryIsEqual ctxt t1 t2
    TCon (PC PNeq)  [t1,t2]   -> cryIsNotEqual ctxt t1 t2
    TCon (PC PGeq)  [t1,t2]   -> cryIsGeq ctxt t1 t2

    _                         -> Unsolved





