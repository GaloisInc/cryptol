{-# LANGUAGE PatternGuards #-}
module Cryptol.TypeCheck.SimpleSolver ( simplify , simplifyStep) where

import Cryptol.TypeCheck.Type hiding
  ( tAdd, tSub, tMul, tDiv, tMod, tExp, tMin, tMax, tWidth
  , tLenFromThen, tLenFromThenTo)
import Cryptol.TypeCheck.Solver.Types
import Cryptol.TypeCheck.Solver.Numeric.Fin(cryIsFinType)
import Cryptol.TypeCheck.Solver.Numeric(cryIsEqual, cryIsNotEqual, cryIsGeq)
import Cryptol.TypeCheck.Solver.Class(solveArithInst,solveCmpInst)

simplify :: Ctxt -> Prop -> Prop
simplify ctxt p =
  case simplifyStep ctxt p of
    Unsolvable e -> pError e
    Unsolved     -> p
    SolvedIf ps  -> pAnd (map (simplify ctxt) ps)


simplifyStep :: Ctxt -> Prop -> Solved
simplifyStep ctxt prop =
  case tNoUser prop of
    TCon (PC PTrue)  []       -> SolvedIf []
    TCon (PC PAnd)   [l,r]    -> SolvedIf [l,r]

    TCon (PC PArith) [ty]     -> solveArithInst ty
    TCon (PC PCmp)   [ty]     -> solveCmpInst   ty

    TCon (PC PFin)   [ty]     -> cryIsFinType ctxt ty

    TCon (PC PEqual) [t1,t2]  -> cryIsEqual ctxt t1 t2
    TCon (PC PNeq)  [t1,t2]   -> cryIsNotEqual ctxt t1 t2
    TCon (PC PGeq)  [t1,t2]   -> cryIsGeq ctxt t1 t2

    _                         -> Unsolved


