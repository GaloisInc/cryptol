{-# LANGUAGE PatternGuards #-}

-- | Simplification of `fin` constraints.
module Cryptol.TypeCheck.Solver.Numeric.Fin where

import Data.Map (Map)

import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.InferTypes
import Cryptol.TypeCheck.Solver.Numeric.Interval
import Cryptol.TypeCheck.Solver.InfNat


cryIsFin :: Map TVar Interval -> Goal -> Solved
cryIsFin varInfo g =
  case pIsFin (goal g) of
    Just ty -> cryIsFinType varInfo g ty
    Nothing -> Unsolved

cryIsFinType :: Map TVar Interval -> Goal -> Type -> Solved
cryIsFinType varInfo g ty =
  case tNoUser ty of

    TCon (TC tc) [] | TCNum _ <- tc -> solved []

    TCon (TF f) ts ->
      case (f,ts) of
        (TCAdd,[t1,t2]) -> solved [ pFin t1, pFin t2 ]
        (TCSub,[t1,_ ]) -> solved [ pFin t1 ]

        -- fin (x * y)
        (TCMul,[t1,t2])
          | iLower i1 >= Nat 1 && iIsFin i1 -> solved [ pFin t2 ]
          | iLower i2 >= Nat 1 && iIsFin i2 -> solved [ pFin t1 ]

          | iLower i1 >= Nat 1 &&
            iLower i2 >= Nat 1 -> solved [ pFin t1, pFin t2 ]

          | iIsFin i1 && iIsFin i2 -> solved []
          where
          i1 = typeInterval varInfo t1
          i2 = typeInterval varInfo t2


        (TCDiv, [t1,_])  -> solved [ pFin t1 ]
        (TCMod, [_,_])   -> solved []

        -- fin (x ^ y)
        (TCExp, [t1,t2])
          | iLower i1 == Inf   -> solved [ t2 =#= tZero ]
          | iLower i2 == Inf   -> solved [ tOne >== t1 ]

          | iLower i1 >= Nat 2 -> solved [ pFin t1, pFin t2 ]
          | iLower i2 >= Nat 1 -> solved [ pFin t1, pFin t2 ]

          | Just x <- iUpper i1, x <= Nat 1 -> solved []
          | Just (Nat 0) <- iUpper i2       -> solved []
          where
          i1 = typeInterval varInfo t1
          i2 = typeInterval varInfo t2

        -- fin (min x y)
        (TCMin, [t1,t2])
          | iIsFin i1  -> solved []
          | iIsFin i2  -> solved []
          | Just x <- iUpper i1, x <= iLower i2 -> solved [ pFin t1 ]
          | Just x <- iUpper i2, x <= iLower i1 -> solved [ pFin t2 ]
          where
          i1 = typeInterval varInfo t1
          i2 = typeInterval varInfo t2

        (TCMax, [t1,t2])          -> solved [ pFin t1, pFin t2 ]
        (TCWidth, [t1])           -> solved [ pFin t1 ]
        (TCLenFromThen,[_,_,_])   -> solved []
        (TCLenFromThenTo,[_,_,_]) -> solved []

        _ -> Unsolved

    _ -> Unsolved


  where
  solved ps = Solved Nothing [ g { goal = p } | p <- ps ]


