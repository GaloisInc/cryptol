-- |
-- Module      :  Cryptol.TypeCheck.Solver.Numeric.Fin
-- Copyright   :  (c) 2015-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Simplification of `fin` constraints.

{-# LANGUAGE PatternGuards #-}
module Cryptol.TypeCheck.Solver.Numeric.Fin where

import Data.Map (Map)
import qualified Data.Map as Map

import Cryptol.TypeCheck.Type
import Cryptol.TypeCheck.Solver.Types
import Cryptol.TypeCheck.Solver.Numeric.Interval
import Cryptol.TypeCheck.Solver.InfNat


cryIsFin :: Map TVar Interval -> Prop -> Solved
cryIsFin varInfo p =
  case pIsFin p of
    Just ty -> cryIsFinType varInfo ty
    Nothing -> Unsolved

cryIsFinType :: Map TVar Interval -> Type -> Solved
cryIsFinType varInfo ty =
  case tNoUser ty of

    TVar x | Just i <- Map.lookup x varInfo
           , iIsFin i -> SolvedIf []

    TCon (TC tc) []
      | TCNum _ <- tc -> SolvedIf []
      | TCInf   <- tc ->
        Unsolvable $ TCErrorMessage "Expected a finite type, but found `inf`."

    TCon (TF f) ts ->
      case (f,ts) of
        (TCAdd,[t1,t2]) -> SolvedIf [ pFin t1, pFin t2 ]
        (TCSub,[t1,_ ]) -> SolvedIf [ pFin t1 ]

        -- fin (x * y)
        (TCMul,[t1,t2])
          | iLower i1 >= Nat 1 && iIsFin i1 -> SolvedIf [ pFin t2 ]
          | iLower i2 >= Nat 1 && iIsFin i2 -> SolvedIf [ pFin t1 ]

          | iLower i1 >= Nat 1 &&
            iLower i2 >= Nat 1 -> SolvedIf [ pFin t1, pFin t2 ]

          | iIsFin i1 && iIsFin i2 -> SolvedIf []
          where
          i1 = typeInterval varInfo t1
          i2 = typeInterval varInfo t2


        (TCDiv, [t1,_])  -> SolvedIf [ pFin t1 ]
        (TCMod, [_,_])   -> SolvedIf []

        -- fin (x ^ y)
        (TCExp, [t1,t2])
          | iLower i1 == Inf   -> SolvedIf [ t2 =#= tZero ]
          | iLower i2 == Inf   -> SolvedIf [ tOne >== t1 ]

          | iLower i1 >= Nat 2 -> SolvedIf [ pFin t1, pFin t2 ]
          | iLower i2 >= Nat 1 -> SolvedIf [ pFin t1, pFin t2 ]

          | Just x <- iUpper i1, x <= Nat 1 -> SolvedIf []
          | Just (Nat 0) <- iUpper i2       -> SolvedIf []
          where
          i1 = typeInterval varInfo t1
          i2 = typeInterval varInfo t2

        -- fin (min x y)
        (TCMin, [t1,t2])
          | iIsFin i1  -> SolvedIf []
          | iIsFin i2  -> SolvedIf []
          | Just x <- iUpper i1, x <= iLower i2 -> SolvedIf [ pFin t1 ]
          | Just x <- iUpper i2, x <= iLower i1 -> SolvedIf [ pFin t2 ]
          where
          i1 = typeInterval varInfo t1
          i2 = typeInterval varInfo t2

        (TCMax, [t1,t2])          -> SolvedIf [ pFin t1, pFin t2 ]
        (TCWidth, [t1])           -> SolvedIf [ pFin t1 ]
        (TCCeilDiv, [_,_])        -> SolvedIf []
        (TCCeilMod, [_,_])        -> SolvedIf []
        (TCLenFromThenTo,[_,_,_]) -> SolvedIf []

        _ -> Unsolved

    _ -> Unsolved


