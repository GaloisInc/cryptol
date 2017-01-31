{-# LANGUAGE Safe, PatternGuards #-}
module Cryptol.TypeCheck.Solver.Numeric
  ( cryIsEqual, cryIsNotEqual, cryIsGeq
  ) where

import Data.Map(Map)

import Cryptol.TypeCheck.PP
import Cryptol.TypeCheck.Type
import Cryptol.TypeCheck.Solver.Types
import Cryptol.TypeCheck.Solver.InfNat
import Cryptol.TypeCheck.Solver.Numeric.Interval

cryIsEqual :: Map TVar Interval -> Type -> Type -> Solved
cryIsEqual = pBin PEqual (==)

cryIsNotEqual :: Map TVar Interval -> Type -> Type -> Solved
cryIsNotEqual = pBin PNeq (/=)

cryIsGeq     :: Map TVar Interval -> Type -> Type -> Solved
cryIsGeq = pBin PGeq (>=)


pBin :: PC -> (Nat' -> Nat' -> Bool) -> Map TVar Interval ->
                                          Type -> Type -> Solved
pBin tf p _i t1 t2
  | Just e <- tIsError t1  = Unsolvable e
  | Just e <- tIsError t2  = Unsolvable e
  | Just x <- tIsNat' t1
  , Just y <- tIsNat' t2 =
      if p x y
        then SolvedIf []
        else Unsolvable $ TCErrorMessage
                        $ "Predicate " ++ show (pp tf) ++ " does not hold for "
                              ++ show x ++ " and " ++ show y
pBin _ _ _ _ _ = Unsolved


