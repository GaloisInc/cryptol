{-# Language OverloadedStrings, DeriveGeneric, DeriveAnyClass #-}
{-# LANGUAGE Safe #-}
module Cryptol.TypeCheck.Solver.Types where

import Data.Map(Map)
import Data.Set(Set)

import Cryptol.TypeCheck.Type
import Cryptol.TypeCheck.PP
import Cryptol.TypeCheck.Solver.Numeric.Interval

data Ctxt =
  SolverCtxt
  { intervals :: Map TVar Interval
  , saturatedAsmps :: Set Prop
  } deriving Show

instance Semigroup Ctxt where
  SolverCtxt is1 as1 <> SolverCtxt is2 as2 = SolverCtxt (is1 <> is2) (as1 <> as2)

instance Monoid Ctxt where
  mempty = SolverCtxt mempty mempty


data Solved = SolvedIf [Prop]           -- ^ Solved, assuming the sub-goals.
            | Unsolved                  -- ^ We could not solve the goal.
            | Unsolvable                -- ^ The goal can never be solved.
              deriving (Show)



elseTry :: Solved -> Solved -> Solved
Unsolved `elseTry` x = x
x        `elseTry` _ = x

solveOpts :: [Solved] -> Solved
solveOpts [] = Unsolved
solveOpts (x : xs) = x `elseTry` solveOpts xs

matchThen :: Maybe a -> (a -> Solved) -> Solved
matchThen Nothing _  = Unsolved
matchThen (Just a) f = f a

guarded :: Bool -> Solved -> Solved
guarded True x = x
guarded False _ = Unsolved


instance PP Solved where
  ppPrec _ res =
    case res of
      SolvedIf ps  -> text "solved" $$ nest 2 (vcat (map pp ps))
      Unsolved     -> text "unsolved"
      Unsolvable   -> text "unsolvable"

