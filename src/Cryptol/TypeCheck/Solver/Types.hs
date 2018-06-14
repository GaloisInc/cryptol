module Cryptol.TypeCheck.Solver.Types where

import Data.Map(Map)

import Cryptol.TypeCheck.Type
import Cryptol.TypeCheck.PP
import Cryptol.TypeCheck.Solver.Numeric.Interval

type Ctxt = Map TVar Interval

data Solved = SolvedIf [Prop]           -- ^ Solved, assuming the sub-goals.
            | Unsolved                  -- ^ We could not solve the goal.
            | Unsolvable TCErrorMessage -- ^ The goal can never be solved.
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
      Unsolvable e -> text "unsolvable" <.> colon <+> text (tcErrorMessage e)
