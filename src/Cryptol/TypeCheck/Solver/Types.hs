module Cryptol.TypeCheck.Solver.Types where

import Cryptol.TypeCheck.Type
import Cryptol.TypeCheck.PP

data Solved = SolvedIf [Prop]           -- ^ Solved, assuming the sub-goals.
            | Unsolved                  -- ^ We could not solve the goal.
            | Unsolvable TCErrorMessage -- ^ The goal can never be solved.
              deriving (Show)

instance PP Solved where
  ppPrec _ res =
    case res of
      SolvedIf ps  -> text "solved" $$ nest 2 (vcat (map pp ps))
      Unsolved     -> text "unsolved"
      Unsolvable e -> text "unsolvable" <> colon <+> text (tcErrorMessage e)
