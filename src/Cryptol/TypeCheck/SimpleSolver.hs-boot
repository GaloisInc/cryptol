-- Cryptol.TypeCheck.Subst calls Cryptol.TypeCheck.SimpleSolver.simplify to
-- simplify types during substitution, but simplify does typeclass solving which
-- for nominal types requires substitution. This file exists to break the import
-- cycle.
module Cryptol.TypeCheck.SimpleSolver where

import Cryptol.TypeCheck.Type
import Cryptol.TypeCheck.Solver.Types

simplify :: Ctxt -> Prop -> Prop
