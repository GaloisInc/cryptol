{-# LANGUAGE BlockArguments #-}
{-# HLINT ignore "Redundant pure" #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Cryptol.TypeCheck.Solver.Numeric.Sampling where

import Control.Monad
import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Solver.InfNat
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Base as Base
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Constraints as Cons
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Preconstraints as Precons
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Sampling as Sampling
import Cryptol.TypeCheck.Solver.Numeric.Sampling.SolvedConstraints (elimDens, toSolvedConstraints)
import Cryptol.TypeCheck.Solver.Numeric.Sampling.System as Sys
import Cryptol.TypeCheck.Subst
import Data.Bifunctor (Bifunctor (bimap))
import qualified Data.Vector as V

{-
High-level description of numeric literal sampling algorithm:
1. Preconstraints
  - Processes typechecked type constraints into `Preconstraints`. (viz.
    `fromProps`)
    - Project type constraints into `PProp`s, which is the domain of type
      constraints that are handled.
    - Normalize the `PProp`s by simplifying arithmetic terms and eliminating
      modulus (by generating additional `PProp`s).
    - Remember and assign each `TParam` to an `Int`.
2. Constraints
  - Convert `PExp`s to `Exp`s which are standardized to know about the number of
    `TParam`s available. (viz. `extractExp`)
  - Extract a linear system of equations over `Rational` and a set of typeclass
    constraints (e.g. `fin`) from `PProp`s. (viz. `extractSysTcs`)
  - Use gaussian elimination to solve the system into a partition of dependent
    and independent variables, where the dependent variables are not mutually
    dependent. (viz. `solveGauss`)
  - Package up the result into a `Constraints`.
3. Solvedconstraints
  - Re-encode the gaussian-solved system of linear equations as a `SolvedSystem
    Rational = Vector (Maybe (Exp Rational))`. (viz. `toSolvedconstraints`)
  - Eliminate the denomenators of rational coefficients, by introducing new
    equations where needed (preserving non-mutual dependency), yielding a
    `SolvedSystem Nat'`. (viz. `elimDens`)
4. Sampling
  - Collect upper bounds on each variable.
  - Statefully sample each variable in order, which can spawn other samplings,
    which ensured to be performed in a valid acyclic order due to the
    preservation of non-mutual dependency among dependent variables.
-}


type Sample = [(TParam, Nat')]

sample ::
  [TParam] ->
  [Prop] ->
  Int ->
  SamplingM [Sample]
sample tparams props nLiteralSamples = do
  precons <- fromProps tparams props
  debug' 0 $ "precons = " ++ show precons
  cons <- toConstraints precons
  debug' 0 $ "cons <- toConstraints precons"
  debug' 0 $ "cons = " ++ show cons
  -- solve constraints system
  solcons <- do
    -- gaussian elimination
    cons <- overSystem (solveGauss (Cons.nVars cons)) cons
    debug' 0 $ "cons <- overSystem solveGauss cons"
    debug' 0 $ "cons = " ++ show cons
    -- verify gaussian-eliminated form
    solcons <- toSolvedConstraints cons
    debug' 0 $ "solcons <- toSolvedConstraints cons"
    debug' 0 $ "solcons = " ++ show solcons
    -- eliminate denomenators
    solcons <- elimDens solcons
    debug' 0 $ "solcons <- elimDens solcons"
    debug' 0 $ "solcons = " ++ show solcons
    --
    pure solcons
  --
  -- sample `nLiteralSamples` number of times
  replicateM nLiteralSamples do
    vals <- V.toList <$> Sampling.sample solcons
    pure (tparams `zip` vals)

applySample :: Sample -> Schema -> Schema
applySample sample Forall {sVars, sProps, sType} =
  Forall
    { -- only keep vars that are not substituted by sample
      sVars = filter (not . (`elem` (fst <$> sample))) sVars,
      sProps = apSubst subst sProps,
      sType = apSubst subst sType
    }
  where
    subst = listSubst $ bimap TVBound tNat' <$> sample
