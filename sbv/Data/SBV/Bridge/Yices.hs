---------------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Bridge.Yices
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Interface to the Yices SMT solver. Import this module if you want to use the
-- Yices SMT prover as your backend solver. Also see:
--
--       - "Data.SBV.Bridge.Boolector"
--
--       - "Data.SBV.Bridge.CVC4"
--
--       - "Data.SBV.Bridge.Z3"
--
--       - "Data.SBV.Bridge.MathSAT"
---------------------------------------------------------------------------------

module Data.SBV.Bridge.Yices (
  -- * Yices specific interface
  sbvCurrentSolver
  -- ** Proving, checking satisfiability, and safety
  , prove, sat, safe, allSat, isVacuous, isTheorem, isSatisfiable
  -- ** Optimization routines
  , optimize, minimize, maximize
  -- * Non-Yices specific SBV interface
  -- $moduleExportIntro
  , module Data.SBV
  ) where

import Data.SBV hiding (prove, sat, safe, allSat, isVacuous, isTheorem, isSatisfiable, optimize, minimize, maximize, sbvCurrentSolver)

-- | Current solver instance, pointing to yices.
sbvCurrentSolver :: SMTConfig
sbvCurrentSolver = yices

-- | Prove theorems, using the Yices SMT solver
prove :: Provable a
      => a              -- ^ Property to check
      -> IO ThmResult   -- ^ Response from the SMT solver, containing the counter-example if found
prove = proveWith sbvCurrentSolver

-- | Find satisfying solutions, using the Yices SMT solver
sat :: Provable a
    => a                -- ^ Property to check
    -> IO SatResult     -- ^ Response of the SMT Solver, containing the model if found
sat = satWith sbvCurrentSolver

-- | Check safety, i.e., prove that all 'sAssert' conditions are statically true in all paths
safe :: SExecutable a
     => a               -- ^ Program to check the safety of
     -> IO SafeResult   -- ^ Response of the SMT solver, containing the unsafe model if found
safe = safeWith sbvCurrentSolver

-- | Find all satisfying solutions, using the Yices SMT solver
allSat :: Provable a
       => a                -- ^ Property to check
       -> IO AllSatResult  -- ^ List of all satisfying models
allSat = allSatWith sbvCurrentSolver

-- | Check vacuity of the explicit constraints introduced by calls to the 'constrain' function, using the Yices SMT solver
isVacuous :: Provable a
          => a             -- ^ Property to check
          -> IO Bool       -- ^ True if the constraints are unsatisifiable
isVacuous = isVacuousWith sbvCurrentSolver

-- | Check if the statement is a theorem, with an optional time-out in seconds, using the Yices SMT solver
isTheorem :: Provable a
          => Maybe Int          -- ^ Optional time-out, specify in seconds
          -> a                  -- ^ Property to check
          -> IO (Maybe Bool)    -- ^ Returns Nothing if time-out expires
isTheorem = isTheoremWith sbvCurrentSolver

-- | Check if the statement is satisfiable, with an optional time-out in seconds, using the Yices SMT solver
isSatisfiable :: Provable a
              => Maybe Int       -- ^ Optional time-out, specify in seconds
              -> a               -- ^ Property to check
              -> IO (Maybe Bool) -- ^ Returns Nothing if time-out expiers
isSatisfiable = isSatisfiableWith sbvCurrentSolver

-- | Optimize cost functions, using the Yices SMT solver
optimize :: (SatModel a, SymWord a, Show a, SymWord c, Show c)
         => OptimizeOpts                -- ^ Parameters to optimization (Iterative, Quantified, etc.)
         -> (SBV c -> SBV c -> SBool)   -- ^ Betterness check: This is the comparison predicate for optimization
         -> ([SBV a] -> SBV c)          -- ^ Cost function
         -> Int                         -- ^ Number of inputs
         -> ([SBV a] -> SBool)          -- ^ Validity function
         -> IO (Maybe [a])              -- ^ Returns Nothing if there is no valid solution, otherwise an optimal solution
optimize = optimizeWith sbvCurrentSolver

-- | Minimize cost functions, using the Yices SMT solver
minimize :: (SatModel a, SymWord a, Show a, SymWord c, Show c)
         => OptimizeOpts                -- ^ Parameters to optimization (Iterative, Quantified, etc.)
         -> ([SBV a] -> SBV c)          -- ^ Cost function to minimize
         -> Int                         -- ^ Number of inputs
         -> ([SBV a] -> SBool)          -- ^ Validity function
         -> IO (Maybe [a])              -- ^ Returns Nothing if there is no valid solution, otherwise an optimal solution
minimize = minimizeWith sbvCurrentSolver

-- | Maximize cost functions, using the Yices SMT solver
maximize :: (SatModel a, SymWord a, Show a, SymWord c, Show c)
         => OptimizeOpts                -- ^ Parameters to optimization (Iterative, Quantified, etc.)
         -> ([SBV a] -> SBV c)          -- ^ Cost function to maximize
         -> Int                         -- ^ Number of inputs
         -> ([SBV a] -> SBool)          -- ^ Validity function
         -> IO (Maybe [a])              -- ^ Returns Nothing if there is no valid solution, otherwise an optimal solution
maximize = maximizeWith sbvCurrentSolver

{- $moduleExportIntro
The remainder of the SBV library that is common to all back-end SMT solvers, directly coming from the "Data.SBV" module.
-}
