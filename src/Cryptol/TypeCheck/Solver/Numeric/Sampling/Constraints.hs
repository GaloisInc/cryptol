{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Cryptol.TypeCheck.Solver.Numeric.Sampling.Constraints where

import Cryptol.TypeCheck.Solver.Numeric.Sampling.Base
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Exp
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Preconstraints
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Q
import Cryptol.TypeCheck.Type (TParam)
import Data.Vector (Vector)

-- | Constraints
data Constraints a = Constraints
  { sys :: Either (System a) (SolvedSystem a),
    tcs :: [Tc a],
    tparams :: Vector TParam -- Var => TParam
  }

deriving instance Show a => Show (Constraints a)

overSystem ::
  Monad m =>
  (System a -> SamplingM m (System a)) ->
  (Constraints a -> SamplingM m (Constraints a))
overSystem k cons = do
  sys <-
    k =<< case sys cons of
      Left sys -> pure sys
      Right _ ->
        throwSamplingError $
          SamplingError
            "overSystem"
            "Expected the system to be unsolved, but it's solved."
  pure cons {sys = Left sys}

overSolvedSystem ::
  Monad m =>
  (SolvedSystem a -> SamplingM m (SolvedSystem a)) ->
  (Constraints a -> SamplingM m (Constraints a))
overSolvedSystem k cons = do
  solsys <-
    k =<< case sys cons of
      Left _ ->
        throwSamplingError $
          SamplingError
            "overSolvedSystem"
            "Expected the system to be solved, but it's unsolved."
      Right solsys -> pure solsys
  pure cons {sys = Right solsys}

solveSystemVia ::
  Monad m =>
  (System a -> SamplingM m (SolvedSystem a)) ->
  (Constraints a -> SamplingM m (Constraints a))
solveSystemVia k cons = do
  solsys <-
    k =<< case sys cons of
      Left sys -> pure sys
      Right _ ->
        throwSamplingError $
          SamplingError
            "solveSystemVia"
            "Expected the system to be unsolved, but it's solved."
  pure cons {sys = Right solsys}

-- | Tc (Type Class constraint)
data Tc a = Tc TcName (Exp a)
  deriving (Show, Functor)

overTcExp :: Monad m => (Exp a -> m (Exp b)) -> (Tc a -> m (Tc b))
overTcExp k (Tc tcName e) = Tc tcName <$> k e

expFromTc :: Tc a -> Maybe (Exp a)
expFromTc (Tc _ e) = Just e

-- | System
-- A system of linear equations over domain `a`
-- The expression `a1*x1 + ... + aN*xN + c` encodes the equation
-- `a1*x1 + ... + aN*aN = c`.
type System a = [Exp a]

-- | SolvedSystem If equ `i` is `Nothing`, then var `i` is free. If equ `i` is
-- `Just e`, then var `i` is bound to expression `e`. A `SolvedSystem`
-- corresponds to an `n` by `n + 1` matrix, or `n` equations of the form:
-- ```
--   x0 = ...
--   x1 = ...
--   ...
--   x{n} = ...
-- ```
-- where the RHS expression for equation `i` must have `0*xi`. Since each
-- equation corresponds to a var, a SolvedSystem is indexed by `Var`.
type SolvedSystem a = Vector (Maybe (Exp a))

data TcName = FinTc | PrimTc
  deriving (Show)

countVars :: Constraints a -> Int
countVars = undefined

-- | fromPreconstraints
-- Preserves order of the `[TParam]` in `Preconstraints`.
fromPreconstraints :: Monad m => Preconstraints -> SamplingM m (Constraints Q)
fromPreconstraints = undefined
