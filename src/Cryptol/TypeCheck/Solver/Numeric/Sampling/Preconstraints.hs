{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}

module Cryptol.TypeCheck.Solver.Numeric.Sampling.Preconstraints where

import Cryptol.TypeCheck.Type (TParam, Prop)
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Exp
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Q
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Base
import GHC.TypeNats

-- | Preconstraints

data Preconstraints

-- | fromProps
-- Preserves order of `[TParam]`.
fromProps :: Monad m => [TParam] -> [Prop] -> SamplingM m Preconstraints
fromProps tparams props = undefined