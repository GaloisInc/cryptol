{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}

module Cryptol.TypeCheck.Solver.Numeric.Sampling.Preconstraints where

import Data.Finite
import Cryptol.TypeCheck.Type (TParam, Prop)

import Cryptol.TypeCheck.Solver.Numeric.Sampling.Exp
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Q
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Base
import GHC.TypeNats

-- | Preconstraints

data Preconstraints (n :: Nat)

data SomePreconstraints = forall n. KnownNat n => SomePreconstraints (Preconstraints n)

-- | [TParam] -> [Prop] -> Preconstraints

fromProps :: Monad m => [TParam] -> [Prop] -> samplingM m SomePreconstraints
fromProps tparams props = undefined