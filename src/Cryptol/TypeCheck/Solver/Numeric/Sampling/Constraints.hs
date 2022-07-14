{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}

module Cryptol.TypeCheck.Solver.Numeric.Sampling.Constraints where

import GHC.TypeNats

import Cryptol.TypeCheck.Solver.Numeric.Sampling.Exp
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Q
import Cryptol.TypeCheck.Solver.Numeric.Sampling.System
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Base
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Preconstraints

-- | Constraints

data Constraints n a = Constraints 
  { sys :: System n a
  , tcs :: [Tc n a]
  }
  deriving (Show, Functor)

data SomeConstraints a = forall n. KnownNat n => SomeConstraints (Constraints n a)

deriving instance Show a => Show (SomeConstraints a)
deriving instance Functor SomeConstraints

data Tc n a = Tc TcName (Exp n a)
  deriving (Show, Functor)

data TcName = FinTc | PrimTc
  deriving (Show)

-- | Translate Preconstraints -> Constraints

fromPreconstraints :: Monad m => SomePreconstraints -> samplingM m (SomeConstraints Q)
fromPreconstraints = undefined
