{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}

module Cryptol.TypeCheck.Solver.Numeric.Sampling.Constraints where

import Cryptol.TypeCheck.Solver.Numeric.Sampling.Exp
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Q
import Cryptol.TypeCheck.Solver.Numeric.Sampling.System
import Cryptol.TypeCheck.Solver.Numeric.Sampling.SolvedSystem
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Base
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Preconstraints
import Data.Vector (Vector)
import Cryptol.TypeCheck.Type (TParam)

-- | Constraints

data Constraints a = Constraints 
  { sys :: Either (System a) (SolvedSystem a)
  , tcs :: [Tc a]
  , tparams :: Vector TParam -- Var => TParam
  }

deriving instance Show a => Show (Constraints a)
data Tc a = Tc TcName (Exp a)
  deriving (Show, Functor)

data TcName = FinTc | PrimTc
  deriving (Show)

countVars :: Constraints a -> Int
countVars = undefined

-- | Translate Preconstraints -> Constraints

fromPreconstraints :: Monad m => Preconstraints -> SamplingM m (Constraints Q)
fromPreconstraints = undefined
