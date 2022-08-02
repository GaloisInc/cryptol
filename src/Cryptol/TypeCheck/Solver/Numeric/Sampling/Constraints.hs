{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Cryptol.TypeCheck.Solver.Numeric.Sampling.Constraints where

import Control.Monad.State (StateT (runStateT), MonadTrans (lift))
import Control.Monad.Writer (MonadWriter (tell), WriterT (WriterT, runWriterT), execWriterT)
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Base
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Exp
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Preconstraints (Preconstraints, SamplingParam)
import qualified Cryptol.TypeCheck.Solver.Numeric.Sampling.Preconstraints as PC
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Q
import Cryptol.TypeCheck.Type (TParam)
import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.Maybe (fromMaybe)

-- | Constraints
--
-- Encodes the following:
-- - `sys`: a system of equations
-- - `tcs`: a list of non-arithmetic typeclass constraints
-- - `params`: a vectro of sampling parameters, both given by the user and
--    generated during sampling
data Constraints a = Constraints
  { sys :: System a,
    tcs :: [Tc a],
    params :: Vector SamplingParam
  }

deriving instance Show a => Show (Constraints a)

overSystem ::
  Monad m =>
  (System a -> SamplingM m (System a)) ->
  (Constraints a -> SamplingM m (Constraints a))
overSystem k cons = do
  sys <- k (sys cons)
  pure cons {sys = sys}

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

data TcName = FinTc | PrimTc
  deriving (Show)

countVars :: Constraints a -> Int
countVars cons = V.length (params cons)

-- | toConstraints
--
-- Preserves order of the `[SamplingParam]` in `Preconstraints`.
toConstraints :: forall m. Monad m => Preconstraints -> SamplingM m (Constraints Q)
toConstraints precons = do
  -- extract sys and tcs from preprops
  (sys, tcs) <- extractSysTcs (PC.preprops precons)
  --
  pure
    Constraints
      { sys = sys,
        tcs = tcs,
        params = PC.params precons
      }
  where
    extractSysTcs :: [PC.PProp] -> SamplingM m (System Q, [Tc Q])
    extractSysTcs pprops = do
      runWriterT . execWriterT . (`traverse` pprops) $ go
      where
        nParams = PC.countVars precons

        go :: PC.PProp -> WriterT (System Q) (WriterT [Tc Q] (SamplingM m)) ()
        go = \case
          PC.PPEqual pe1 pe2 -> do
            e1 <- lift . lift $ extractExp pe1
            e2 <- lift . lift $extractExp pe2
            tellExp [e1 - e2]
          PC.PPFin pe -> do
            e <- lift . lift $ extractExp pe
            tellTc [Tc FinTc e]
          -- not supported, or should have been filtered out in Preconstraints
          _ -> undefined 

        tellExp = tell
        tellTc = lift . tell

        -- extractExp :: PC.PExp -> WriterT (System Q) (WriterT [Tc Q] (SamplingM m)) (Exp Q)
        extractExp :: PC.PExp -> SamplingM m (Exp Q)
        extractExp = \case
          PC.PEConst q -> pure $ fromConstant nParams q
          PC.PETerm q i -> do
            pure $ single nParams q i
          PC.PEOp2 PC.PAdd pe1 pe2 -> do
            pe1 <- extractExp pe1
            pe2 <- extractExp pe2
            pure $ pe1 + pe2
          _ -> undefined -- not in normal form

-- \ do
-- -- -- $ go `traverse` pprops
-- --   where
-- --     go :: PC.PProp -> WriterT (System Q) (WriterT [Tc Q] (SamplingM m)) ()
-- --     go = _
--   _
