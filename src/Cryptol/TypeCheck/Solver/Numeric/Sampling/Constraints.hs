{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Cryptol.TypeCheck.Solver.Numeric.Sampling.Constraints where

import Control.Monad.Except (MonadError (throwError))
import Control.Monad.State (MonadTrans (lift), StateT (runStateT))
import Control.Monad.Writer (MonadWriter (tell), WriterT (WriterT, runWriterT), execWriterT)
import Cryptol.TypeCheck.PP (pp, ppList)
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Base
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Exp
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Preconstraints (Preconstraints)
import qualified Cryptol.TypeCheck.Solver.Numeric.Sampling.Preconstraints as PC
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Q
import Cryptol.TypeCheck.Type (TParam)
import qualified Data.List as L
import Data.Maybe (fromMaybe)
import Data.Vector (Vector)
import qualified Data.Vector as V

-- | Constraints
--
-- Encodes the following:
-- - `sys`: a system of equations
-- - `tcs`: a list of non-arithmetic typeclass constraints
-- - `tparams`: a vector of the numeric type parameters from a signature
data Constraints a = Constraints
  { sys :: System a,
    tcs :: [Tc a],
    tparams :: Vector TParam,
    nVars :: Int
  }

instance Show a => Show (Constraints a) where
  show Constraints {..} =
    unlines
      [ "Constraints:",
        "  sys:\n" ++ unlines (fmap (("    " ++) . show) sys),
        "  tcs     = " ++ show tcs,
        "  tparams = " ++ show (ppList (V.toList (pp <$> tparams))),
        "  nVars   = " ++ show nVars
      ]

overSystem ::
  (System a -> SamplingM (System a)) ->
  (Constraints a -> SamplingM (Constraints a))
overSystem k cons = do
  sys <- k (sys cons)
  pure cons {sys = sys}

-- | Tc (Type Class constraint)
data Tc a = Tc TcName (Exp a)
  deriving (Show, Functor)

overTcExp :: (Exp a -> Exp b) -> (Tc a -> Tc b)
overTcExp k (Tc tcName e) = Tc tcName (k e)

overTcExpM :: Monad m => (Exp a -> m (Exp b)) -> (Tc a -> m (Tc b))
overTcExpM k (Tc tcName e) = Tc tcName <$> k e

expFromTc :: Tc a -> Maybe (Exp a)
expFromTc (Tc _ e) = Just e

-- | System
-- A system of linear equations over domain `a`
-- The expression `a1*x1 + ... + aN*xN + c` encodes the equation
-- `a1*x1 + ... + aN*aN = c`.
-- type System a = [Exp a]
type System a = [Equ a]

-- encodes equality with var terms on the LHS and constant term on the RHS
newtype Equ a = Equ (Exp a)
  deriving (Functor)

instance Show a => Show (Equ a) where
  show (Equ (Exp as c)) =
    unwords
      [ L.intercalate " + " . V.toList $
          ( (\(i, a) -> show a ++ "*" ++ "x{" ++ show i ++ "}")
              <$> V.zip (V.generate (V.length as) id) as
          ),
        "=",
        show c
      ]

-- a*x + b*y = n  ~~>  a*x + b*y - n = 0
fromEqu :: Num a => Equ a -> Exp a
fromEqu (Equ (Exp as c)) = Exp as (-c)

-- a*x + b*y + n = 0  ~~>  a*x + b*y = -n
toEqu :: Num a => Exp a -> Equ a
toEqu (Exp as c) = Equ $ Exp as (-c)

asExp :: (Exp a -> b) -> Equ a -> b
asExp f (Equ e) = f e

overExp :: (Exp a -> Exp b) -> (Equ a -> Equ b)
overExp f (Equ e) = Equ (f e)

data TcName = FinTc | PrimeTc
  deriving (Show)

-- | toConstraints
--
-- Preserves order of the `[SamplingParam]` in `Preconstraints`.
toConstraints :: Preconstraints -> SamplingM (Constraints Q)
toConstraints precons = do
  -- extract sys and tcs from preprops
  (sys, tcs) <- extractSysTcs (PC.preprops precons)
  -- pad all exps to the number of params
  --
  pure
    Constraints
      { sys = sys,
        tcs = tcs,
        tparams = PC.tparams precons,
        nVars = PC.nVars precons
      }
  where
    extractSysTcs :: [PC.PProp] -> SamplingM (System Q, [Tc Q])
    extractSysTcs pprops = do
      runWriterT . execWriterT . (`traverse` pprops) $ go
      where
        nParams = PC.nVars precons

        go :: PC.PProp -> WriterT (System Q) (WriterT [Tc Q] SamplingM) ()
        go = \case
          PC.PPEqual pe1 pe2 -> do
            -- resulting expression of the form `Exp [x,y,z] q` represents
            -- equality `a*x + b*y + c*z = q`
            e1 <- lift . lift $ extractExp pe1
            e2 <- lift . lift $ extractExp pe2
            tellEqu [toEqu $ e1 - e2]
          PC.PPFin pe -> do
            e <- lift . lift $ extractExp pe
            tellTc [Tc FinTc e]
          -- not supported, or should have been filtered out in Preconstraints
          pprop ->
            throwError $
              SamplingError "toConstraints.extractSysTcs" $
                "This PProp is not supported by literal literal sampling: "
                  ++ "`"
                  ++ show pprop
                  ++ "`"

        tellEqu = tell
        tellTc = lift . tell

        -- extractExp :: PC.PExp -> WriterT (System Q) (WriterT [Tc Q] (SamplingM)) (Exp Q)
        extractExp :: PC.PExp -> SamplingM (Exp Q)
        extractExp = \case
          PC.PEConst q -> pure $ fromConstant nParams q
          PC.PETerm q i -> do
            pure $ single nParams q i
          PC.PEOp2 PC.PAdd pe1 pe2 -> do
            pe1 <- extractExp pe1
            pe2 <- extractExp pe2
            pure $ pe1 + pe2
          _ -> undefined -- not in normal form
