{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE FlexibleInstances #-}
module Cryptol.TypeCheck.Solver.Numeric.Sampling.Base where

import Control.Monad.Except
import Control.Monad.State (StateT, MonadState (get, put), gets, State, runState)
import Cryptol.TypeCheck.Solver.InfNat (Nat')
import System.Random.TF.Gen (RandomGen)
import Cryptol.Testing.Random (Gen)

-- | SamplingM
type SamplingM m = ExceptT SamplingError m

data SamplingError = SamplingError String String
  deriving (Show) -- TODO

-- instance MonadFail m => MonadFail (ExceptT SamplingError m) where
--   fail = throwSamplingError . SamplingError "pattern fail"


-- TODO
runSamplingM :: Monad m => SamplingM m a -> m (Either SamplingError a)
runSamplingM = runExceptT
-- -- runSamplingM m = either (const Nothing) Just <$> runExcept (runExceptT m)

throwSamplingError :: Monad m => SamplingError -> SamplingM m a
throwSamplingError = throwError

-- | GenM
type GenM g = State g

runGenM :: g -> GenM g a -> (a, g)
runGenM = flip runState

toGenM :: (g -> (a, g)) -> GenM g a
toGenM m = do
  (a, g) <- gets m
  put g
  pure a

genWeightedFromList :: RandomGen g => [(Int, Nat')] -> GenM g Nat'
genWeightedFromList = undefined -- TODO: also, use this in the correct place

nat'_max :: Nat'
nat'_max = 128

integer_max :: Integer
integer_max = 128

-- Generate a random `Nat'` that is less than or equal to the given bound,
-- chosen uniformly at random. If the bound is `Inf`, then `Inf` is chosen with
-- TBD weight, or else a value bounded by `_NAT'_MAX` is chosen.
genLeq :: RandomGen g => Nat' -> GenM g Nat'
genLeq = undefined

-- Generate a randon Nat' that is less than or equal to the given bound, where
-- each choice `x` is given weight `1/x`.
genLeqWBI :: RandomGen g => Nat' -> GenM g Nat'
genLeqWBI = undefined -- TODO: also, use this in the correct place