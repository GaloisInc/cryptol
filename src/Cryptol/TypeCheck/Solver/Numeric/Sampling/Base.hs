{-# OPTIONS_GHC -Wno-name-shadowing #-}
module Cryptol.TypeCheck.Solver.Numeric.Sampling.Base where

import Control.Monad.Except
import Control.Monad.State (StateT, MonadState (get, put))
import Cryptol.TypeCheck.Solver.InfNat (Nat')
import System.Random.TF.Gen (RandomGen)
import Cryptol.Testing.Random (Gen)

-- | SamplingM
-- • `ExceptT SamplingError` thows errors during sampling
-- • `ExceptT ()` excepts when can't sample
type SamplingM m = ExceptT SamplingError (ExceptT () m)

data SamplingError = SamplingError String String
  deriving (Show) -- TODO

-- TODO
-- runsamplingM :: Monad m => SamplingM m a -> m (Either SamplingError (Maybe a))
-- -- runsamplingM m = either (const Nothing) Just <$> runExcept (runExceptT m)
-- runsamplingM m = _ <$> runExceptT (runExceptT m)

throwSamplingError :: Monad m => SamplingError -> SamplingM m a
throwSamplingError = throwError

noSampling :: Monad m => SamplingM m a
noSampling =
  -- throwError . SamplingError "sampling" $
  --   "no sampling"
  lift . throwError $ ()

-- | GenM
type GenM g = StateT g (Except SamplingError)

toGenM :: (g -> (a, g)) -> GenM g a
toGenM m = do
  g <- get
  (a, g) <- pure (m g)
  put g
  pure a

genWeightedFromList :: RandomGen g => [(Int, Nat')] -> GenM g Nat'
genWeightedFromList = undefined

_NAT'_MAX :: Nat'
_NAT'_MAX = 128

-- Generate a random `Nat'` that is less than or equal to the given bound,
-- chosen uniformly at random. If the bound is `Inf`, then `Inf` is chosen with
-- TBD weight, or else a value bounded by `_NAT'_MAX` is chosen.
genLeq :: RandomGen g => Nat' -> GenM g Nat'
genLeq = undefined

-- Generate a randon Nat' that is less than or equal to the given bound, where
-- each choice `x` is given weight `1/x`.
genLeqWBI :: RandomGen g => Nat' -> GenM g Nat'
genLeqWBI = undefined