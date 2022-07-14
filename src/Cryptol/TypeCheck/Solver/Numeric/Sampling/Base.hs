module Cryptol.TypeCheck.Solver.Numeric.Sampling.Base where

import Control.Monad.Except
import Control.Monad.State (StateT)
import Cryptol.TypeCheck.Solver.InfNat (Nat')
import System.Random.TF.Gen (RandomGen)

-- | SamplingM

type SamplingM = ExceptT () (Except SamplingError)

data SamplingError = SamplingError String String
  deriving (Show) -- TODO

runsamplingM :: SamplingM a -> Either SamplingError (Maybe a)
runsamplingM m = either (const Nothing) Just <$> runExcept (runExceptT m)

throwSamplingError :: SamplingError -> SamplingM a
throwSamplingError = lift . throwError

noSampling :: SamplingM a
noSampling = throwError ()


-- | GenM

type GenM g = StateT g (Except SamplingError)

-- -- TODO: use System.Random.TF.Gen.next to convert a Word32 into a Nat' less than the input somehow
-- genBounded :: RandomGen g => Nat' -> Int -> GenM g Nat'
-- genBounded = undefined

genWeightedFromList :: RandomGen g => [(Int, Nat')] -> GenM g Nat'
genWeightedFromList = undefined