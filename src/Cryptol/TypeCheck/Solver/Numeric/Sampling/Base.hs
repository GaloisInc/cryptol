{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Cryptol.TypeCheck.Solver.Numeric.Sampling.Base where

import Control.Monad.Except
import Control.Monad.State (MonadState (get, put), State, StateT, evalStateT, gets, runState)
import Cryptol.Testing.Random (Gen)
import Cryptol.TypeCheck.Solver.InfNat (Nat')
import System.Random.TF (newTFGen)
import System.Random.TF.Gen (RandomGen, TFGen)

-- | SamplingM
type SamplingM = ExceptT SamplingError (StateT TFGen IO)

data SamplingError = SamplingError String String

instance Show SamplingError where 
  show (SamplingError title msg) = "[" ++ title ++ "] " ++ msg

runSamplingM :: SamplingM a -> IO (Either SamplingError a)
runSamplingM m = do
  g <- newTFGen
  flip evalStateT g . runExceptT $ m

debug :: String -> SamplingM ()
debug = liftIO . putStrLn

debugLevel :: Int
debugLevel = -1

debug' :: Int -> String -> SamplingM ()
debug' lvl
  | lvl <= debugLevel = debug
  | otherwise = const (pure ())

throwSamplingError :: SamplingError -> SamplingM a
throwSamplingError = throwError

nat'_max :: Nat'
nat'_max = 128

integer_max :: Integer
integer_max = 128

{-
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

-- Generate a random `Nat'` that is less than or equal to the given bound,
-- chosen uniformly at random. If the bound is `Inf`, then `Inf` is chosen with
-- TBD weight, or else a value bounded by `_NAT'_MAX` is chosen.
genLeq :: RandomGen g => Nat' -> GenM g Nat'
genLeq = undefined

-- Generate a randon Nat' that is less than or equal to the given bound, where
-- each choice `x` is given weight `1/x`.
genLeqWBI :: RandomGen g => Nat' -> GenM g Nat'
genLeqWBI = undefined -- TODO: also, use this in the correct place
-}
