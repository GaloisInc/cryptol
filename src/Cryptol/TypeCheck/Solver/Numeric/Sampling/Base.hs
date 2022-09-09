{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE LambdaCase #-}

module Cryptol.TypeCheck.Solver.Numeric.Sampling.Base where

import Control.Monad.Except (ExceptT, MonadError (throwError), runExceptT)
import Control.Monad.State (StateT, evalStateT)
import Control.Monad.Trans (liftIO)
import Data.Ratio (denominator, numerator)
import System.Random.TF (TFGen, newTFGen)

-- | SamplingM
type SamplingM = ExceptT SamplingError (StateT TFGen IO)

data SamplingError
  = InternalError String String
  | NoNumericTypeVariables
  | InvalidTypeConstraints String
  | NoSolution

instance Show SamplingError where
  show = \case
    InternalError title msg -> title ++ ": " ++ msg
    NoNumericTypeVariables -> "no numeric type variables"
    InvalidTypeConstraints msg -> "invalid type constraints: " ++ msg
    NoSolution -> "constraints have no solution"

runSamplingM :: SamplingM a -> IO (Either SamplingError a)
runSamplingM m = do
  g <- newTFGen
  flip evalStateT g . runExceptT $ m

debug :: String -> SamplingM ()
debug str = liftIO . putStrLn $ "[>>>] " ++ str

debugLevel :: Int
debugLevel = 2

debug' :: Int -> String -> SamplingM ()
debug' lvl
  | lvl <= debugLevel = liftIO . putStrLn
  | otherwise = const (pure ())

throwSamplingError :: SamplingError -> SamplingM a
throwSamplingError = throwError

fromRationalToInt :: Rational -> Maybe Int
fromRationalToInt q
  | denominator q == 1 = Just . fromIntegral . numerator $ q
  | otherwise = Nothing
