-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Tools.ExpectedValue
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Computing the expected value of a symbolic variable
-----------------------------------------------------------------------------

{-# LANGUAGE PatternGuards #-}
module Data.SBV.Tools.ExpectedValue (expectedValue, expectedValueWith) where

import Control.DeepSeq (rnf)
import System.Random   (newStdGen, StdGen)
import Numeric

import Data.SBV.BitVectors.Data

-- | Generalized version of 'expectedValue', allowing the user to specify the
-- warm-up count and the convergence factor. Maximum iteration count can also
-- be specified, at which point convergence won't be sought. The boolean controls verbosity.
expectedValueWith :: Outputtable a => Bool -> Int -> Maybe Int -> Double -> Symbolic a -> IO [Double]
expectedValueWith chatty warmupCount mbMaxIter epsilon m
  | warmupCount < 0 || epsilon < 0
  = error $ "SBV.expectedValue: warmup count and epsilon both must be non-negative, received: " ++ show (warmupCount, epsilon)
  | True
  = warmup warmupCount (repeat 0) >>= go warmupCount
  where progress s | not chatty = return ()
                   | True       = putStr $ "\r*** " ++ s
        warmup :: Int -> [Integer] -> IO [Integer]
        warmup 0 v = do progress $ "Warmup complete, performed " ++ show warmupCount ++ " rounds.\n"
                        return v
        warmup n v = do progress $ "Performing warmup, round: " ++ show (warmupCount - n)
                        g <- newStdGen
                        t <- runOnce g
                        let v' = zipWith (+) v t
                        rnf v' `seq` warmup (n-1) v'
        runOnce :: StdGen -> IO [Integer]
        runOnce g = do (_, Result _ _ _ _ cs _ _ _ _ _ cstrs os) <- runSymbolic' (Concrete g) (m >>= output)
                       let cval o = case o `lookup` cs of
                                      Nothing -> error "SBV.expectedValue: Cannot compute expected-values in the presence of uninterpreted constants!"
                                      Just cw -> case (cwKind cw, cwVal cw) of
                                                   (KBool, _)                -> if cwToBool cw then 1 else 0
                                                   (KBounded{}, CWInteger v) -> v
                                                   (KUnbounded, CWInteger v) -> v
                                                   (KReal, _)                -> error "Cannot compute expected-values for real valued results."
                                                   _                         -> error $ "SBV.expectedValueWith: Unexpected CW: " ++ show cw
                       if all ((== 1) . cval) cstrs
                          then return $ map cval os
                          else runOnce g -- constraint not satisfied try again with the same set of constraints
        go :: Int -> [Integer] -> IO [Double]
        go cases curSums
         | Just n <- mbMaxIter, n < curRound
         = do progress "\n"
              progress "Maximum iteration count reached, stopping.\n"
              return curEVs
         | True
         = do g <- newStdGen
              t <- runOnce g
              let newSums  = zipWith (+) curSums t
                  newEVs = map ev' newSums
                  diffs  = zipWith (\x y -> abs (x - y)) newEVs curEVs
              if all (< epsilon) diffs
                 then do progress $ "Converges with epsilon " ++ show epsilon ++ " after " ++ show curRound ++ " rounds.\n"
                         return newEVs
                 else do progress $ "Tuning, round: " ++ show curRound ++ " (margin: " ++ showFFloat (Just 6) (maximum (0:diffs)) "" ++ ")"
                         go newCases newSums
         where curRound = cases - warmupCount
               newCases = cases + 1
               ev, ev' :: Integer -> Double
               ev  x  = fromIntegral x / fromIntegral cases
               ev' x  = fromIntegral x / fromIntegral newCases
               curEVs = map ev curSums

-- | Given a symbolic computation that produces a value, compute the
-- expected value that value would take if this computation is run
-- with its free variables drawn from uniform distributions of its
-- respective values, satisfying the given constraints specified by
-- 'constrain' and 'pConstrain' calls. This is equivalent to calling
-- 'expectedValueWith' the following parameters: verbose, warm-up
-- round count of @10000@, no maximum iteration count, and with
-- convergence margin @0.0001@.
expectedValue :: Outputtable a => Symbolic a -> IO [Double]
expectedValue = expectedValueWith True 10000 Nothing 0.0001
