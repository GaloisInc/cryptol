-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Utils.TDiff
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Runs an IO computation printing the time it took to run it
-----------------------------------------------------------------------------

module Data.SBV.Utils.TDiff(timeIf) where

import Control.DeepSeq (rnf, NFData(..))
import System.Time     (TimeDiff(..), normalizeTimeDiff, diffClockTimes, getClockTime)
import Numeric         (showFFloat)

showTDiff :: TimeDiff -> String
showTDiff itd = et
  where td = normalizeTimeDiff itd
        vals = dropWhile (\(v, _) -> v == 0) (zip [tdYear td, tdMonth td, tdDay td, tdHour td, tdMin td] "YMDhm")
        sec = ' ' : show (tdSec td) ++ dropWhile (/= '.') pico
        pico = showFFloat (Just 3) (((10**(-12))::Double) * fromIntegral (tdPicosec td)) "s"
        et = concatMap (\(v, c) -> ' ':show v ++ [c]) vals ++ sec

-- | If selected, runs the computation @m@, and prints the time it took
-- to run it. The return type should be an instance of 'NFData' to ensure
-- the correct elapsed time is printed.
timeIf :: NFData a => Bool -> String -> IO a -> IO a
timeIf False _ m = m
timeIf True  w m = do start <- getClockTime
                      r <- m
                      end <- rnf r `seq` getClockTime
                      let elapsed = diffClockTimes end start
                      putStrLn $ "** Elapsed " ++ w ++ " time:" ++ showTDiff elapsed
                      return r
