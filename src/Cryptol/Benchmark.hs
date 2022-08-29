module Cryptol.Benchmark
  ( BenchmarkStats (..)
  , benchmark
  , secs
  ) where

import           Criterion.Measurement       (runBenchmark, secs, threshold)
import           Criterion.Measurement.Types
import           Data.Int
import qualified Data.Vector                 as V
import qualified Data.Vector.Unboxed         as U

data BenchmarkStats = BenchmarkStats
  { benchAvgTime    :: !Double
  , benchAvgCpuTime :: !Double
  , benchAvgCycles  :: !Int64
  } deriving Show

benchmark :: Double -> (a -> IO b) -> a -> IO BenchmarkStats
benchmark period f x = do
  (meas, _) <- runBenchmark (whnfAppIO f x) period
  let meas' = rescale <$> V.filter ((>= threshold) . measTime) meas
      len = length meas'
      sumMeasure sel = U.sum $ measure sel meas'
  pure BenchmarkStats
    { benchAvgTime = sumMeasure measTime / fromIntegral len
    , benchAvgCpuTime = sumMeasure measCpuTime / fromIntegral len
    , benchAvgCycles = sumMeasure measCycles `div` fromIntegral len }
