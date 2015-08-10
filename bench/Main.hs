-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
module Main where

import qualified Data.Text.Lazy     as T
import qualified Data.Text.Lazy.IO  as T

import qualified Cryptol.Parser     as P
import qualified Cryptol.Parser.AST as P

import Criterion.Main

main :: IO ()
main = defaultMain [
    bgroup "parser" [
        parser "Prelude" "lib/Cryptol.cry"
      ]
  ]

-- | Make a benchmark for parsing a Cryptol module
parser :: String -> FilePath -> Benchmark
parser name path =
  env (T.readFile path) $ \(~bytes) ->
    bench name $ whnfIO $ do
      let cfg = P.defaultConfig
                { P.cfgSource  = path
                , P.cfgPreProc = P.guessPreProc path
                }
      case P.parseModule cfg bytes of
        Right pm -> return pm
        Left err -> error (show err)
