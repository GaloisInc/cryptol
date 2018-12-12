module Main(main) where

import System.FilePath(takeExtension)
import TestLib(mainWith,Config(..))

main :: IO ()
main = mainWith Config { cfgDefaultBinary = "cryptol"
                       , cfgBinOpts       = \f -> ["-b",f]
                       , cfgIsTestCase    = \f -> takeExtension f == ".icry"
                       }

