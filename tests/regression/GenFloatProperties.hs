{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}
-- | Generate a Cryptol script that proves, checks, or disproves various
-- Cryptol properties about floating-point operations.
--
-- Note that all of these properties are parameterized over arbitrary exponents
-- and precisions, and many of the properties are also parameterized over
-- arbitrary rounding modes, so this will generate code which instantiates each
-- property at a particular float size and at all supported rounding modes.
module Main (main) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T

data ResultType
  = ProveProperty
    -- ^ Something which should hold for all inputs, and an SMT solver is able
    -- to prove it.
  | CheckProperty
    -- ^ Something which should hold for all inputs, but most SMT solvers
    -- cannot prove it (at least, not without taking an extraordinarily long
    -- time). We resort to spot-checking these properties on specific inputs.
  | Counterexample
    -- ^ Something which does not hold for at least one input.

data Result = Result
  { resultName :: !Text
  , resultType :: !ResultType
  , resultHasRoundingMode :: !Bool
  }

propertiesFile :: FilePath
propertiesFile = "FloatPropertiesGeneric.cry"

icryFile :: FilePath
icryFile = "float_properties.icry"

scriptFile :: FilePath
scriptFile = "GenFloatProperties.hs"

scrapeResults :: IO [Result]
scrapeResults = do
  ls0 <- T.lines <$> T.readFile propertiesFile
  let ls1 = zip ls0 (drop 1 (cycle ls0))
  let ls2 =
        filter
          (\(l, _) ->
            any (`T.isPrefixOf` l) ["prop_", "check_", "counterexample_"] &&
            (" :" `T.isInfixOf` l))
          ls1
  pure $
    map
      (\(l1, l2) ->
        let name = head (T.splitOn " " l1) in
        Result
          { resultName =
              name
          , resultType =
              if "prop_" `T.isPrefixOf` l1 then ProveProperty
              else if "check_" `T.isPrefixOf` l1 then CheckProperty
              else if "counterexample_" `T.isPrefixOf` l1 then Counterexample
              else error $ "Unsupported result name: " ++ T.unpack name
          , resultHasRoundingMode =
              any ("RoundingMode" `T.isInfixOf`) [l1, l2]
          })
      ls2

resultCommandLines :: Result -> [Text]
resultCommandLines r =
  [ "\"" <> action <> " " <> resultName r <> "...\""
  | let action = case resultType r of
                   ProveProperty -> "Proving"
                   CheckProperty -> "Checking"
                   Counterexample -> "Disproving"
  ] ++
  if resultHasRoundingMode r
    then [basicCommand <> " " <> rm | rm <- roundingModes]
    else [basicCommand]
  where
    -- We arbitrarily instantiate each property at Float32 (`{8, 24}), but
    -- these properties should hold for any Float size.
    basicCommand :: Text
    basicCommand = command <> " " <> resultName r <> "`{8, 24}"
      where
        command = case resultType r of
                    ProveProperty -> ":prove"
                    CheckProperty -> ":check"
                    Counterexample -> ":sat"

    roundingModes :: [Text]
    roundingModes = ["rne", "rna", "rtp", "rtn", "rtz"]

main :: IO ()
main = do
  results <- scrapeResults
  T.putStrLn $ T.unlines $
    [ "// THIS IS AUTO-GENERATED"
    , "//"
    , "// Rather than modifying this file, please modify the script which"
    , "// generated it (" <> T.pack scriptFile <> ") and regenerate it using:"
    , "//"
    , "//   runghc " <> T.pack scriptFile <> " > " <> T.pack icryFile
    , ""
    , ":load " <> T.pack propertiesFile
    , ":set prover=w4-bitwuzla" -- A reasonably fast solver for floating-point-related properties
    , ":set ascii=on"
    , ":set show-examples=no"
    ] ++
    concatMap resultCommandLines results
