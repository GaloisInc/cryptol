module Cryptol.Utils.Color (colorizeString, OutputColor(..)) where

import System.Console.ANSI

data OutputColor = Failed | Passed | Prompt deriving (Enum, Eq)
colorizeString :: OutputColor -> String -> String
colorizeString color msg = prefix ++ msg ++ suffix where
    -- sgr | isBatch  = setSGRCode
    --     | otherwise = const ""
    sgr = setSGRCode
    prefix = case color of
                  Failed -> sgr [SetColor Foreground Vivid Red]
                  Passed -> sgr [SetColor Foreground Vivid Green]
                  Prompt -> sgr [SetColor Foreground Vivid Blue] ++ sgr [SetConsoleIntensity BoldIntensity]
    suffix = sgr [Reset]


