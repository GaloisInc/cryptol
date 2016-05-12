module Cryptol.Utils.Color (
    colorizeString, OutputColor(..)
  , errorMsg, errorAtMsg
  , warningMsg, warningAtMsg
  ) where

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

errorMsg :: String
errorMsg = colorizeString Failed "[error]"

errorAtMsg :: String
errorAtMsg = errorMsg ++ " at"

warningMsg :: String
warningMsg = colorizeString Failed "[warning]"

warningAtMsg :: String
warningAtMsg = warningMsg ++ " at"
