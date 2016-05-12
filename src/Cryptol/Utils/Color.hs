module Cryptol.Utils.Color (
    colorPrompt
  , errorMsg, errorAtMsg
  , warningMsg, warningAtMsg
  , testPassedMsg, testFailedMsg, testErrorMsg
  ) where

import System.Console.ANSI

data OutputColor = BadColor | GoodColor | PromptColor deriving (Enum, Eq)
colorizeString :: OutputColor -> String -> String
colorizeString color msg = prefix ++ msg ++ suffix where
    -- sgr | isBatch  = setSGRCode
    --     | otherwise = const ""
    sgr = setSGRCode
    prefix = case color of
                  BadColor -> sgr [SetColor Foreground Vivid Red]
                  GoodColor -> sgr [SetColor Foreground Vivid Green]
                  PromptColor -> sgr [SetColor Foreground Vivid Blue] ++ sgr [SetConsoleIntensity BoldIntensity]
    suffix = sgr [Reset]

colorPrompt :: String -> String
colorPrompt prompt = colorizeString PromptColor prompt

errorMsg :: String
errorMsg = colorizeString BadColor "[error]"

errorAtMsg :: String
errorAtMsg = errorMsg ++ " at"

warningMsg :: String
warningMsg = colorizeString BadColor "[warning]"

warningAtMsg :: String
warningAtMsg = warningMsg ++ " at"

testPassedMsg :: String
testPassedMsg = colorizeString GoodColor "Passed"

testFailedMsg :: String
testFailedMsg = colorizeString BadColor "FAILED"

testErrorMsg :: String
testErrorMsg = colorizeString BadColor "ERROR"
