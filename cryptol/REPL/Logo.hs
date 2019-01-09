-- |
-- Module      :  REPL.Logo
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

module REPL.Logo where

import Cryptol.REPL.Monad
import Paths_cryptol (version)

import Cryptol.Version (commitShortHash,commitDirty)
import Data.Version (showVersion)
import System.Console.ANSI


type Version = String

type Logo = [String]

logo :: Bool -> (String -> [String]) -> Logo
logo useColor mk =
     [ sgr [SetColor Foreground Dull  White] ++ l | l <- ws ]
  ++ [ sgr [SetColor Foreground Vivid Blue ] ++ l | l <- vs ]
  ++ [ sgr [SetColor Foreground Dull  Blue ] ++ l | l <- ds ]
  ++ [ sgr [Reset] ]
  where
  sgr | useColor  = setSGRCode
      | otherwise = const []
  hashText | commitShortHash == "UNKNOWN" = ""
           | otherwise = " (" ++ commitShortHash ++
                                 (if commitDirty then ", modified)" else ")")
  versionText = "version " ++ showVersion version ++ hashText
  ver = sgr [SetColor Foreground Dull White]
        ++ replicate (lineLen - 20 - length versionText) ' '
        ++ versionText
  ls        = mk ver
  slen      = length ls `div` 3
  (ws,rest) = splitAt slen ls
  (vs,ds)   = splitAt slen rest
  lineLen   = length (head ls)

displayLogo :: Bool -> REPL ()
displayLogo useColor = unlessBatch (io (mapM_ putStrLn (logo useColor logo2)))

logo1 :: String -> [String]
logo1 ver =
    [ "                        _        _"
    , "   ___ _ __ _   _ _ __ | |_ ___ | |"
    , "  / __| \'__| | | | \'_ \\| __/ _ \\| |"
    , " | (__| |  | |_| | |_) | || (_) | |"
    , "  \\___|_|   \\__, | .__/ \\__\\___/|_|"
    , "            |___/|_| " ++ ver
    ]

logo2 :: String -> [String]
logo2 ver =
    [ "┏━╸┏━┓╻ ╻┏━┓╺┳╸┏━┓╻  "
    , "┃  ┣┳┛┗┳┛┣━┛ ┃ ┃ ┃┃  "
    , "┗━╸╹┗╸ ╹ ╹   ╹ ┗━┛┗━╸"
    , ver
    ]


