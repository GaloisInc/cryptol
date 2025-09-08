-- |
-- Module      :  REPL.Logo
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

module REPL.Logo where

import Cryptol.REPL.Monad
import Cryptol.Utils.Panic (panic)
import Paths_cryptol (version)

import Cryptol.Version (commitShortHash,commitDirty)
import Data.Version (showVersion)
import System.Console.ANSI
import Prelude ()
import Prelude.Compat


type Version = String

type Logo = [String]

-- | The list of 'String's returned by the @mk@ function should be non-empty.
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
        ++ versionText ++ "\n"
        ++ "https://cryptol.net  :? for help"
  ls        = mk ver
  slen      = length ls `div` 3
  (ws,rest) = splitAt slen ls
  (vs,ds)   = splitAt slen rest
  line      = case ls of
                line':_ -> line'
                [] -> panic "logo" ["empty lines"]
  lineLen   = length line

displayLogo :: Bool -> Bool -> REPL ()
displayLogo useColor useUnicode =
  unlessBatch (io (mapM_ putStrLn (logo useColor (if useUnicode then logo2 else logo1))))

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


