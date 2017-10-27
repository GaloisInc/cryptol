#!/usr/bin/env runhaskell

-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

import Cryptol.Parser.Lexer
import Cryptol.Utils.PP
import qualified Data.Text    as Text
import qualified Data.Text.IO as Text

main :: IO ()
main =
  do txt <- Text.getContents
     putStrLn $ wrap
              $ concat
              $ map toHTML
              $ fst
              $ primLexer defaultConfig txt

wrap :: String -> String
wrap txt = "<html><head>" ++ sty ++ "</head><body>" ++ txt ++ "</body>"

toHTML :: Located Token -> String
toHTML tok = "<span class=\"" ++ cl ++ "\" title=\"" ++ pos ++ "\">"
          ++ concatMap esc (Text.unpack (tokenText (thing tok)))
          ++ "</span>"
  where
  pos = show (pp (srcRange tok)) ++ " " ++ concatMap esc (show (tokenType (thing tok)))
  cl  = case tokenType (thing tok) of
          Num {}      -> "number"
          Ident {}    -> "identifier"
          KW {}       -> "keyword"
          Op {}       -> "operator"
          Sym {}      -> "symbol"
          Virt {}     -> "virtual"
          White Space -> "white"
          White _     -> "comment"
          Err {}      -> "error"
          EOF         -> "eof"
          StrLit {}   -> "text"
          ChrLit {}   -> "text"

  esc c = case c of
            '<'   -> "&lt;"
            '>'   -> "&gt;"
            '&'   -> "&amp;"
            ' '   -> "&nbsp;"
            '"'   -> "&quot;"
            '\n'  -> "<br>"
            _     -> [c]

sty :: String
sty = unlines
  [ "<style>"
  , "body { font-family: monospace }"
  , ".number        { color: #cc00cc }"
  , ".identifier    { }"
  , ".keyword       { color: blue; }"
  , ".operator      { color: #cc00cc }"
  , ".symbol        { color: blue }"
  , ".white         { }"
  , ".virtual       { background-color: red }"
  , ".comment       { color: green }"
  , ".error         { color: red }"
  , ".text          { color: #cc00cc }"
  , "</style>"
  ]

