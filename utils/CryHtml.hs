#!/usr/bin/env runhaskell

-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

import Cryptol.Parser.Lexer
import Cryptol.Utils.PP

main :: IO ()
main = interact (wrap . concat . map toHTML . fst . primLexer defaultConfig)

wrap :: String -> String
wrap txt = "<html><head>" ++ sty ++ "</head><body>" ++ txt ++ "</body>"

toHTML :: Located Token -> String
toHTML tok = "<span class=\"" ++ cl ++ "\" title=\"" ++ pos ++ "\">"
          ++ concatMap esc (tokenText (thing tok))
          ++ "</span>"
  where
  pos = show (pp (srcRange tok)) ++ " " ++ show (tokenType (thing tok))
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

