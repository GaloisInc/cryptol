#!/usr/bin/env runhaskell

{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

import Control.Monad (forM_)
import Cryptol.Parser.Lexer
import Cryptol.Utils.PP
import qualified Data.Text    as Text
import qualified Data.Text.IO as Text
import Text.Blaze.Html (Html, Attribute, AttributeValue, toValue, toHtml, (!))
import qualified Text.Blaze.Html as H
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A
import Text.Blaze.Html.Renderer.Pretty (renderHtml)


main :: IO ()
main =
  do txt <- Text.getContents
     putStrLn $ renderHtml
              $ page
              $ toHtml
              $ map toBlaze
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


page :: Html -> Html
page inner = do
    H.docTypeHtml ! A.xmlns "http://www.w3.org/1999/xhtml" $ do
        H.head $ do
            H.meta ! A.httpEquiv "Content-Type" ! A.content "text/html; charset=UTF-8"
            H.title "Cryptol Source"
            H.style $ H.preEscapedString sty
        H.body inner


toBlaze :: Located Token -> Html
toBlaze tok = H.span ! (A.class_ $ cl $ tokenType $ thing tok)
                     ! (A.title $ toValue $ show $ pp $ srcRange tok)
  $ H.toHtml
  $ tokenText
  $ thing tok


cl :: TokenT -> AttributeValue
cl tok =
  case tok of
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



sty :: String
sty = unlines
  [ "body { font-family: monospace }"
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
  ]

