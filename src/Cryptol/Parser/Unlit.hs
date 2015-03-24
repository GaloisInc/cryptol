-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Convert a literate source file into an ordinary source file.

{-# LANGUAGE OverloadedStrings, Safe, PatternGuards #-}
module Cryptol.Parser.Unlit
  ( unLit, PreProc(..), guessPreProc, knownExts
  ) where

import           Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text
import           Data.Char(isSpace)
import           System.FilePath(takeExtension)

import           Cryptol.Utils.Panic

data PreProc = None | Markdown | LaTeX

knownExts :: [String]
knownExts  =
  [ "cry"
  , "tex"
  , "markdown"
  , "md"
  ]

guessPreProc :: FilePath -> PreProc
guessPreProc file = case takeExtension file of
                      ".tex"      -> LaTeX
                      ".markdown" -> Markdown
                      ".md"       -> Markdown
                      _           -> None

unLit :: PreProc -> Text -> Text
unLit None = id
unLit proc = Text.unlines . concatMap toCryptol . preProc proc . Text.lines

preProc :: PreProc -> [Text] -> [Block]
preProc p =
  case p of
    None     -> return . Code
    Markdown -> markdown
    LaTeX    -> latex


data Block = Code [Text] | Comment [Text]

toCryptol :: Block -> [Text]
toCryptol (Code xs) = xs
toCryptol (Comment ls) =
  case ls of
    []       -> []
    [l]      -> [ "/* " `Text.append` l `Text.append` " */" ]
    l1 : rest -> let (more, l) = splitLast rest
                 in "/* " `Text.append` l1 : more ++ [ l `Text.append` " */" ]

  where
  splitLast []  = panic "Cryptol.Parser.Unlit.toCryptol" [ "splitLast []" ]
  splitLast [x] = ([], x)
  splitLast (x : xs) = let (ys,y) = splitLast xs
                       in (x:ys,y)


mk :: ([Text] -> Block) -> [Text] -> [Block]
mk _ [] = []
mk c ls = [ c (reverse ls) ]


-- | The preprocessor for `markdown`
markdown :: [Text] -> [Block]
markdown = blanks []
  where
  comment current []    = mk Comment current
  comment current (l : ls)
    | isBlank l         = blanks (l : current) ls
    | otherwise         = comment (l : current) ls

  blanks current []     = mk Comment current
  blanks current (l : ls)
    | isCodeLine l             = mk Comment current ++ code [l] ls
    | Just op <- isOpenFence l = mk Comment (l : current) ++ fenced op [] ls
    | isBlank l                = blanks  (l : current) ls
    | otherwise                = comment (l : current) ls

  code current []       = mk Code current
  code current (l : ls)
    | isCodeLine l      = code (l : current) ls
    | otherwise         = mk Code current ++ comment [] (l : ls)

  fenced op current []     = mk op current  -- XXX should this be an error?
  fenced op current (l : ls)
    | isCloseFence l    = mk op current ++ comment [l] ls
    | otherwise         = fenced op (l : current) ls


  isOpenFence l  | "```cryptol" == l'         = Just Code
                 | "```"        == l'         = Just Code
                 | "```" `Text.isPrefixOf` l' = Just Comment
                 | otherwise                  = Nothing
    where
    l' = Text.dropWhile isSpace l
  isCloseFence l = "```" `Text.isPrefixOf` l
  isBlank l      = Text.all isSpace l
  isCodeLine l   = "\t" `Text.isPrefixOf` l || "    " `Text.isPrefixOf` l



-- | The preprocessor for `latex`
latex :: [Text] -> [Block]
latex = comment []
  where
  comment current []    = mk Comment current
  comment current (l : ls)
    | isBeginCode l     = mk Comment (l : current) ++ code [] ls
    | otherwise         = comment (l : current) ls

  code current []       = mk Code current
  code current (l : ls)
    | isEndCode l       = mk Code current ++ comment [l] ls
    | otherwise         = code (l : current) ls

  isBeginCode l = "\\begin{code}" `Text.isPrefixOf` l
  isEndCode l   = "\\end{code}"   `Text.isPrefixOf` l




