#!/usr/bin/env runhaskell

-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{- A utility for spliting a long column of stuff into multiple columns. -}
import Data.List(transpose)

rs = 4      -- number of rows per column
spacing = 4 -- blanks between columns

main = interact (unlines . map concat . transpose . map toCol . chop rs . lines)

colWidth xs = spacing + maximum (0 : map length xs)

padTo x xs  = xs ++ replicate (x - length xs) ' '

toCol xs    = map (padTo (colWidth xs)) xs

chop n []   = []
chop n xs   = let (as,bs) = splitAt n xs
              in as : chop n bs
