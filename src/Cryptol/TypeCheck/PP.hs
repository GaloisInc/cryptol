-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
module Cryptol.TypeCheck.PP
  ( NameMap, WithNames(..)
  , emptyNameMap
  , ppWithNamesPrec, ppWithNames
  , intToName, nameList
  , dump
  , module Cryptol.Utils.PP
  ) where

import           Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import           Data.List(transpose)
import           Cryptol.Utils.PP


type NameMap = IntMap String

emptyNameMap :: NameMap
emptyNameMap = IntMap.empty

-- | This packages together a type with some names to be used to display
-- the variables.  It is used for pretty printing types.
data WithNames a = WithNames a NameMap

ppWithNamesPrec :: PP (WithNames a) => NameMap -> Int -> a -> Doc
ppWithNamesPrec names prec t = ppPrec prec (WithNames t names)

ppWithNames :: PP (WithNames a) => NameMap -> a -> Doc
ppWithNames names t = ppWithNamesPrec names 0 t

dump :: PP (WithNames a) => a -> String
dump x = show (ppWithNames IntMap.empty x)

-- | Compute the n-th variant of a name (e.g., @a5@).
nameVariant :: Int -> String -> String
nameVariant 0 x   = x
nameVariant n x   = x ++ show n

-- | Compute all variants of a name: @a, a1, a2, a3, ...@
nameVariants :: String -> [String]
nameVariants x = map (`nameVariant` x) [ 0 .. ]

-- | Expand a list of base names into an infinite list of variations.
nameList :: [String] -> [String]
nameList names = concat $ transpose $ map nameVariants baseNames
  where
  baseNames | null names = map (:[]) [ 'a' .. 'z' ]
            | otherwise  = names

intToName :: Int -> String
intToName x = nameList [] !! x

