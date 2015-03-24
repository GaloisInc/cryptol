-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe #-}
{-# LANGUAGE PatternGuards #-}
module Cryptol.Utils.PP
  ( PP(..)
  , pp
  , pretty
  , optParens
  , ppInfix
  , Assoc(..)
  , Infix(..)
  , module Text.PrettyPrint
  , ordinal
  , ordSuffix
  , commaSep
  ) where

import Text.PrettyPrint

class PP a where
  ppPrec :: Int -> a -> Doc

pp :: PP a => a -> Doc
pp = ppPrec 0

pretty :: PP a => a -> String
pretty  = show . pp

optParens :: Bool -> Doc -> Doc
optParens b body | b         = parens body
                 | otherwise = body


-- | Information about associativity.
data Assoc = LeftAssoc | RightAssoc | NonAssoc
              deriving (Show,Eq)

-- | Information about an infix expression of some sort.
data Infix op thing = Infix
  { ieOp    :: op       -- ^ operator
  , ieLeft  :: thing    -- ^ left argument
  , ieRight :: thing    -- ^ right argumrnt
  , iePrec  :: Int      -- ^ operator precedence
  , ieAssoc :: Assoc    -- ^ operator associativity
  }

commaSep :: [Doc] -> Doc
commaSep = fsep . punctuate comma


-- | Pretty print an infix expression of some sort.
ppInfix :: (PP thing, PP op)
        => Int            -- ^ Non-infix leaves are printed with this precedence
        -> (thing -> Maybe (Infix op thing))
                          -- ^ pattern to check if sub-thing is also infix
        -> Infix op thing -- ^ Pretty print this infix expression
        -> Doc
ppInfix lp isInfix expr =
  sep [ ppSub (wrapSub LeftAssoc ) (ieLeft expr) <+> pp (ieOp expr)
      , ppSub (wrapSub RightAssoc) (ieRight expr) ]
  where
  wrapSub dir p = p < iePrec expr || p == iePrec expr && ieAssoc expr /= dir

  ppSub w e
    | Just e1 <- isInfix e = optParens (w (iePrec e1)) (ppInfix lp isInfix e1)
  ppSub _ e                = ppPrec lp e



-- | Display a numeric values as an ordinar (e.g., 2nd)
ordinal :: (Integral a, Show a, Eq a) => a -> Doc
ordinal x = text (show x) <> text (ordSuffix x)

-- | The suffix to use when displaying a number as an oridinal
ordSuffix :: (Integral a, Eq a) => a -> String
ordSuffix n0 =
  case n `mod` 10 of
    1 | notTeen -> "st"
    2 | notTeen -> "nd"
    3 | notTeen -> "rd"
    _ -> "th"

  where
  n       = abs n0
  m       = n `mod` 100
  notTeen = m < 11 || m > 19


