-- |
-- Module      :  Cryptol.Parser.Position
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe #-}

{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RecordWildCards #-}
module Cryptol.Parser.Position (
  -- * Position
  Position,
  line, col, colOffset,
  start,
  startOfLine, beforeStartOfLine,
  move, moves, advanceColBy,
  replPosition,

  -- * Range
  Range(..),
  emptyRange,
  rComb, rCombs, rCombMaybe,
  rangeWithin,

  -- * Located
  Located(..),
  HasLoc(..), AddLoc(..),
  at,
  combLoc

) where

import           Data.Text(Text)
import qualified Data.Text as T

import GHC.Generics (Generic)
import Control.DeepSeq

import Cryptol.Utils.PP

data Located a  = Located { srcRange :: !Range, thing :: !a }
                  deriving (Eq, Ord, Show, Generic, NFData
                           , Functor, Foldable, Traversable )

data Position = Position {
  pLine :: !Int,
  -- ^ 1 based

  pCol :: !Int,
  -- ^ 1 based. Interpreting tabs.
  -- This is used for layout processing and pretty printing.

  pColOffset :: !Int
  -- ^ 0 based. UTF-32 offset in the line.
  -- Note that this does not interpret tabs.
  -- It is used for comparisons.
} deriving (Show, Generic, NFData)

line :: Position -> Int
line = pLine

col :: Position -> Int
col = pCol

colOffset :: Position -> Int
colOffset = pColOffset

instance Eq Position where
  x == y = line x == line y && colOffset x == colOffset y

instance Ord Position where
  compare x y =
    case compare (line x) (line y) of
      LT -> LT
      EQ -> compare (colOffset x) (colOffset y)
      GT -> GT

data Range      = Range { from   :: !Position
                        , to     :: !Position
                        , source :: FilePath }
                  deriving (Eq, Ord, Show, Generic, NFData)

-- | Returns `True` if the first range is contained in the second one.
rangeWithin :: Range -> Range -> Bool
a `rangeWithin` b =
  source a == source b && from a >= from b && to a <= to b

-- | An empty range.
--
-- Caution: using this on the LHS of a use of rComb will cause the empty source
-- to propagate.
emptyRange :: Range
emptyRange  = Range { from = start, to = start, source = "" }

replPosition :: (Int,Int) -> Position
replPosition (l,c) = Position { pLine = l, pCol = c, pColOffset = c }

start :: Position
start = Position { pLine = 1, pCol = 1, pColOffset = 0 }

startOfLine :: Int -> Position
startOfLine n = start { pLine = n }

beforeStartOfLine :: Int -> Position
beforeStartOfLine n = Position { pLine = n, pCol = 0, pColOffset = -1 }

advanceColBy :: Int -> Position -> Position
advanceColBy n p = p { pCol = pCol p + n, pColOffset = pColOffset p + n }

move :: Position -> Char -> Position
move p c = case c of
            '\t' -> p { pCol = ((col p + 7) `div` 8) * 8 + 1, pColOffset = colOffset p + 1 }
            '\n' -> p { pCol = 1, pLine = 1 + line p, pColOffset = 0 }
            _    -> p { pCol = 1 + col p, pColOffset = colOffset p + 1 }

moves :: Position -> Text -> Position
moves = T.foldl' move

rComb :: Range -> Range -> Range
rComb r1 r2  = Range { from = rFrom, to = rTo, source = source r1 }
  where rFrom = min (from r1) (from r2)
        rTo   = max (to r1)   (to r2)

rCombMaybe :: Maybe Range -> Maybe Range -> Maybe Range
rCombMaybe Nothing y = y
rCombMaybe x Nothing = x
rCombMaybe (Just x) (Just y) = Just (rComb x y)

rCombs :: [Range] -> Range
rCombs  = foldl1 rComb


--------------------------------------------------------------------------------

instance PP Position where
  ppPrec _ p = int (line p) <.> colon <.> int (col p)

instance PP Range where
  ppPrec _ r = text (source r) <.> char ':'
            <.> pp (from r) <.> text "--" <.> pp (to r)

instance PP a => PP (Located a) where
  ppPrec _ l = parens (text "at" <+> pp (srcRange l) <.> comma <+> pp (thing l))

instance PPName a => PPName (Located a) where
  ppNameFixity  Located { .. } = ppNameFixity thing
  ppPrefixName  Located { .. } = ppPrefixName thing
  ppInfixName   Located { .. } = ppInfixName  thing

--------------------------------------------------------------------------------

class HasLoc t where
  getLoc :: t -> Maybe Range

instance HasLoc Range where
  getLoc r = Just r

instance HasLoc (Located a) where
  getLoc r = Just (srcRange r)

instance (HasLoc a, HasLoc b) => HasLoc (a,b) where
  getLoc (f,t) = case getLoc f of
                   Nothing -> getLoc t
                   Just l ->
                      case getLoc t of
                        Nothing -> return l
                        Just l1 -> return (rComb l l1)

instance HasLoc a => HasLoc [a] where
  getLoc = go Nothing
    where
    go x [] = x
    go Nothing (x : xs)  = go (getLoc x) xs
    go (Just l) (x : xs) = case getLoc x of
                             Nothing -> go (Just l) xs
                             Just l1 -> go (Just (rComb l l1)) xs

instance HasLoc a => HasLoc (Maybe a) where
  getLoc Nothing = Nothing
  getLoc (Just x) = getLoc x

class HasLoc t => AddLoc t where
  addLoc  :: t -> Range -> t
  dropLoc :: t -> t

instance AddLoc (Located a) where
  addLoc t r = t { srcRange = r }
  dropLoc r  = r

at :: (HasLoc l, AddLoc t) => l -> t -> t
at l e = maybe e (addLoc e) (getLoc l)

combLoc :: (a -> b -> c) -> Located a -> Located b -> Located c
combLoc f l1 l2 = Located { srcRange = rComb (srcRange l1) (srcRange l2)
                          , thing    = f (thing l1) (thing l2)
                          }

