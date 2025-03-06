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
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RecordWildCards #-}
module Cryptol.Parser.Position where

import           Data.Text(Text)
import qualified Data.Text as T

import GHC.Generics (Generic)
import Control.DeepSeq

import Cryptol.Utils.PP

data Located a  = Located { srcRange :: !Range, thing :: !a }
                  deriving (Eq, Ord, Show, Generic, NFData
                           , Functor, Foldable, Traversable )


data Position   = Position { line :: !Int, col :: !Int }
                  deriving (Eq, Ord, Show, Generic, NFData)

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

start :: Position
start = Position { line = 1, col = 1 }

move :: Position -> Char -> Position
move p c = case c of
            '\t' -> p { col = ((col p + 7) `div` 8) * 8 + 1 }
            '\n' -> p { col = 1, line = 1 + line p }
            _    -> p { col = 1 + col p }

moves :: Position -> Text -> Position
moves p cs = T.foldl' move p cs

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

