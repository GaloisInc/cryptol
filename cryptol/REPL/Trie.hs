-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

module REPL.Trie where

import           Cryptol.Utils.Panic (panic)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe,maybeToList)


-- | Maps string names to values, allowing for partial key matches and querying.
data Trie a = Node (Map.Map Char (Trie a)) (Maybe a)
    deriving (Show)

emptyTrie :: Trie a
emptyTrie  = Node Map.empty Nothing

-- | Insert a value into the Trie.  Will call `panic` if a value already exists
-- with that key.
insertTrie :: String -> a -> Trie a -> Trie a
insertTrie k a = loop k
  where
  loop key (Node m mb) = case key of
    c:cs -> Node (Map.alter (Just . loop cs . fromMaybe emptyTrie) c m) mb
    []   -> case mb of
      Nothing -> Node m (Just a)
      Just _  -> panic "[REPL] Trie" ["key already exists:", "\t" ++ k]

-- | Return all matches with the given prefix.
lookupTrie :: String -> Trie a -> [a]
lookupTrie key t@(Node mp _) = case key of

  c:cs -> case Map.lookup c mp of
    Just m' -> lookupTrie cs m'
    Nothing -> []

  [] -> leaves t

-- | Return all of the values from a Trie.
leaves :: Trie a -> [a]
leaves (Node mp mb) = maybeToList mb ++ concatMap leaves (Map.elems mp)
