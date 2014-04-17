-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.BitVectors.STree
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Implementation of full-binary symbolic trees, providing logarithmic
-- time access to elements. Both reads and writes are supported.
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}

module Data.SBV.BitVectors.STree (STree, readSTree, writeSTree, mkSTree) where

import Data.Bits (Bits(..))

import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.Model

-- | A symbolic tree containing values of type e, indexed by
-- elements of type i. Note that these are full-trees, and their
-- their shapes remain constant. There is no API provided that
-- can change the shape of the tree. These structures are useful
-- when dealing with data-structures that are indexed with symbolic
-- values where access time is important. 'STree' structures provide
-- logarithmic time reads and writes.
type STree i e = STreeInternal (SBV i) (SBV e)

-- Internal representation, not exposed to the user
data STreeInternal i e = SLeaf e                        -- NB. parameter 'i' is phantom
                       | SBin  (STreeInternal i e) (STreeInternal i e)
                       deriving Show

instance (SymWord e, Mergeable (SBV e)) => Mergeable (STree i e) where
  symbolicMerge b (SLeaf i)  (SLeaf j)    = SLeaf (symbolicMerge b i j)
  symbolicMerge b (SBin l r) (SBin l' r') = SBin  (symbolicMerge b l l') (symbolicMerge b r r')
  symbolicMerge _ _          _            = error "SBV.STree.symbolicMerge: Impossible happened while merging states"

-- | Reading a value. We bit-blast the index and descend down the full tree
-- according to bit-values.
readSTree :: (Num i, Bits i, SymWord i, SymWord e) => STree i e -> SBV i -> SBV e
readSTree s i = walk (blastBE i) s
  where walk []     (SLeaf v)  = v
        walk (b:bs) (SBin l r) = ite b (walk bs r) (walk bs l)
        walk _      _          = error $ "SBV.STree.readSTree: Impossible happened while reading: " ++ show i

-- | Writing a value, similar to how reads are done. The important thing is that the tree
-- representation keeps updates to a minimum.
writeSTree :: (Mergeable (SBV e), Num i, Bits i, SymWord i, SymWord e) => STree i e -> SBV i -> SBV e -> STree i e
writeSTree s i j = walk (blastBE i) s
  where walk []     _          = SLeaf j
        walk (b:bs) (SBin l r) = SBin (ite b l (walk bs l)) (ite b (walk bs r) r)
        walk _      _          = error $ "SBV.STree.writeSTree: Impossible happened while reading: " ++ show i

-- | Construct the fully balanced initial tree using the given values.
mkSTree :: forall i e. HasKind i => [SBV e] -> STree i e
mkSTree ivals
  | isReal (undefined :: i)
  = error "SBV.STree.mkSTree: Cannot build a real-valued sized tree"
  | not (isBounded (undefined :: i))
  = error "SBV.STree.mkSTree: Cannot build an infinitely large tree"
  | reqd /= given
  = error $ "SBV.STree.mkSTree: Required " ++ show reqd ++ " elements, received: " ++ show given
  | True
  = go ivals
  where reqd = 2 ^ intSizeOf (undefined :: i)
        given = length ivals
        go []  = error "SBV.STree.mkSTree: Impossible happened, ran out of elements"
        go [l] = SLeaf l
        go ns  = let (l, r) = splitAt (length ns `div` 2) ns in SBin (go l) (go r)
