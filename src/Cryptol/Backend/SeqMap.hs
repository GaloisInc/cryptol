-- |
-- Module      :  Cryptol.Backend.SeqMap
-- Copyright   :  (c) 2013-2021 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Cryptol.Backend.SeqMap
  ( -- * Sequence Maps
    SeqMap
  , indexSeqMap
  , lookupSeqMap
  , finiteSeqMap
  , infiniteSeqMap
  , enumerateSeqMap
  , streamSeqMap
  , reverseSeqMap
  , updateSeqMap
  , dropSeqMap
  , concatSeqMap
  , splitSeqMap
  , memoMap
  , delaySeqMap
  , zipSeqMap
  , mapSeqMap
  , mergeSeqMap
  , barrelShifter
  , shiftSeqByInteger

  , IndexSegment(..)
  ) where

import qualified Control.Exception as X
import Control.Monad
import Control.Monad.IO.Class
import Data.Bits
import Data.List
import Data.IORef
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Cryptol.Backend
import Cryptol.Backend.Concrete (Concrete)
import Cryptol.Backend.Monad (Unsupported(..))

import Cryptol.TypeCheck.Solver.InfNat(Nat'(..))
import Cryptol.Utils.Panic

-- | A sequence map represents a mapping from nonnegative integer indices
--   to values.  These are used to represent both finite and infinite sequences.
data SeqMap sym a
  = IndexSeqMap  !(Integer -> SEval sym a)
  | UpdateSeqMap !(Map Integer (SEval sym a))
                 !(SeqMap sym a)
  | MemoSeqMap
     !Nat'
     !(IORef (Map Integer a, Integer -> SEval sym a))
     !(Integer -> SEval sym a)
      -- Use this to overwrite the evaluation function when the cache is full

indexSeqMap :: (Integer -> SEval sym a) -> SeqMap sym a
indexSeqMap = IndexSeqMap

lookupSeqMap :: Backend sym => SeqMap sym a -> Integer -> SEval sym a
lookupSeqMap (IndexSeqMap f) i = f i
lookupSeqMap (UpdateSeqMap m xs) i =
  case Map.lookup i m of
    Just x  -> x
    Nothing -> lookupSeqMap xs i

lookupSeqMap (MemoSeqMap sz cache_eval evalPanic) i =
  do (cache,eval) <- liftIO (readIORef cache_eval)
     case Map.lookup i cache of
       Just z -> pure z
       Nothing ->
        do v <- eval i
           liftIO $ atomicModifyIORef' cache_eval $ \(oldCache,oldFun) ->
             let !newCache = Map.insert i v oldCache
                 -- If we memoize the entire map,
                 -- overwrite the evaluation closure to let
                 -- the garbage collector reap it
                 !newEval =
                   case sz of
                     Nat sz' | toInteger (Map.size newCache) >= sz' -> evalPanic
                     _ -> oldFun
             in ((newCache, newEval), v)

instance Backend sym => Functor (SeqMap sym) where
  fmap f xs = IndexSeqMap (\i -> f <$> lookupSeqMap xs i)

-- | Generate a finite sequence map from a list of values
finiteSeqMap :: Backend sym => sym -> [SEval sym a] -> SeqMap sym a
finiteSeqMap sym xs =
   UpdateSeqMap
      (Map.fromList (zip [0..] xs))
      (IndexSeqMap (\i -> invalidIndex sym i))

-- | Generate an infinite sequence map from a stream of values
infiniteSeqMap :: Backend sym => sym -> [SEval sym a] -> SEval sym (SeqMap sym a)
infiniteSeqMap sym xs =
   -- TODO: use an int-trie?
   memoMap sym Inf (IndexSeqMap $ \i -> genericIndex xs i)

-- | Create a finite list of length @n@ of the values from @[0..n-1]@ in
--   the given the sequence emap.
enumerateSeqMap :: (Backend sym, Integral n) => n -> SeqMap sym a -> [SEval sym a]
enumerateSeqMap n m = [ lookupSeqMap m  i | i <- [0 .. (toInteger n)-1] ]

-- | Create an infinite stream of all the values in a sequence map
streamSeqMap :: Backend sym => SeqMap sym a -> [SEval sym a]
streamSeqMap m = [ lookupSeqMap m i | i <- [0..] ]

-- | Reverse the order of a finite sequence map
reverseSeqMap :: Backend sym =>
  Integer {- ^ Size of the sequence map -} ->
  SeqMap sym a ->
  SeqMap sym a
reverseSeqMap n vals = IndexSeqMap $ \i -> lookupSeqMap vals (n - 1 - i)

updateSeqMap :: SeqMap sym a -> Integer -> SEval sym a -> SeqMap sym a
updateSeqMap (UpdateSeqMap m sm) i x = UpdateSeqMap (Map.insert i x m) sm
updateSeqMap xs i x = UpdateSeqMap (Map.singleton i x) xs

-- | Concatenate the first @n@ values of the first sequence map onto the
--   beginning of the second sequence map.
concatSeqMap :: Backend sym => Integer -> SeqMap sym a -> SeqMap sym a -> SeqMap sym a
concatSeqMap n x y =
    IndexSeqMap $ \i ->
       if i < n
         then lookupSeqMap x i
         else lookupSeqMap y (i-n)

-- | Given a number @n@ and a sequence map, return two new sequence maps:
--   the first containing the values from @[0..n-1]@ and the next containing
--   the values from @n@ onward.
splitSeqMap :: Backend sym => Integer -> SeqMap sym a -> (SeqMap sym a, SeqMap sym a)
splitSeqMap n xs = (hd,tl)
  where
  hd = xs
  tl = IndexSeqMap $ \i -> lookupSeqMap xs (i+n)

-- | Drop the first @n@ elements of the given 'SeqMap'.
dropSeqMap :: Backend sym => Integer -> SeqMap sym a -> SeqMap sym a
dropSeqMap 0 xs = xs
dropSeqMap n xs = IndexSeqMap $ \i -> lookupSeqMap xs (i+n)

delaySeqMap :: Backend sym => sym -> SEval sym (SeqMap sym a) -> SEval sym (SeqMap sym a)
delaySeqMap sym xs =
  do xs' <- sDelay sym xs
     pure $ IndexSeqMap $ \i -> do m <- xs'; lookupSeqMap m i

-- | Given a sequence map, return a new sequence map that is memoized using
--   a finite map memo table.
memoMap :: Backend sym => sym -> Nat' -> SeqMap sym a -> SEval sym (SeqMap sym a)

-- Sequence is alreay memoized, just return it
memoMap _sym _sz x@(MemoSeqMap{}) = pure x

memoMap sym sz x = do
  stk <- sGetCallStack sym
  cache <- liftIO $ newIORef (Map.empty, eval stk)
  return (MemoSeqMap sz cache evalPanic)

  where
    eval stk i = sWithCallStack sym stk (lookupSeqMap x i)

    -- Not 100% sure that we actually need to do the bounds check here,
    -- or if we are assuming that the argument would be in bounds, but
    -- it doesn't really hurt to do it, as if we *did* already do the check
    -- this code should never run (unless we messed up something).
    evalPanic i = case sz of
                    Nat sz' | i < 0 || i >= sz' -> invalidIndex sym i
                    _ -> panic "lookupSeqMap"
                            ["Messed up size accounting", show sz, show i]


-- | Apply the given evaluation function pointwise to the two given
--   sequence maps.
zipSeqMap ::
  Backend sym =>
  sym ->
  (a -> a -> SEval sym a) ->
  Nat' ->
  SeqMap sym a ->
  SeqMap sym a ->
  SEval sym (SeqMap sym a)
zipSeqMap sym f sz x y =
  memoMap sym sz (IndexSeqMap $ \i -> join (f <$> lookupSeqMap x i <*> lookupSeqMap y i))

-- | Apply the given function to each value in the given sequence map
mapSeqMap ::
  Backend sym =>
  sym ->
  (a -> SEval sym a) ->
  Nat' ->
  SeqMap sym a ->
  SEval sym (SeqMap sym a)
mapSeqMap sym f sz x =
  memoMap sym sz (IndexSeqMap $ \i -> f =<< lookupSeqMap x i)


{-# INLINE mergeSeqMap #-}
mergeSeqMap :: Backend sym =>
  sym ->
  (SBit sym -> a -> a -> SEval sym a) ->
  SBit sym ->
  SeqMap sym a ->
  SeqMap sym a ->
  SeqMap sym a
mergeSeqMap sym f c x y =
  IndexSeqMap $ \i -> mergeEval sym f c (lookupSeqMap x i) (lookupSeqMap y i)


{-# INLINE shiftSeqByInteger #-}
shiftSeqByInteger :: Backend sym =>
  sym ->
  (SBit sym -> a -> a -> SEval sym a)
     {- ^ if/then/else operation of values -} ->
  (Integer -> Integer -> Maybe Integer)
     {- ^ reindexing operation -} ->
  SEval sym a {- ^ zero value -} ->
  Nat' {- ^ size of the sequence -} ->
  SeqMap sym a {- ^ sequence to shift -} ->
  SInteger sym {- ^ shift amount, assumed to be in range [0,len] -} ->
  SEval sym (SeqMap sym a)
shiftSeqByInteger sym merge reindex zro m xs idx
  | Just j <- integerAsLit sym idx = shiftOp xs j
  | otherwise =
      do (n, idx_bits) <- enumerateIntBits sym m idx
         barrelShifter sym merge shiftOp m xs n (map BitIndexSegment idx_bits)
 where
   shiftOp vs shft =
     pure $ indexSeqMap $ \i ->
       case reindex i shft of
         Nothing -> zro
         Just i' -> lookupSeqMap vs i'


data IndexSegment sym
  = BitIndexSegment (SBit sym)
  | WordIndexSegment (SWord sym)

{-# SPECIALIZE
  barrelShifter ::
  Concrete ->
  (SBit Concrete -> a -> a -> SEval Concrete a) ->
  (SeqMap Concrete a -> Integer -> SEval Concrete (SeqMap Concrete a)) ->
  Nat' ->
  SeqMap Concrete a ->
  Integer ->
  [IndexSegment Concrete] ->
  SEval Concrete (SeqMap Concrete a)
 #-}
barrelShifter :: Backend sym =>
  sym ->
  (SBit sym -> a -> a -> SEval sym a)
     {- ^ if/then/else operation of values -} ->
  (SeqMap sym a -> Integer -> SEval sym (SeqMap sym a))
     {- ^ concrete shifting operation -} ->
  Nat' {- ^ Size of the map being shifted -} ->
  SeqMap sym a {- ^ initial value -} ->
  Integer {- Number of bits in shift amount -} ->
  [IndexSegment sym]  {- ^ segments of the shift amount, in big-endian order -} ->
  SEval sym (SeqMap sym a)
barrelShifter sym mux shift_op sz x0 n0 bs0
  | n0 >= toInteger (maxBound :: Int) =
      liftIO (X.throw (UnsupportedSymbolicOp ("Barrel shifter with too many bits in shift amount: " ++ show n0)))
  | otherwise = go x0 (fromInteger n0) bs0

  where
  go x !_n [] = return x

  go x !n (WordIndexSegment w:bs) =
    let n' = n - fromInteger (wordLen sym w) in
    case wordAsLit sym w of
      Just (_,0) -> go x n' bs
      Just (_,j) ->
        do x_shft <- shift_op x (j * bit n')
           go x_shft n' bs
      Nothing ->
        do wbs <- unpackWord sym w
           go x n (map BitIndexSegment wbs ++ bs)

  go x !n (BitIndexSegment b:bs) =
    let n' = n - 1 in
    case bitAsLit sym b of
      Just False -> go x n' bs
      Just True ->
        do x_shft <- shift_op x (bit n')
           go x_shft n' bs
      Nothing ->
        do x_shft <- shift_op x (bit n')
           x' <- memoMap sym sz (mergeSeqMap sym mux b x_shft x)
           go x' n' bs
