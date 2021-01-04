-- |
-- Module      :  Cryptol.Eval.SeqMap
-- Copyright   :  (c) 2020 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--

module Cryptol.Backend.SeqMap
  ( SeqMap (..)
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
  , zipSeqMap
  , mapSeqMap
  ) where

import Control.Monad.IO.Class
import Data.IORef
import Data.List (genericIndex)
import qualified Data.Map.Strict as Map

import Cryptol.Backend
import Cryptol.Utils.Panic(panic)


lookupSeqMap :: SeqMap sym a -> Integer -> SEval sym a
lookupSeqMap (IndexSeqMap f) i = f i
lookupSeqMap (UpdateSeqMap m f) i =
  case Map.lookup i m of
    Just x  -> x
    Nothing -> f i

-- | Generate a finite sequence map from a list of values
finiteSeqMap :: [SEval sym a] -> SeqMap sym a
finiteSeqMap xs =
   UpdateSeqMap
      (Map.fromList (zip [0..] xs))
      (\i -> panic "finiteSeqMap" ["Out of bounds access of finite seq map", "length: " ++ show (length xs), show i])

-- | Generate an infinite sequence map from a stream of values
infiniteSeqMap :: Backend sym => sym -> [SEval sym a] -> SEval sym (SeqMap sym a)
infiniteSeqMap sym xs =
   -- TODO: use an int-trie?
   memoMap sym (IndexSeqMap $ \i -> genericIndex xs i)

-- | Create a finite list of length @n@ of the values from @[0..n-1]@ in
--   the given the sequence emap.
enumerateSeqMap :: (Integral n) => n -> SeqMap sym a -> [SEval sym a]
enumerateSeqMap n m = [ lookupSeqMap m  i | i <- [0 .. (toInteger n)-1] ]

-- | Create an infinite stream of all the values in a sequence map
streamSeqMap :: SeqMap sym a -> [SEval sym a]
streamSeqMap m = [ lookupSeqMap m i | i <- [0..] ]

-- | Reverse the order of a finite sequence map
reverseSeqMap :: Integer     -- ^ Size of the sequence map
              -> SeqMap sym a
              -> SeqMap sym a
reverseSeqMap n vals = IndexSeqMap $ \i -> lookupSeqMap vals (n - 1 - i)

updateSeqMap :: SeqMap sym a -> Integer -> SEval sym a -> SeqMap sym a
updateSeqMap (UpdateSeqMap m sm) i x = UpdateSeqMap (Map.insert i x m) sm
updateSeqMap (IndexSeqMap f) i x = UpdateSeqMap (Map.singleton i x) f

-- | Concatenate the first @n@ values of the first sequence map onto the
--   beginning of the second sequence map.
concatSeqMap :: Integer -> SeqMap sym  a -> SeqMap sym a -> SeqMap sym a
concatSeqMap n x y =
    IndexSeqMap $ \i ->
       if i < n
         then lookupSeqMap x i
         else lookupSeqMap y (i-n)

-- | Given a number @n@ and a sequence map, return two new sequence maps:
--   the first containing the values from @[0..n-1]@ and the next containing
--   the values from @n@ onward.
splitSeqMap :: Integer -> SeqMap sym a -> (SeqMap sym a, SeqMap sym a)
splitSeqMap n xs = (hd,tl)
  where
  hd = xs
  tl = IndexSeqMap $ \i -> lookupSeqMap xs (i+n)

-- | Drop the first @n@ elements of the given 'SeqMap'.
dropSeqMap :: Integer -> SeqMap sym a -> SeqMap sym a
dropSeqMap 0 xs = xs
dropSeqMap n xs = IndexSeqMap $ \i -> lookupSeqMap xs (i+n)

-- | Given a sequence map, return a new sequence map that is memoized using
--   a finite map memo table.
memoMap :: Backend sym => sym -> SeqMap sym a -> SEval sym (SeqMap sym a)
memoMap sym x = do
  stk <- sGetCallStack sym
  cache <- liftIO $ newIORef $ Map.empty
  return $ IndexSeqMap (memo cache stk)

  where
  memo cache stk i = do
    mz <- liftIO (Map.lookup i <$> readIORef cache)
    case mz of
      Just z  -> return z
      Nothing -> sWithCallStack sym stk (doEval cache i)

  doEval cache i = do
    v <- lookupSeqMap x i
    liftIO $ atomicModifyIORef' cache (\m -> (Map.insert i v m, ()))
    return v

-- | Apply the given evaluation function pointwise to the two given
--   sequence maps.
zipSeqMap ::
  Backend sym =>
  sym ->
  (a -> a -> SEval sym a) ->
  SeqMap sym a ->
  SeqMap sym a ->
  SEval sym (SeqMap sym a)
zipSeqMap sym f x y =
  memoMap sym (IndexSeqMap $ \i ->
    do xi <- lookupSeqMap x i
       yi <- lookupSeqMap y i
       f xi yi)

-- | Apply the given function to each value in the given sequence map
mapSeqMap ::
  Backend sym =>
  sym ->
  (a -> SEval sym a) ->
  SeqMap sym a -> SEval sym (SeqMap sym a)
mapSeqMap sym f x =
  memoMap sym (IndexSeqMap $ \i -> f =<< lookupSeqMap x i)
