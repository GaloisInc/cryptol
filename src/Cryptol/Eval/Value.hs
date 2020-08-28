-- |
-- Module      :  Cryptol.Eval.Value
-- Copyright   :  (c) 2013-2016 Galois, Inc.
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
{-# LANGUAGE Safe #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Cryptol.Eval.Value
  ( -- * GenericValue
    GenValue(..)
  , forceValue
  , Backend(..)
  , asciiMode
    -- ** Value introduction operations
  , word
  , lam
  , wlam
  , flam
  , tlam
  , nlam
  , ilam
    -- ** Value eliminators
  , fromVBit
  , fromVInteger
  , fromVRational
  , fromVFloat
  , fromVSeq
  , asIndex
  , tryFromBits
  , fromVFun
  , fromVPoly
  , fromVNumPoly
  , fromVTuple
  , fromVRecord
  , lookupRecord
    -- ** Pretty printing
  , defaultPPOpts
  , ppValue

    -- * Sequence Maps
  , SeqMap
  , lookupSeqMap
  , enumerateSeqMap
  , actualizeSeqMap
  , voidSeqMap
  , delaySeqMap
  , generateSeqMap
  , updateSeqMap
  , finiteSeqMap
  , unpackSeqMap
  , concatSeqMap
  , joinSeqMap
  , takeSeqMap
  , dropSeqMap
  , packSeqMap
  , reverseSeqMap
  , splitSeqMap
  , memoMap
  , zipSeqMap
  , mapSeqMap
  , bitwiseWordUnOp
  , bitwiseWordBinOp
  , leftShiftSeqMap
  , rightShiftSeqMap
  , leftRotateSeqMap
  , rightRotateSeqMap

  , generateSeqMap'
  , finiteSeqMap'
  , unpackSeqMap'

  -- * merging values
  , iteValue
  , mergeSeqMap
  ) where

import Control.Monad.IO.Class
--import Data.Bits
import Data.List (genericTake)
import Data.IORef
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import MonadLib

import qualified Cryptol.Eval.Arch as Arch
import Cryptol.Eval.Backend
import Cryptol.Eval.Monad
import Cryptol.Eval.Type

import Cryptol.TypeCheck.Solver.InfNat(Nat'(..))
import Cryptol.Utils.Ident (Ident)
import Cryptol.Utils.Panic(panic)
import Cryptol.Utils.PP
import Cryptol.Utils.RecordMap

--import Data.List(genericIndex)

import GHC.Generics (Generic)

-- Values ----------------------------------------------------------------------

-- | A sequence map represents a mapping from nonnegative integer indices
--   to values.  These are used to represent both finite and infinite sequences.
data SeqMap sym
  = GenerateSeqMap !(Integer -> SEval sym (GenValue sym))

  | VoidSeqMap
      -- ^ Seq map representing out-of-bound indexing
  | UpdateSeqMap !(Map Integer (SEval sym (GenValue sym))) !(SeqMap sym)

  | UnpackSeqMap !(SWord sym)
      -- ^ Invariant: word length is at least 1
  | JoinSeqMap !Integer !(SeqMap sym)
      -- ^ Invariant: @each@ is > 0
  | ConcatSeqMap !Integer !(SeqMap sym) !(SeqMap sym)
      -- ^ Invariant: @front@ is > 0
  | DropSeqMap !Integer !(SeqMap sym)
      -- ^ Invariant: @front@ is > 0
  | DelaySeqMap !(SEval sym (SeqMap sym))
      -- ^ Basically a no-op, but makes sequence maps lazier
  | MemoSeqMap !(SeqMapCache sym) !(SeqMap sym)
      -- ^ Memoized sequence

instance Show (SeqMap sym) where
  showsPrec _ VoidSeqMap = showString "void"
  showsPrec _ (GenerateSeqMap _) = showString "generate"
  showsPrec _ (UnpackSeqMap _) = showString "word"
  showsPrec p (UpdateSeqMap m xs) = showParen (p > 0) $
    showString "update" . shows (fst <$> Map.toList m) . showsPrec 1 xs
  showsPrec p (JoinSeqMap each xs) = showParen (p > 0) $
    showString "join " . shows each . showChar ' ' . showsPrec 1 xs
  showsPrec p (ConcatSeqMap front xs ys) = showParen (p > 0) $
    showString "concat " . shows front .
    showChar ' ' . showsPrec 1 xs .
    showChar ' ' . showsPrec 1 ys
  showsPrec p (DropSeqMap toDrop xs) = showParen (p > 0) $
    showString "drop " . shows toDrop .
    showChar ' ' . showsPrec 1 xs
  showsPrec _ (DelaySeqMap _) = showString "delay"
  showsPrec p (MemoSeqMap _c xs) = showParen (p > 0) $
    showString "memo " . showsPrec 1 xs

delaySeqMap :: Backend sym =>
  sym -> SEval sym (SeqMap sym) -> SEval sym (SeqMap sym)
delaySeqMap sym xs =
  sMaybeReady sym xs >>= \case
    Just _  -> xs
    Nothing -> DelaySeqMap <$> sDelay sym Nothing xs

type SeqMapCache sym = IORef (Map Integer (GenValue sym))

voidSeqMap :: SeqMap sym
voidSeqMap = VoidSeqMap

evalMemo :: Backend sym => sym -> Integer -> SeqMapCache sym -> SeqMap sym -> SEval sym (GenValue sym)
evalMemo sym i cache vs =
  liftIO (Map.lookup i <$> readIORef cache) >>= \case
    Just z -> pure z
    Nothing ->
      do v <- lookupSeqMap sym i vs
         liftIO $ atomicModifyIORef' cache (\m -> (Map.insert i v m, ()))
         pure v

lookupSeqMap :: Backend sym => sym -> Integer -> SeqMap sym -> SEval sym (GenValue sym)
lookupSeqMap sym i VoidSeqMap = invalidIndex sym i
lookupSeqMap _   i (GenerateSeqMap f) = f i
lookupSeqMap sym i (UnpackSeqMap w) = VBit <$> wordBit sym w i
lookupSeqMap sym i (DelaySeqMap xs) = lookupSeqMap sym i =<< xs
lookupSeqMap sym i (MemoSeqMap cache vs) = evalMemo sym i cache vs
lookupSeqMap sym i (UpdateSeqMap m sm) =
  case Map.lookup i m of
    Just x  -> x
    Nothing -> lookupSeqMap sym i sm
lookupSeqMap sym i (JoinSeqMap each sm) =
  do let (q,r) = divMod i each
     xs <- fromVSeq <$> (lookupSeqMap sym q sm)
     lookupSeqMap sym r xs
lookupSeqMap sym i (ConcatSeqMap front xs ys)
  | i < front = lookupSeqMap sym i xs
  | otherwise = lookupSeqMap sym (i - front) ys
lookupSeqMap sym i (DropSeqMap front xs) =
  lookupSeqMap sym (i + front) xs

enumerateSeqMap :: Backend sym => sym -> Integer -> SeqMap sym -> [SEval sym (GenValue sym)]
enumerateSeqMap sym len sm = [ lookupSeqMap sym i sm | i <- [ 0 .. len-1 ] ]

generateSeqMap :: Backend sym =>
  sym ->
  (Integer -> SEval sym (GenValue sym)) ->
  SEval sym (SeqMap sym)
generateSeqMap _ f = pure (GenerateSeqMap f)

generateSeqMap' :: Backend sym =>
  (Integer -> SEval sym (GenValue sym)) -> SeqMap sym
generateSeqMap' f = GenerateSeqMap f

finiteSeqMap' :: Backend sym => [SEval sym (GenValue sym)] -> SeqMap sym
finiteSeqMap' [] = VoidSeqMap
finiteSeqMap' xs = UpdateSeqMap (Map.fromList (zip [0..] xs)) VoidSeqMap

unpackSeqMap' :: SWord sym -> SeqMap sym
unpackSeqMap' w = UnpackSeqMap w

-- | Generate a finite sequence map from a list of values
finiteSeqMap :: Backend sym => sym -> [SEval sym (GenValue sym)] -> SEval sym (SeqMap sym)
finiteSeqMap _sym xs = pure $ finiteSeqMap' xs

unpackSeqMap :: Backend sym =>
  sym ->
  SWord sym ->
  SEval sym (SeqMap sym)
unpackSeqMap _ w = pure (UnpackSeqMap w)

updateSeqMap :: Backend sym =>
  sym ->
  SeqMap sym ->
  Integer ->
  SEval sym (GenValue sym) ->
  SEval sym (SeqMap sym)
updateSeqMap _sym (UpdateSeqMap m vs) i x = pure (UpdateSeqMap (Map.insert i x m) vs)
updateSeqMap _sym vs i x = pure (UpdateSeqMap (Map.singleton i x) vs)

-- | Concatenate the first @n@ values of the first sequence map onto the
--   beginning of the second sequence map.
concatSeqMap :: Backend sym =>
  sym ->
  Integer ->
  SeqMap sym ->
  SeqMap sym ->
  SEval sym (SeqMap sym)
concatSeqMap _sym _front xs VoidSeqMap = pure xs
concatSeqMap sym _front (UnpackSeqMap wx) (UnpackSeqMap wy) =
  UnpackSeqMap <$> joinWord sym wx wy
concatSeqMap _sym front xs ys
  | front <= 0 = pure ys
  | otherwise  = pure (ConcatSeqMap front xs ys)

joinSeqMap :: Backend sym =>
  sym ->
  Integer ->
  SeqMap sym ->
  SEval sym (SeqMap sym)
joinSeqMap _sym each vs
  | each > 0  = pure (JoinSeqMap each vs)
  | otherwise = pure VoidSeqMap

takeSeqMap :: Backend sym =>
  sym ->
  Integer ->
  SeqMap sym ->
  SEval sym (SeqMap sym)
takeSeqMap sym toTake vs = case vs of
  VoidSeqMap -> pure VoidSeqMap

  ConcatSeqMap front xs ys
    | front == toTake -> pure xs
    | front > toTake  -> takeSeqMap sym toTake xs
    | otherwise ->
        do ys' <- delaySeqMap sym (takeSeqMap sym (toTake - front) ys)
           pure (ConcatSeqMap front xs ys')

  UpdateSeqMap m vs' ->
    do vs'' <- delaySeqMap sym (takeSeqMap sym toTake vs')
       pure (UpdateSeqMap (takeUpdates toTake m) vs'')

  UnpackSeqMap w -> UnpackSeqMap <$> takeWord sym toTake w

  _ -> pure vs

dropSeqMap :: Backend sym =>
  sym ->
  Integer ->
  SeqMap sym ->
  SEval sym (SeqMap sym)
dropSeqMap sym toDrop vs
  | toDrop <= 0 = pure vs
  | otherwise = case vs of

        VoidSeqMap -> pure VoidSeqMap

        ConcatSeqMap front xs ys
           | front == toDrop -> pure ys
           | front < toDrop ->
               dropSeqMap sym (toDrop - front) ys
           | otherwise -> -- front > toDrop
               do xs' <- dropSeqMap sym toDrop xs
                  pure (ConcatSeqMap (front - toDrop) xs' ys)

        DropSeqMap x vs' -> dropSeqMap sym (toDrop+x) vs'

        UpdateSeqMap m vs' ->
           do vs'' <- dropSeqMap sym toDrop vs'
              pure (UpdateSeqMap (dropUpdates toDrop m) vs'')

        UnpackSeqMap w -> UnpackSeqMap <$> dropWord sym toDrop w

        _ -> pure (DropSeqMap toDrop vs)

takeUpdates :: Integer -> Map Integer a -> Map Integer a
takeUpdates toTake m = fst (Map.split toTake m)

dropUpdates :: Integer -> Map Integer a -> Map Integer a
dropUpdates toDrop m =
  case Map.splitLookup toDrop m of
    (_, Just a, m')  -> Map.insert 0 a (Map.mapKeysMonotonic (\i -> i - toDrop) m')
    (_, Nothing, m') -> Map.mapKeysMonotonic (\i -> i - toDrop) m'


leftRotateSeqMap :: Backend sym =>
  sym -> (Integer -> SEval sym (SeqMap sym)) -> Nat' -> SeqMap sym -> Integer -> SEval sym (SeqMap sym)
leftRotateSeqMap _ _ Inf _ _ = panic "leftRotateSeqMap" ["Cannot rotate infinite sequences"]
leftRotateSeqMap sym _ (Nat n) xs amt
  | i == 0 = pure xs
  | otherwise =
      do hd <- takeSeqMap sym i xs
         tl <- dropSeqMap sym i xs
         concatSeqMap sym (n - i) tl hd
 where
 i = amt `mod` n

rightRotateSeqMap :: Backend sym =>
  sym -> (Integer -> SEval sym (SeqMap sym)) -> Nat' -> SeqMap sym -> Integer -> SEval sym (SeqMap sym)
rightRotateSeqMap _ _ Inf _ _ = panic "rightRotateSeqMap" ["Cannot rotate infinite sequences"]
rightRotateSeqMap sym _ (Nat n) xs amt
  | i == 0 = pure xs
  | otherwise =
      do hd <- takeSeqMap sym i xs
         tl <- dropSeqMap sym i xs
         concatSeqMap sym (n - i) tl hd
 where
 i = (n - amt) `mod` n

leftShiftSeqMap :: Backend sym =>
  sym -> (Integer -> SEval sym (SeqMap sym)) -> Nat' -> SeqMap sym -> Integer -> SEval sym (SeqMap sym)
leftShiftSeqMap sym _ Inf xs toShift =
  dropSeqMap sym toShift xs
leftShiftSeqMap _ _ _ xs 0 = pure xs
leftShiftSeqMap sym mkZro (Nat n) xs toShift
  | toShift < n
  = do xs' <- dropSeqMap sym toShift xs
       zs  <- mkZro toShift
       concatSeqMap sym (n - toShift) xs' zs
  | otherwise = mkZro n

rightShiftSeqMap :: Backend sym =>
  sym -> (Integer -> SEval sym (SeqMap sym)) -> Nat' -> SeqMap sym -> Integer -> SEval sym (SeqMap sym)
rightShiftSeqMap sym mkZro Inf xs toShift =
  do zs <- mkZro toShift
     concatSeqMap sym toShift zs xs
rightShiftSeqMap _ _ _ xs 0 = pure xs
rightShiftSeqMap sym mkZro (Nat n) xs toShift
  | toShift < n
  = do zs <- mkZro toShift
       xs' <- takeSeqMap sym (n - toShift) xs
       concatSeqMap sym toShift zs xs'
  | otherwise = mkZro n

computeSegments :: Integer -> Integer -> Map Integer a -> [Either (Integer, Integer) a]
computeSegments start0 end0 m =
  case Map.splitLookup start0 m of
    (_, Just a, m')  -> Right a : go (start0+1) end0 (Map.toList m')
    (_, Nothing, m') -> go start0 end0 (Map.toList m')

 where
   go start end _ | start > end = []
   go start end [] = [Left (start, end)]
   go start end ((k,a):ks)
     | start == k = Right a : go (start+1) end ks
     | k > end    = [Left (start, end)]
     | otherwise  = Left (start, k-1) : Right a : go (k+1) end ks

getWordSegments ::
  Backend sym =>
  sym ->
  Integer ->
  SeqMap sym ->
  SEval sym [Either (SEval sym (SBit sym)) (SWord sym)]
getWordSegments sym len0 xs0
  | len0 <= 0 = pure []
  | otherwise = segs 0 len0 xs0

  where
  segs start _len VoidSeqMap =
    invalidIndex sym start

  segs start len (GenerateSeqMap f) =
    pure [ Left (fromVBit <$> f i) | i <- genericTake len [ start .. ] ]

  segs start len (MemoSeqMap cache vs) =
    pure [ Left (fromVBit <$> evalMemo sym i cache vs) | i <- genericTake len [ start .. ] ]

  segs start len (DelaySeqMap xs) =
    segs start len =<< xs

  segs start len (UnpackSeqMap w)
    | start == 0 && wordLen sym w == len = pure [Right w]
    | otherwise =
        do w' <- takeWord sym len =<< dropWord sym start w
           return [Right w']

  segs start len (DropSeqMap front xs) =
    segs (start+front) len xs

  segs start len (UpdateSeqMap upds vs) =
    do ws <- mapM go (computeSegments start (start+len-1) upds)
       pure (concat ws)
     where
     go (Left (s,e)) = segs s (e+1-s) vs
     go (Right a)    = pure [Left (fromVBit <$> a)]

  segs start len (ConcatSeqMap front xs ys)
    | start+len <= front = segs start len xs
    | front <= start     = segs (start - front) len ys
    | otherwise =
       do w1 <- segs start (front-start) xs
          w2 <- segs 0 (start+len-front) ys
          pure (w1++w2)

  segs start len (JoinSeqMap each xss) =
    do xss' <- sequence [ fromVSeq <$> lookupSeqMap sym q xss | q <- [ startq .. endq ] ]
       case xss' of
         []  -> evalPanic "getWordSegments" ["invalid join", show start, show len, show each]
         [x] -> segs startr (endr+1-startr) x
         (hd:x:xs) ->
           do h <- segs startr (each-startr) hd
              tl <- go x xs
              pure (h++tl)

   where
    end = start+len-1
    (startq, startr) = start `divMod` each
    (endq, endr)     = end   `divMod` each

    go x [] = segs 0 (endr+1) x
    go x (x':xs) =
       do h <- segs 0 each x
          tl <- go x' xs
          pure (h++tl)

-- | Pack a sequence map into a word value, taking @len@ bits.
packSeqMap :: Backend sym => sym -> Integer -> SeqMap sym -> SEval sym (SWord sym)
packSeqMap sym len0 v0
   | len0 <= 0 = wordLit sym 0 0
   | otherwise = pack 0 len0 v0
  where
  --   Invariant 0 < len, so at least 1 bit must be taken.
  pack start _len VoidSeqMap = invalidIndex sym start

  pack start len (GenerateSeqMap f) =
    do bs <- traverse (\i -> fromVBit <$> f i) (genericTake len [ start .. ])
       packWord sym bs

  pack start len (MemoSeqMap cache vs) =
    do bs <- traverse (\i -> fromVBit <$> evalMemo sym i cache vs) (genericTake len [ start .. ])
       packWord sym bs

  pack start len (DelaySeqMap xs) =
    pack start len =<< xs

  pack start len (UnpackSeqMap w)
    | start == 0 && wordLen sym w == len = pure w
    | otherwise = takeWord sym len =<< dropWord sym start w

  pack start len (UpdateSeqMap upds vs) =
    do ws <- mapM go (computeSegments start (start+len-1) upds)
       case ws of
         [] -> panic "packSeqMap" ["empty segment list!", show start, show len]
         (w:ws') -> foldM (joinWord sym) w ws'
   where
   go (Left (s,e)) = pack s (e+1-s) vs
   go (Right a)    = do b <- fromVBit <$> a
                        packWord sym [b]

  pack start len (DropSeqMap front xs) =
    pack (start+front) len xs

  pack start len (ConcatSeqMap front xs ys)
    | start+len <= front = pack start len xs
    | front <= start     = pack (start - front) len ys
    | otherwise =
       do w1 <- pack start (front-start) xs
          w2 <- pack 0 (start+len-front) ys
          joinWord sym w1 w2

  pack start len (JoinSeqMap each xss) =
    do xss' <- sequence [ fromVSeq <$> lookupSeqMap sym q xss | q <- [ startq .. endq ] ]
       case xss' of
         []   -> evalPanic "packSeqMap" ["invalid join", show start, show end, show each]
         [x] -> pack startr (endr+1-startr) x
         (hd:x:xs) ->
           do h <- pack startr (each-startr) hd
              go h x xs

   where
    end = start+len-1
    (startq, startr) = start `divMod` each
    (endq, endr)     = end   `divMod` each

    go h x [] = joinWord sym h =<< pack 0 (endr+1) x
    go h x (x':xs) =
       do h' <- joinWord sym h =<< pack 0 each x
          go h' x' xs


-- | Reverse the order of a finite sequence map
reverseSeqMap ::
  Backend sym =>
  sym ->
  Integer {- ^ Size of the sequence map -} ->
  SeqMap sym ->
  SEval sym (SeqMap sym)
reverseSeqMap sym n vs = generateSeqMap sym (\i -> lookupSeqMap sym (n - 1 - i) vs)

-- | Given a number @n@ and a sequence map, return two new sequence maps:
--   the first containing the values from @[0..n-1]@ and the next containing
--   the values from @n@ onward.
splitSeqMap :: Backend sym =>
  sym -> Integer -> SeqMap sym -> (SEval sym (SeqMap sym), SEval sym (SeqMap sym))
splitSeqMap sym n xs = (pure xs, dropSeqMap sym n xs)

-- | Given a sequence map, return a new sequence map that is memoized using
--   a finite map memo table.
memoMap :: Backend sym => sym -> SeqMap sym -> SEval sym (SeqMap sym)
memoMap _sym vs@(MemoSeqMap _ _) = pure vs
memoMap _sym vs = do
  cache <- liftIO $ newIORef $ Map.empty
  pure $ MemoSeqMap cache vs

-- | Apply the given evaluation function pointwise to the two given
--   sequence maps.
zipSeqMap ::
  Backend sym =>
  sym ->
  (SEval sym (GenValue sym) -> SEval sym (GenValue sym) -> SEval sym (GenValue sym)) ->
  SeqMap sym ->
  SeqMap sym ->
  SEval sym (SeqMap sym)
zipSeqMap sym f x y =
  memoMap sym =<< (generateSeqMap sym $ \i -> f (lookupSeqMap sym i x) (lookupSeqMap sym i y))


zipSegments ::
  Backend sym =>
  sym ->
  (SEval sym (SBit sym) -> SEval sym (SBit sym) -> SEval sym (SBit sym)) ->
  (SWord sym -> SWord sym -> SEval sym (SWord sym)) ->
  [Either (SEval sym (SBit sym)) (SWord sym)] ->
  [Either (SEval sym (SBit sym)) (SWord sym)] ->
  SEval sym (SeqMap sym)
zipSegments sym bitop wordop = go 0 []
  where
  concatBts _     [] z = pure (UnpackSeqMap z)
  concatBts btsn bts z =
    do btsm <- finiteSeqMap sym (reverse bts)
       concatSeqMap sym btsn btsm (UnpackSeqMap z)

  go !btsn bts (Right wx : xs) ys
    | wordLen sym wx == 0 = go btsn bts xs ys

  go btsn bts xs (Right wy : ys)
    | wordLen sym wy == 0 = go btsn bts xs ys

  go btsn bts (Right wx : xs) (Right wy : ys)

    | wordLen sym wx < wordLen sym wy
    = do (wy1,wy2) <- splitWord sym (wordLen sym wx) (wordLen sym wy - wordLen sym wx) wy
         z <- concatBts btsn bts =<< wordop wx wy1
         concatSeqMap sym (btsn + wordLen sym wx) z =<< go 0 [] xs (Right wy2 : ys)

    | wordLen sym wx > wordLen sym wy
    = do (wx1,wx2) <- splitWord sym (wordLen sym wy) (wordLen sym wx - wordLen sym wy) wx
         z <- concatBts btsn bts =<< wordop wx1 wy
         concatSeqMap sym (btsn + wordLen sym wy) z =<< go 0 [] (Right wx2 : xs) ys

    | otherwise -- wordLen sym wx == wordLen sym wy
    = do z <- concatBts btsn bts =<< wordop wx wy
         concatSeqMap sym (btsn + wordLen sym wx) z =<< go 0 [] xs ys

  go btsn bts (Left bx : xs) (Right wy : ys) =
   do let bz = VBit <$> bitop bx (wordBit sym wy 0)
      wy' <- dropWord sym 1 wy
      go (btsn+1) (bz : bts) xs (Right wy' : ys)

  go btsn bts (Right wx : xs) (Left by : ys) =
   do let bz = VBit <$> bitop (wordBit sym wx 0) by
      wx' <- dropWord sym 1 wx
      go (btsn+1) (bz : bts) (Right wx' : xs) ys

  go btsn bts (Left bx : xs) (Left by : ys) =
   do let bz = VBit <$> bitop bx by
      go (btsn+1) (bz : bts) xs ys

  go _ bts [] [] = finiteSeqMap sym (reverse bts)

  go _ _ _ _ = evalPanic "zipSegments" ["segment mismatch!"]

mapSegments ::
  Backend sym =>
  sym ->
  (SEval sym (SBit sym) -> SEval sym (SBit sym)) ->
  (SWord sym -> SEval sym (SWord sym)) ->
  [Either (SEval sym (SBit sym)) (SWord sym)] ->
  SEval sym (SeqMap sym)
mapSegments sym bitop wordop = go 0 []
  where
  concatBts _     [] z = pure (UnpackSeqMap z)
  concatBts btsn bts z =
    do btsm <- finiteSeqMap sym (reverse bts)
       concatSeqMap sym btsn btsm (UnpackSeqMap z)

  go !btsn bts (Right w : xs)
    | wordLen sym w == 0 = go btsn bts xs

  go btsn bts (Right w : xs) =
    do w' <- wordop w
       z  <- concatBts btsn bts w'
       concatSeqMap sym (btsn + wordLen sym w) z =<< go 0 [] xs

  go btsn bts (Left b : xs) =
    do let bz = VBit <$> bitop b
       go (btsn+1) (bz:bts) xs

  go _btsn bts [] = finiteSeqMap sym (reverse bts)

bitwiseWordUnOp ::
  Backend sym =>
  sym ->
  Integer ->
  (SEval sym (SBit sym) -> SEval sym (SBit sym)) ->
  (SWord sym -> SEval sym (SWord sym)) ->
  SeqMap sym -> SEval sym (SeqMap sym)
bitwiseWordUnOp sym len bitop wordop xs
  | len <= 0 = pure VoidSeqMap
  | otherwise =
     do xsegs <- getWordSegments sym len xs
        mapSegments sym bitop wordop xsegs

bitwiseWordBinOp ::
  Backend sym =>
  sym ->
  Integer ->
  (SEval sym (SBit sym) -> SEval sym (SBit sym) -> SEval sym (SBit sym)) ->
  (SWord sym -> SWord sym -> SEval sym (SWord sym)) ->
  SeqMap sym -> SeqMap sym -> SEval sym (SeqMap sym)
bitwiseWordBinOp sym len bitop wordop xs ys
  | len <= 0 = pure VoidSeqMap
  | otherwise =
     do xsegs <- getWordSegments sym len xs
        ysegs <- getWordSegments sym len ys
        zipSegments sym bitop wordop xsegs ysegs

-- | Apply the given function to each value in the given sequence map
mapSeqMap ::
  Backend sym =>
  sym ->
  (SEval sym (GenValue sym) -> SEval sym (GenValue sym)) ->
  SeqMap sym -> SEval sym (SeqMap sym)
mapSeqMap sym f x =
  memoMap sym =<< (generateSeqMap sym $ \i -> f (lookupSeqMap sym i x))

actualizeSeqMap :: forall sym. Backend sym => sym -> Integer -> SeqMap sym -> SEval sym (SeqMap sym)
actualizeSeqMap sym len0 xs0
  | len0 <= 0 = pure VoidSeqMap
  | otherwise = actualize 0 len0 xs0
 where
 -- Invariant, len > 0
 actualize :: Integer -> Integer -> SeqMap sym -> SEval sym (SeqMap sym)
 actualize start _len VoidSeqMap = invalidIndex sym start
 actualize start len (UnpackSeqMap w)
    | start == 0 && wordLen sym w == len = pure (UnpackSeqMap w)
    | otherwise = UnpackSeqMap <$> (takeWord sym len =<< dropWord sym start w)
 actualize start len (JoinSeqMap each xs) =
   do xs' <- actualize (start*each) (len*each) xs
      joinSeqMap sym each xs'
 actualize start len (ConcatSeqMap front xs ys)
   | start+len <= front = actualize start len xs
   | front <= start     = actualize (start - front) len ys
   | otherwise =
       do xs' <- actualize start (front-start) xs
          ys' <- actualize 0 (start+len-front) ys
          concatSeqMap sym (front-start) xs' ys'
 actualize start len (DelaySeqMap xs) =
   actualize start len =<< xs
 actualize start len (DropSeqMap toDrop xs) =
   actualize (start+toDrop) len xs
 actualize start len xs = finiteSeqMap' <$>
     mapM (\i -> pure <$> (forceValue sym =<< lookupSeqMap sym i xs))
          (genericTake len [ start .. ])

-- | Generic value type, parameterized by bit and word types.
--
--   NOTE: we maintain an important invariant regarding sequence types.
--   'VSeq' must never be used for finite sequences of bits.
--   Always use the 'VWord' constructor instead!  Infinite sequences of bits
--   are handled by the 'VStream' constructor, just as for other types.
data GenValue sym
  = VBit !(SBit sym)                           -- ^ @ Bit    @
  | VInteger !(SInteger sym)                   -- ^ @ Integer @ or @ Z n @
  | VRational !(SRational sym)                 -- ^ @ Rational @
  | VFloat !(SFloat sym)
  | VRecord !(RecordMap Ident (SEval sym (GenValue sym))) -- ^ @ { .. } @
  | VTuple ![SEval sym (GenValue sym)]              -- ^ @ ( .. ) @
  | VSeq !Nat' !TValue !(SeqMap sym)                   -- ^ @ [n]a @
  | VFun !(SEval sym (GenValue sym) -> SEval sym (GenValue sym)) -- ^ functions
  | VPoly !(TValue -> SEval sym (GenValue sym))   -- ^ polymorphic values (kind *)
  | VNumPoly !(Nat' -> SEval sym (GenValue sym))  -- ^ polymorphic values (kind #)
 deriving Generic

-- | Force the evaluation of a value
forceValue :: Backend sym => sym -> GenValue sym -> SEval sym (GenValue sym)
forceValue sym v = case v of
  VBit b      -> seq b (pure v)
  VInteger i  -> seq i (pure v)
  VRational q -> seq q (pure v)
  VFloat f    -> seq f (pure v)
  VRecord fs  -> VRecord <$> traverse (pure <$> (forceValue sym =<<)) fs
  VTuple xs   -> VTuple <$> traverse (pure <$> (forceValue sym =<<)) xs
  VSeq (Nat n) a xs -> VSeq (Nat n) a <$> actualizeSeqMap sym n xs
  VSeq Inf _ _  -> pure v
  VFun _        -> pure v
  VPoly _       -> pure v
  VNumPoly _    -> pure v

instance Backend sym => Show (GenValue sym) where
  show v = case v of
    VRecord fs -> "record:" ++ show (displayOrder fs)
    VTuple xs  -> "tuple:" ++ show (length xs)
    VBit _     -> "bit"
    VInteger _ -> "integer"
    VRational _ -> "rational"
    VFloat _   -> "float"
    VSeq (Nat n) _ xs -> "seq:" ++ show n ++ " " ++ show xs
    VSeq Inf _ xs     -> "stream " ++ show xs
    VFun _     -> "fun"
    VPoly _    -> "poly"
    VNumPoly _ -> "numpoly"


-- Pretty Printing -------------------------------------------------------------

ppValue :: forall sym.
  Backend sym =>
  sym ->
  PPOpts ->
  GenValue sym ->
  SEval sym Doc
ppValue sym opts = loop
  where
  loop :: GenValue sym -> SEval sym Doc
  loop val = case val of
    VBit b      -> return $ ppBit sym b
    VInteger i  -> return $ ppInteger sym opts i
    VRational q -> return $ ppRational sym opts q
    VFloat i    -> return $ ppFloat sym opts i

    VRecord fs ->
       do fs' <- traverseRecordMap (\_ v -> loop =<< v) fs
          return $ braces (sep (punctuate comma (map ppField (displayFields fs'))))
      where
      ppField (f,r) = pp f <+> char '=' <+> r

    VTuple vals ->
       do vals' <- traverse (\ v -> loop =<< v) vals
          return $ parens (sep (punctuate comma vals'))

    -- word printing
    VSeq (Nat w) TVBit vals ->
      ppWord sym opts <$> packSeqMap sym w vals

    -- string printing
    VSeq (Nat n) (TVSeq w TVBit) vals
      | asciiMode opts w && w > 0 -> ppString n w vals

    -- finite sequence
    VSeq (Nat n) _ vals ->
       do vals' <- traverse (\v -> loop =<< v) $ enumerateSeqMap sym n vals
          return $ brackets $ fsep $ punctuate comma vals'

    -- infinite sequence
    VSeq Inf _ vals ->
       do vals' <- traverse (\v -> loop =<< v) $ enumerateSeqMap sym (toInteger (useInfLength opts)) vals
          return $ brackets $ fsep
                $ punctuate comma
                ( vals' ++ [text "..."] )

    VFun _            -> return $ text "<function>"
    VPoly _           -> return $ text "<polymorphic value>"
    VNumPoly _        -> return $ text "<polymorphic value>"

  ppString :: Integer -> Integer -> SeqMap sym -> SEval sym Doc
  ppString n w vals
    | n <= 0 = pure (text (show ""))
    | otherwise =
        do ws <- traverse (packSeqMap sym w . fromVSeq =<<) (enumerateSeqMap sym n vals)
           case traverse (wordAsChar sym) ws of
             Just str -> return $ text (show str)
             _ -> return $ brackets (fsep (punctuate comma $ map (ppWord sym opts) ws))


asciiMode :: PPOpts -> Integer -> Bool
asciiMode opts width = useAscii opts && (width == 7 || width == 8)


-- Value Constructors ----------------------------------------------------------

-- | Create a packed word of n bits.
word :: Backend sym => sym -> Integer -> Integer -> SEval sym (GenValue sym)
word sym n i
  | n >= Arch.maxBigIntWidth = wordTooWide n
  | otherwise                = VSeq (Nat n) TVBit . UnpackSeqMap <$> wordLit sym n i

lam :: (SEval sym (GenValue sym) -> SEval sym (GenValue sym)) -> GenValue sym
lam  = VFun

-- | Functions that assume word inputs
wlam :: Backend sym => sym -> (SWord sym -> SEval sym (GenValue sym)) -> GenValue sym
wlam sym f =
  VFun (\arg -> arg >>= \case
    VSeq (Nat w) _ v -> f =<< packSeqMap sym w v
    _ -> panic "wlam" ["Expected word value"]
  )

-- | Functions that assume floating point inputs
flam :: Backend sym =>
        (SFloat sym -> SEval sym (GenValue sym)) -> GenValue sym
flam f = VFun (\arg -> arg >>= f . fromVFloat)


-- | A type lambda that expects a 'Type'.
tlam :: Backend sym => (TValue -> GenValue sym) -> GenValue sym
tlam f = VPoly (return . f)

-- | A type lambda that expects a 'Type' of kind #.
nlam :: Backend sym => (Nat' -> GenValue sym) -> GenValue sym
nlam f = VNumPoly (return . f)

-- | A type lambda that expects a finite numeric type.
ilam :: Backend sym => (Integer -> GenValue sym) -> GenValue sym
ilam f = nlam (\n -> case n of
                       Nat i -> f i
                       Inf   -> panic "ilam" [ "Unexpected `inf`" ])

-- Value Destructors -----------------------------------------------------------

-- | Extract a bit value.
fromVBit :: GenValue sym -> SBit sym
fromVBit val = case val of
  VBit b -> b
  _      -> evalPanic "fromVBit" ["not a Bit"]

-- | Extract an integer value.
fromVInteger :: GenValue sym -> SInteger sym
fromVInteger val = case val of
  VInteger i -> i
  _      -> evalPanic "fromVInteger" ["not an Integer"]

-- | Extract a rational value.
fromVRational :: GenValue sym -> SRational sym
fromVRational val = case val of
  VRational q -> q
  _      -> evalPanic "fromVRational" ["not a Rational"]

-- | Extract a finite sequence value.
fromVSeq :: GenValue sym -> SeqMap sym
fromVSeq val = case val of
  VSeq _ _ vs -> vs
  _           -> evalPanic "fromVSeq" ["not a sequence"]

asIndex :: Backend sym =>
  sym ->
  String ->
  TValue ->
  GenValue sym ->
  SEval sym (Either (SInteger sym) (SWord sym))
asIndex _sym _msg TVInteger (VInteger i) = pure (Left i)
asIndex sym  _msg (TVSeq w TVBit) (VSeq _ _ xs) = Right <$> packSeqMap sym w xs
asIndex _sym msg tv _ = evalPanic "asIndex" ["not an index value", show tv, msg]

-- | If the given list of values are all fully-evaluated thunks
--   containing bits, return a packed word built from the same bits.
--   However, if any value is not a fully-evaluated bit, return 'Nothing'.
tryFromBits :: Backend sym => sym -> [SEval sym (GenValue sym)] -> SEval sym (Maybe (SWord sym))
tryFromBits sym = go id
  where
  go f [] = Just <$> (packWord sym (f []))
  go f (v : vs) =
    sMaybeReady sym v >>= \case
      Just b  -> go (f . ((fromVBit b):)) vs
      Nothing -> pure Nothing

-- | Extract a function from a value.
fromVFun :: GenValue sym -> (SEval sym (GenValue sym) -> SEval sym (GenValue sym))
fromVFun val = case val of
  VFun f -> f
  _      -> evalPanic "fromVFun" ["not a function"]

-- | Extract a polymorphic function from a value.
fromVPoly :: GenValue sym -> (TValue -> SEval sym (GenValue sym))
fromVPoly val = case val of
  VPoly f -> f
  _       -> evalPanic "fromVPoly" ["not a polymorphic value"]

-- | Extract a polymorphic function from a value.
fromVNumPoly :: GenValue sym -> (Nat' -> SEval sym (GenValue sym))
fromVNumPoly val = case val of
  VNumPoly f -> f
  _          -> evalPanic "fromVNumPoly" ["not a polymorphic value"]

-- | Extract a tuple from a value.
fromVTuple :: GenValue sym -> [SEval sym (GenValue sym)]
fromVTuple val = case val of
  VTuple vs -> vs
  _         -> evalPanic "fromVTuple" ["not a tuple"]

-- | Extract a record from a value.
fromVRecord :: GenValue sym -> RecordMap Ident (SEval sym (GenValue sym))
fromVRecord val = case val of
  VRecord fs -> fs
  _          -> evalPanic "fromVRecord" ["not a record"]

fromVFloat :: GenValue sym -> SFloat sym
fromVFloat val =
  case val of
    VFloat x -> x
    _        -> evalPanic "fromVFloat" ["not a Float"]

-- | Lookup a field in a record.
lookupRecord :: Ident -> GenValue sym -> SEval sym (GenValue sym)
lookupRecord f val =
  case lookupField f (fromVRecord val) of
    Just x  -> x
    Nothing -> evalPanic "lookupRecord" ["malformed record"]


-- Merge and if/then/else

{-# INLINE iteValue #-}
iteValue :: Backend sym =>
  sym ->
  TValue ->
  SBit sym ->
  SEval sym (GenValue sym) ->
  SEval sym (GenValue sym) ->
  SEval sym (GenValue sym)
iteValue sym tv b x y
  | Just True  <- bitAsLit sym b = x
  | Just False <- bitAsLit sym b = y
  | otherwise = mergeValue' sym tv b x y

{-# INLINE mergeValue' #-}
mergeValue' :: Backend sym =>
  sym ->
  TValue ->
  SBit sym ->
  SEval sym (GenValue sym) ->
  SEval sym (GenValue sym) ->
  SEval sym (GenValue sym)
mergeValue' sym tv = mergeEval sym (mergeValue sym tv)

mergeValue :: Backend sym =>
  sym ->
  TValue ->
  SBit sym ->
  GenValue sym ->
  GenValue sym ->
  SEval sym (GenValue sym)
mergeValue sym tv c v1 v2 =
  case (tv, v1, v2) of
    (_, VBit b1     , VBit b2     ) -> VBit <$> iteBit sym c b1 b2
    (_, VInteger i1 , VInteger i2 ) -> VInteger <$> iteInteger sym c i1 i2
    (_, VRational q1, VRational q2) -> VRational <$> iteRational sym c q1 q2

    (TVRec tfs, VRecord fs1, VRecord fs2) ->
      do let getTy lbl = case lookupField lbl tfs of
                           Just ty -> ty
                           Nothing -> panic "mergeValue" ["Missing field", show lbl]
         let res = zipRecords (\lbl -> mergeValue' sym (getTy lbl) c) fs1 fs2
         case res of
           Left f -> panic "Cryptol.Eval.Generic" [ "mergeValue: incompatible record values", show f ]
           Right r -> pure (VRecord r)

    (TVTuple ts, VTuple vs1, VTuple vs2)
       | length ts == length vs1 && length vs1 == length vs2  ->
         pure $ VTuple $ zipWith3 (\t -> mergeValue' sym t c) ts vs1 vs2

    (TVSeq n tp, VSeq n1 _ vs1 , VSeq n2 _ vs2)
       | Nat n == n1 && n1 == n2 -> VSeq n1 tp <$> mergeSeqMap sym (Nat n) tp c vs1 vs2

    (TVStream tp, VSeq Inf _ vs1, VSeq Inf _ vs2 ) -> VSeq Inf tp <$> mergeSeqMap sym Inf tp c vs1 vs2


    (TVFun _ tp, VFun f1, VFun f2) -> pure $ VFun $ \x -> mergeValue' sym tp c (f1 x) (f2 x)

    (tp, _, _) -> panic "Cryptol.Eval.Generic"
                             [ "mergeValue: incompatible values", "Expected type:" ++ show tp ]

{-# INLINE mergeSeqMap #-}
mergeSeqMap :: Backend sym =>
  sym ->
  Nat' ->
  TValue {- element type -} ->
  SBit sym ->
  SeqMap sym ->
  SeqMap sym ->
  SEval sym (SeqMap sym)

-- special case for [n]Bit
mergeSeqMap sym (Nat n) TVBit c x y =
  do xs <- bitwiseWordBinOp sym n (mergeEval sym (iteBit sym) c) (iteWord sym c) x y
     return xs

mergeSeqMap sym _ tv c x y =
  memoMap sym =<< (generateSeqMap sym $ \i ->
    mergeValue' sym tv c (lookupSeqMap sym i x) (lookupSeqMap sym i y))
