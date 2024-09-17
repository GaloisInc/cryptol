-- |
-- Module      :  Cryptol.Backend.WordValue
-- Copyright   :  (c) 2013-2021 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE BangPatterns #-}
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

module Cryptol.Backend.WordValue
  ( -- * WordValue
    WordValue
  , wordVal
  , wordValWidth
  , bitmapWordVal
  , asWordList
  , asWordVal
  , asBitsMap
  , joinWordVal
  , takeWordVal
  , dropWordVal
  , extractWordVal
  , wordValLogicOp
  , wordValUnaryOp
  , assertWordValueInBounds
  , enumerateWordValue
  , enumerateWordValueRev
  , enumerateIndexSegments
  , wordValueSize
  , indexWordValue
  , updateWordValue
  , delayWordValue
  , joinWords
  , shiftSeqByWord
  , shiftWordByInteger
  , shiftWordByWord
  , wordValAsLit
  , reverseWordVal
  , forceWordValue
  , wordValueEqualsInteger
  , updateWordByWord

  , mergeWord
  , mergeWord'
  ) where

import Control.Monad (unless)
import Data.Bits
import GHC.Generics (Generic)

import Cryptol.Backend
import Cryptol.Backend.Concrete (Concrete(..))
import Cryptol.Backend.Monad (EvalError(..))
import Cryptol.Backend.SeqMap

import Cryptol.TypeCheck.Solver.InfNat(widthInteger, Nat'(..))

-- | Force the evaluation of a word value
forceWordValue :: Backend sym => WordValue sym -> SEval sym ()
forceWordValue (WordVal w)  = seq w (return ())
forceWordValue (ThunkWordVal _ m)  = forceWordValue =<< m
forceWordValue (BitmapVal _n packed _) = do w <- packed; seq w (return ())

-- | An arbitrarily-chosen number of elements where we switch from a dense
--   sequence representation of bit-level words to 'SeqMap' representation.
largeBitSize :: Integer
largeBitSize = bit 32

-- | For efficiency reasons, we handle finite sequences of bits as special cases
--   in the evaluator.  In cases where we know it is safe to do so, we prefer to
--   used a "packed word" representation of bit sequences.  This allows us to rely
--   directly on Integer types (in the concrete evaluator) and SBV's Word types (in
--   the symbolic simulator).
--
--   However, if we cannot be sure all the bits of the sequence
--   will eventually be forced, we must instead rely on an explicit sequence of bits
--   representation.
data WordValue sym
  = ThunkWordVal Integer !(SEval sym (WordValue sym))
  | WordVal !(SWord sym)                      -- ^ Packed word representation for bit sequences.
  | BitmapVal
       !Integer -- ^ Length of the word
       !(SEval sym (SWord sym)) -- ^ Thunk for packing the word
       !(SeqMap sym (SBit sym)) -- ^
 deriving (Generic)

wordValWidth :: forall sym. Backend sym => WordValue sym -> Integer
wordValWidth val =
  case val of
    ThunkWordVal n _ -> n
    WordVal sv -> wordLen' (Nothing :: Maybe sym) sv
    BitmapVal n _ _ -> n
{-# INLINE wordValWidth #-}

wordVal :: SWord sym -> WordValue sym
wordVal = WordVal

packBitmap :: Backend sym => sym -> Integer -> SeqMap sym (SBit sym) -> SEval sym (SWord sym)
packBitmap sym sz bs = packWord sym =<< sequence (enumerateSeqMap sz bs)

unpackBitmap :: Backend sym => sym -> SWord sym -> SeqMap sym (SBit sym)
unpackBitmap sym w = indexSeqMap $ \i -> wordBit sym w i

bitmapWordVal :: Backend sym => sym -> Integer -> SeqMap sym (SBit sym) -> SEval sym (WordValue sym)
bitmapWordVal sym sz bs =
  do packed <- sDelay sym (packBitmap sym sz bs)
     pure (BitmapVal sz packed bs)

{-# INLINE joinWordVal #-}
joinWordVal :: Backend sym => sym -> WordValue sym -> WordValue sym -> SEval sym (WordValue sym)
joinWordVal sym wv1 wv2 =
  let fallback = fallbackWordJoin sym wv1 wv2 in
  case (wv1, wv2) of
    (WordVal w1, WordVal w2) ->
      WordVal <$> joinWord sym w1 w2

    (ThunkWordVal _ m1, _) ->
      isReady sym m1 >>= \case
        Just x -> joinWordVal sym x wv2
        Nothing -> fallback

    (_,ThunkWordVal _ m2) ->
      isReady sym m2 >>= \case
        Just x   -> joinWordVal sym wv1 x
        Nothing  -> fallback

    (WordVal w1, BitmapVal _ packed2 _) ->
      isReady sym packed2 >>= \case
        Just w2 -> WordVal <$> joinWord sym w1 w2
        Nothing  -> fallback

    (BitmapVal _ packed1 _, WordVal w2) ->
      isReady sym packed1 >>= \case
        Just w1 -> WordVal <$> joinWord sym w1 w2
        Nothing -> fallback

    (BitmapVal _ packed1 _, BitmapVal _ packed2 _) ->
      do r1 <- isReady sym packed1
         r2 <- isReady sym packed2
         case (r1,r2) of
           (Just w1, Just w2) -> WordVal <$> joinWord sym w1 w2
           _ -> fallback

{-# INLINE fallbackWordJoin #-}
fallbackWordJoin :: Backend sym => sym -> WordValue sym -> WordValue sym -> SEval sym (WordValue sym)
fallbackWordJoin sym w1 w2 =
  do let n1 = wordValueSize sym w1
     let n2 = wordValueSize sym w2
     let len = n1 + n2
     packed <- sDelay sym
                 (do a <- asWordVal sym w1
                     b <- asWordVal sym w2
                     joinWord sym a b)
     let bs = concatSeqMap n1 (asBitsMap sym w1) (asBitsMap sym w2)
     pure (BitmapVal len packed bs)


{-# INLINE takeWordVal #-}
takeWordVal ::
  Backend sym =>
  sym ->
  Integer ->
  Integer ->
  WordValue sym ->
  SEval sym (WordValue sym)
takeWordVal sym leftWidth rigthWidth (WordVal w) =
  do (lw, _rw) <- splitWord sym leftWidth rigthWidth w
     pure (WordVal lw)

takeWordVal sym leftWidth rightWidth (ThunkWordVal _ m) =
  isReady sym m >>= \case
    Just w -> takeWordVal sym leftWidth rightWidth w
    Nothing ->
      do m' <- sDelay sym (takeWordVal sym leftWidth rightWidth =<< m)
         return (ThunkWordVal leftWidth m')

takeWordVal sym leftWidth rightWidth (BitmapVal _n packed xs) =
  isReady sym packed >>= \case
    Just w -> do (lw, _rw) <- splitWord sym leftWidth rightWidth w
                 pure (WordVal lw)
    Nothing -> bitmapWordVal sym leftWidth xs

{-# INLINE dropWordVal #-}
dropWordVal ::
  Backend sym =>
  sym ->
  Integer ->
  Integer ->
  WordValue sym ->
  SEval sym (WordValue sym)
dropWordVal sym leftWidth rigthWidth (WordVal w) =
  do (_lw, rw) <- splitWord sym leftWidth rigthWidth w
     pure (WordVal rw)

dropWordVal sym leftWidth rightWidth (ThunkWordVal _ m) =
  isReady sym m >>= \case
    Just w -> dropWordVal sym leftWidth rightWidth w
    Nothing ->
      do m' <- sDelay sym (dropWordVal sym leftWidth rightWidth =<< m)
         return (ThunkWordVal rightWidth m')

dropWordVal sym leftWidth rightWidth (BitmapVal _n packed xs) =
  isReady sym packed >>= \case
    Just w -> do (_lw, rw) <- splitWord sym leftWidth rightWidth w
                 pure (WordVal rw)
    Nothing ->
      do let rxs = dropSeqMap leftWidth xs
         bitmapWordVal sym rightWidth rxs

{-# INLINE extractWordVal #-}

-- | Extract a subsequence of bits from a @WordValue@.
--   The first integer argument is the number of bits in the
--   resulting word.  The second integer argument is the
--   number of less-significant digits to discard.  Stated another
--   way, the operation `extractWordVal n i w` is equivalent to
--   first shifting `w` right by `i` bits, and then truncating to
--   `n` bits.
extractWordVal ::
  Backend sym =>
  sym ->
  Integer ->
  Integer ->
  WordValue sym ->
  SEval sym (WordValue sym)
extractWordVal sym len start (WordVal w) =
   WordVal <$> extractWord sym len start w
extractWordVal sym len start (ThunkWordVal _n m) =
  isReady sym m >>= \case
    Just w -> extractWordVal sym len start w
    Nothing ->
      do m' <- sDelay sym (extractWordVal sym len start =<< m)
         pure (ThunkWordVal len m')
extractWordVal sym len start (BitmapVal n packed xs) =
  isReady sym packed >>= \case
    Just w -> WordVal <$> extractWord sym len start w
    Nothing ->
      do let xs' = dropSeqMap (n - start - len) xs
         bitmapWordVal sym len xs'

{-# INLINE wordValLogicOp #-}

wordValLogicOp ::
  Backend sym =>
  sym ->
  (SBit sym -> SBit sym -> SEval sym (SBit sym)) ->
  (SWord sym -> SWord sym -> SEval sym (SWord sym)) ->
  WordValue sym ->
  WordValue sym ->
  SEval sym (WordValue sym)
wordValLogicOp _sym _ wop (WordVal w1) (WordVal w2) = WordVal <$> wop w1 w2

wordValLogicOp sym bop wop (WordVal w1) (BitmapVal n2 packed2 bs2) =
  isReady sym packed2 >>= \case
    Just w2 -> WordVal <$> wop w1 w2
    Nothing -> bitmapWordVal sym n2 =<< zipSeqMap sym bop (Nat n2) (unpackBitmap sym w1) bs2

wordValLogicOp sym bop wop (BitmapVal n1 packed1 bs1) (WordVal w2) =
  isReady sym packed1 >>= \case
    Just w1 -> WordVal <$> wop w1 w2
    Nothing -> bitmapWordVal sym n1 =<< zipSeqMap sym bop (Nat n1) bs1 (unpackBitmap sym w2)

wordValLogicOp sym bop wop (BitmapVal n1 packed1 bs1) (BitmapVal _n2 packed2 bs2) =
  do r1 <- isReady sym packed1
     r2 <- isReady sym packed2
     case (r1,r2) of
       (Just w1, Just w2) -> WordVal <$> wop w1 w2
       _ -> bitmapWordVal sym n1 =<< zipSeqMap sym bop (Nat n1) bs1 bs2

wordValLogicOp sym bop wop (ThunkWordVal _ m1) w2 =
  do w1 <- m1
     wordValLogicOp sym bop wop w1 w2

wordValLogicOp sym bop wop w1 (ThunkWordVal _ m2) =
  do w2 <- m2
     wordValLogicOp sym bop wop w1 w2

{-# INLINE wordValUnaryOp #-}
wordValUnaryOp ::
  Backend sym =>
  sym ->
  (SBit sym -> SEval sym (SBit sym)) ->
  (SWord sym -> SEval sym (SWord sym)) ->
  WordValue sym ->
  SEval sym (WordValue sym)
wordValUnaryOp _ _ wop (WordVal w)  = WordVal <$> wop w
wordValUnaryOp sym bop wop (ThunkWordVal _ m) = wordValUnaryOp sym bop wop =<< m
wordValUnaryOp sym bop wop (BitmapVal n packed xs) =
  isReady sym packed >>= \case
    Just w  -> WordVal <$> wop w
    Nothing -> bitmapWordVal sym n =<< mapSeqMap sym bop (Nat n) xs

{-# SPECIALIZE joinWords ::
  Concrete ->
  Integer ->
  Integer ->
  SeqMap Concrete (WordValue Concrete)->
  SEval Concrete (WordValue Concrete)
  #-}
joinWords :: forall sym.
  Backend sym =>
  sym ->
  Integer ->
  Integer ->
  SeqMap sym (WordValue sym) ->
  SEval sym (WordValue sym)

-- small enough to pack
joinWords sym nParts nEach xs | nParts * nEach < largeBitSize =
  do z <- wordLit sym 0 0
     loop (wordVal z) (enumerateSeqMap nParts xs)

 where
 loop :: WordValue sym -> [SEval sym (WordValue sym)] -> SEval sym (WordValue sym)
 loop !wv [] = pure wv
 loop !wv (w : ws) =
    do w'  <- delayWordValue sym nEach w
       wv' <- joinWordVal sym wv w'
       loop wv' ws

-- too large to pack
joinWords sym nParts nEach xs = bitmapWordVal sym (nParts * nEach) zs
  where
    zs = indexSeqMap $ \i ->
            do let (q,r) = divMod i nEach
               ys <- lookupSeqMap xs q
               indexWordValue sym ys r

reverseWordVal :: Backend sym => sym -> WordValue sym -> SEval sym (WordValue sym)
reverseWordVal sym w =
  let m = wordValueSize sym w in
  bitmapWordVal sym m <$> reverseSeqMap m $ asBitsMap sym w

wordValAsLit :: Backend sym => sym -> WordValue sym -> SEval sym (Maybe Integer)
wordValAsLit sym (WordVal w) = pure (snd <$> wordAsLit sym w)
wordValAsLit sym (ThunkWordVal _ m) =
  isReady sym m >>= \case
    Just v  -> wordValAsLit sym v
    Nothing -> pure Nothing
wordValAsLit sym (BitmapVal _ packed _) =
  isReady sym packed >>= \case
    Just w  -> pure (snd <$> wordAsLit sym w)
    Nothing -> pure Nothing

-- | Force a word value into packed word form
asWordVal :: Backend sym => sym -> WordValue sym -> SEval sym (SWord sym)
asWordVal _   (WordVal w)            = return w
asWordVal sym (ThunkWordVal _ m)     = asWordVal sym =<< m
asWordVal _   (BitmapVal _ packed _) = packed

wordValueEqualsInteger :: forall sym. Backend sym =>
  sym ->
  WordValue sym ->
  Integer ->
  SEval sym (SBit sym)
wordValueEqualsInteger sym wv i
  | wordValueSize sym wv < widthInteger i = return (bitLit sym False)
  | otherwise = loop wv

 where
   loop (ThunkWordVal _ m) = loop =<< m
   loop (WordVal w) = wordEq sym w =<< wordLit sym (wordLen sym w) i
   loop (BitmapVal n packed bs) =
     isReady sym packed >>= \case
       Just w  -> loop (WordVal w)
       Nothing -> bitsAre i =<< sequence (enumerateSeqMap n (reverseSeqMap n bs))

   -- NB little-endian sequence of bits
   bitsAre :: Integer -> [SBit sym] -> SEval sym (SBit sym)
   bitsAre !n [] = return (bitLit sym (n == 0))
   bitsAre !n (b:bs) =
     do pb  <- bitIs (testBit n 0) b
        pbs <- bitsAre (n `shiftR` 1) bs
        bitAnd sym pb pbs

   bitIs :: Bool -> SBit sym -> SEval sym (SBit sym)
   bitIs b x = if b then pure x else bitComplement sym x

asWordList :: forall sym. Backend sym => sym -> [WordValue sym] -> SEval sym (Maybe [SWord sym])
asWordList sym = loop id
 where
   loop :: ([SWord sym] -> [SWord sym]) -> [WordValue sym] -> SEval sym (Maybe [SWord sym])
   loop f [] = pure (Just (f []))
   loop f (WordVal x : vs) = loop (f . (x:)) vs
   loop f (ThunkWordVal _ m : vs) =
     isReady sym m >>= \case
       Just m' -> loop f (m' : vs)
       Nothing -> pure Nothing
   loop f (BitmapVal _ packed _ : vs) =
     isReady sym packed >>= \case
       Just x -> loop (f . (x:)) vs
       Nothing -> pure Nothing

-- | Force a word value into a sequence of bits
asBitsMap :: Backend sym => sym -> WordValue sym -> SeqMap sym (SBit sym)
asBitsMap _   (BitmapVal _ _ xs)  = xs
asBitsMap sym (WordVal w)         = indexSeqMap $ \i -> wordBit sym w i
asBitsMap sym (ThunkWordVal _ m)  =
  indexSeqMap $ \i ->
    do mp <- asBitsMap sym <$> (unwindThunks m)
       lookupSeqMap mp i

-- | Turn a word value into a sequence of bits, forcing each bit.
--   The sequence is returned in big-endian order.
enumerateWordValue :: Backend sym => sym -> WordValue sym -> SEval sym [SBit sym]
enumerateWordValue sym (WordVal w) = unpackWord sym w
enumerateWordValue sym (ThunkWordVal _ m) = enumerateWordValue sym =<< m
  -- TODO? used the packed value if it is ready?
enumerateWordValue _ (BitmapVal n _ xs) = sequence (enumerateSeqMap n xs)

-- | Turn a word value into a sequence of bits, forcing each bit.
--   The sequence is returned in reverse of the usual order, which is little-endian order.
enumerateWordValueRev :: Backend sym => sym -> WordValue sym -> SEval sym [SBit sym]
enumerateWordValueRev sym (WordVal w)  = reverse <$> unpackWord sym w
enumerateWordValueRev sym (ThunkWordVal _ m)  = enumerateWordValueRev sym =<< m
  -- TODO? used the packed value if it is ready?
enumerateWordValueRev _   (BitmapVal n _ xs) = sequence (enumerateSeqMap n (reverseSeqMap n xs))


enumerateIndexSegments :: Backend sym => sym -> WordValue sym -> SEval sym [IndexSegment sym]
enumerateIndexSegments _sym (WordVal w) = pure [WordIndexSegment w]
enumerateIndexSegments sym (ThunkWordVal _ m) = enumerateIndexSegments sym =<< m
enumerateIndexSegments sym (BitmapVal n packed xs) =
  isReady sym packed >>= \case
    Just w  -> pure [WordIndexSegment w]
    Nothing -> traverse (BitIndexSegment <$>) (enumerateSeqMap n xs)

{-# SPECIALIZE bitsValueLessThan ::
  Concrete ->
  Integer ->
  [SBit Concrete] ->
  Integer ->
  SEval Concrete (SBit Concrete)
  #-}
bitsValueLessThan ::
  Backend sym =>
  sym ->
  Integer {- ^ bit-width -} ->
  [SBit sym] {- ^ big-endian list of index bits -} ->
  Integer {- ^ Upper bound to test against -} ->
  SEval sym (SBit sym)
bitsValueLessThan sym _w [] _n = pure $ bitLit sym False
bitsValueLessThan sym w (b:bs) n
  | nbit =
      do notb <- bitComplement sym b
         bitOr sym notb =<< bitsValueLessThan sym (w-1) bs n
  | otherwise =
      do notb <- bitComplement sym b
         bitAnd sym notb =<< bitsValueLessThan sym (w-1) bs n
 where
 nbit = testBit n (fromInteger (w-1))


assertWordValueInBounds ::
  Backend sym => sym -> Integer -> WordValue sym -> SEval sym ()

-- Can't index out of bounds for a sequence that is
-- longer than the expressible index values
assertWordValueInBounds sym n idx
  | n >= 2^(wordValueSize sym idx)
  = return ()

assertWordValueInBounds sym n (WordVal idx)
  | Just (_w,i) <- wordAsLit sym idx
  = unless (i < n) (raiseError sym (InvalidIndex (Just i)))

-- If the index is a packed word, test that it
-- is less than the concrete value of n, which
-- fits into w bits because of the above test.
assertWordValueInBounds sym n (WordVal idx) =
  do n' <- wordLit sym (wordLen sym idx) n
     p <- wordLessThan sym idx n'
     assertSideCondition sym p (InvalidIndex Nothing)

-- Force thunks
assertWordValueInBounds sym n (ThunkWordVal _ m) =
  assertWordValueInBounds sym n =<< m

-- If the index is an unpacked word, force all the bits
-- and compute the unsigned less-than test directly.
assertWordValueInBounds sym n (BitmapVal sz packed bits) =
  isReady sym packed >>= \case
    Just w -> assertWordValueInBounds sym n (WordVal w)
    Nothing ->
      do bitsList <- sequence (enumerateSeqMap sz bits)
         p <- bitsValueLessThan sym sz bitsList n
         assertSideCondition sym p (InvalidIndex Nothing)

delayWordValue :: Backend sym => sym -> Integer -> SEval sym (WordValue sym) -> SEval sym (WordValue sym)
delayWordValue sym sz m =
  isReady sym m >>= \case
    Just w  -> pure w
    Nothing -> ThunkWordVal sz <$> sDelay sym (unwindThunks m)

-- If we are calling this, we know the spine of the word value has been
-- demanded, so we unwind any chains of `ThunkWordValue` that may have built up.
unwindThunks :: Backend sym => SEval sym (WordValue sym) -> SEval sym (WordValue sym)
unwindThunks m =
  m >>= \case
    ThunkWordVal _ m' -> unwindThunks m'
    x -> pure x

{-# INLINE shiftWordByInteger #-}
shiftWordByInteger ::
  Backend sym =>
  sym ->
  (SWord sym -> SWord sym -> SEval sym (SWord sym)) 
    {- ^ operation on word values -} ->
  (Integer -> Integer -> Maybe Integer)
    {- ^ reindexing operation -} ->
  WordValue sym {- ^ word value to shift -} ->
  SInteger sym {- ^ shift amount, assumed to be in range [0,len] -} ->
  SEval sym (WordValue sym)

shiftWordByInteger sym wop reindex x idx =
  case x of
    ThunkWordVal w wm ->
      isReady sym wm >>= \case
        Just x' -> shiftWordByInteger sym wop reindex x' idx
        Nothing ->
         do m' <- sDelay sym
                     (do x' <- wm
                         shiftWordByInteger sym wop reindex x' idx)
            return (ThunkWordVal w m')

    WordVal x' -> WordVal <$> (wop x' =<< wordFromInt sym (wordLen sym x') idx)

    BitmapVal n packed bs0 ->
      isReady sym packed >>= \case
        Just w -> shiftWordByInteger sym wop reindex (WordVal w) idx
        Nothing ->
          bitmapWordVal sym n =<<
            shiftSeqByInteger sym (iteBit sym) reindex (pure (bitLit sym False)) (Nat n) bs0 idx


{-# INLINE shiftWordByWord #-}
shiftWordByWord ::
  Backend sym =>
  sym ->
  (SWord sym -> SWord sym -> SEval sym (SWord sym))
    {- ^ operation on word values -} ->
  (Integer -> Integer -> Maybe Integer)
    {- ^ reindexing operation -} ->
  WordValue sym {- ^ value to shift -} ->
  WordValue sym {- ^ amount to shift -} ->
  SEval sym (WordValue sym)
shiftWordByWord sym wop reindex x idx =
  case x of
    ThunkWordVal w wm ->
      isReady sym wm >>= \case
        Just wm' -> shiftWordByWord sym wop reindex wm' idx
        Nothing ->
         do m' <- sDelay sym (do wm' <- wm
                                 shiftWordByWord sym wop reindex wm' idx)
            return (ThunkWordVal w m')

    WordVal x' -> WordVal <$> (wop x' =<< asWordVal sym idx)

    BitmapVal n packed bs0 ->
      isReady sym packed >>= \case
        Just w -> shiftWordByWord sym wop reindex (WordVal w) idx
        Nothing ->
          bitmapWordVal sym n =<<
            shiftSeqByWord sym (iteBit sym) reindex (pure (bitLit sym False)) (Nat n) bs0 idx


{-# INLINE updateWordByWord #-}
updateWordByWord ::
  Backend sym =>
  sym ->
  IndexDirection ->
  WordValue sym {- ^ value to update -} ->
  WordValue sym {- ^ index to update at -} ->
  SEval sym (SBit sym) {- ^ fresh bit -} ->
  SEval sym (WordValue sym)
updateWordByWord sym dir w0 idx bitval =
  wordValAsLit sym idx >>= \case
    Just j ->
      let sz = wordValueSize sym w0 in
      case dir of
        IndexForward  -> updateWordValue sym w0 j bitval
        IndexBackward -> updateWordValue sym w0 (sz - j - 1) bitval
    Nothing -> loop w0

 where
   loop (ThunkWordVal sz m) =
     isReady sym m >>= \case
       Just w' -> loop w'
       Nothing -> delayWordValue sym sz (loop =<< m)

   loop (BitmapVal sz packed bs) =
     isReady sym packed >>= \case
       Just w -> loop (WordVal w)
       Nothing ->
         case dir of
           IndexForward ->
             bitmapWordVal sym sz $ indexSeqMap $ \i ->
               do b <- wordValueEqualsInteger sym idx i
                  mergeEval sym (iteBit sym) b bitval (lookupSeqMap bs i)
           IndexBackward ->
             bitmapWordVal sym sz $ indexSeqMap $ \i ->
               do b <- wordValueEqualsInteger sym idx (sz - i - 1)
                  mergeEval sym (iteBit sym) b bitval (lookupSeqMap bs i)

   loop (WordVal wv) = WordVal <$>
      -- TODO, this is too strict in bit
      do let sz = wordLen sym wv
         b <- bitval
         msk <- case dir of
                  IndexForward ->
                    do highbit <- wordLit sym sz (bit (fromInteger (sz-1)))
                       wordShiftRight sym highbit =<< asWordVal sym idx
                  IndexBackward ->
                    do lowbit <- wordLit sym sz 1
                       wordShiftLeft sym lowbit =<< asWordVal sym idx
         case bitAsLit sym b of
           Just True  -> wordOr  sym wv msk
           Just False -> wordAnd sym wv =<< wordComplement sym msk
           Nothing ->
             do zro <- wordLit sym sz 0
                one <- wordComplement sym zro
                q   <- iteWord sym b one zro
                w'  <- wordAnd sym wv =<< wordComplement sym msk
                wordXor sym w' =<< wordAnd sym msk q


{-# INLINE shiftSeqByWord #-}
shiftSeqByWord  ::
  Backend sym =>
  sym ->
  (SBit sym -> a -> a -> SEval sym a)
     {- ^ if/then/else operation of values -} ->
  (Integer -> Integer -> Maybe Integer)
     {- ^ reindexing operation -} ->
  SEval sym a  {- ^ zero value -} ->
  Nat' {- ^ size of the sequence -} ->
  SeqMap sym a {- ^ sequence to shift -} ->
  WordValue sym {- ^ shift amount -} ->
  SEval sym (SeqMap sym a)
shiftSeqByWord sym merge reindex zro sz xs idx =
  wordValAsLit sym idx >>= \case
    Just j -> shiftOp xs j
    Nothing ->
      do idx_segs <- enumerateIndexSegments sym idx
         barrelShifter sym merge shiftOp sz xs idx_bits idx_segs
  where
   idx_bits = wordValueSize sym idx

   shiftOp vs shft =
     pure $ indexSeqMap $ \i ->
       case reindex i shft of
         Nothing -> zro
         Just i' -> lookupSeqMap vs i'

-- | Compute the size of a word value
-- TODO, can we get rid of this? If feels like it should be
--  unnecessary.
wordValueSize :: Backend sym => sym -> WordValue sym -> Integer
wordValueSize sym (WordVal w)  = wordLen sym w
wordValueSize _ (ThunkWordVal n _) = n
wordValueSize _ (BitmapVal n _ _) = n

-- | Select an individual bit from a word value
indexWordValue :: Backend sym => sym -> WordValue sym -> Integer -> SEval sym (SBit sym)
indexWordValue sym (ThunkWordVal _ m) idx = do m' <- m ; indexWordValue sym m' idx
indexWordValue sym (WordVal w) idx
   | 0 <= idx && idx < wordLen sym w = wordBit sym w idx
   | otherwise = invalidIndex sym idx
indexWordValue sym (BitmapVal n _packed xs) idx
   | 0 <= idx && idx < n = lookupSeqMap xs idx
   | otherwise = invalidIndex sym idx

-- | Produce a new 'WordValue' from the one given by updating the @i@th bit with the
--   given bit value.
updateWordValue :: Backend sym =>
  sym -> WordValue sym -> Integer -> SEval sym (SBit sym) -> SEval sym (WordValue sym)
updateWordValue sym wv0 idx b = loop wv0
  where
    loop (ThunkWordVal sz m) =
      isReady sym m >>= \case
        Just w  -> loop w
        Nothing -> delayWordValue sym sz (loop =<< m)

    loop (WordVal w)
      | idx < 0 || idx >= wordLen sym w = invalidIndex sym idx
      | otherwise =
          isReady sym b >>= \case
            Just b' -> WordVal <$> wordUpdate sym w idx b'
            Nothing ->
              do let bs = unpackBitmap sym w
                 bitmapWordVal sym (wordLen sym w) $ updateSeqMap bs idx b

    loop (BitmapVal sz packed bs)
      | 0 <= idx && idx < sz =
          isReady sym packed >>= \case
            Just w  -> loop (WordVal w)
            Nothing -> bitmapWordVal sym sz $ updateSeqMap bs idx b
      | otherwise = invalidIndex sym idx

{-# INLINE mergeWord #-}
mergeWord :: Backend sym =>
  sym ->
  SBit sym ->
  WordValue sym ->
  WordValue sym ->
  SEval sym (WordValue sym)
mergeWord sym c (ThunkWordVal _ m1) (ThunkWordVal _ m2) =
  mergeWord' sym c (unwindThunks m1) (unwindThunks m2)
mergeWord sym c (ThunkWordVal _ m1) w2 =
  mergeWord' sym c (unwindThunks m1) (pure w2)
mergeWord sym c w1 (ThunkWordVal _ m2) =
  mergeWord' sym c (pure w1) (unwindThunks m2)

mergeWord sym c (WordVal w1) (WordVal w2) =
  WordVal <$> iteWord sym c w1 w2

mergeWord sym c (BitmapVal n1 packed1 bs1) (WordVal w2) =
  isReady sym packed1 >>= \case
    Just w1 -> WordVal <$> iteWord sym c w1 w2
    Nothing -> mergeBitmaps sym c n1 bs1 (unpackBitmap sym w2)

mergeWord sym c (WordVal w1) (BitmapVal n2 packed2 bs2) =
  isReady sym packed2 >>= \case
    Just w2 -> WordVal <$> iteWord sym c w1 w2
    Nothing -> mergeBitmaps sym c n2 (unpackBitmap sym w1) bs2

mergeWord sym c (BitmapVal n1 packed1 bs1) (BitmapVal _n2 packed2 bs2) =
  do r1 <- isReady sym packed1
     r2 <- isReady sym packed2
     case (r1,r2) of
       (Just w1, Just w2) -> WordVal <$> iteWord sym c w1 w2
       _ -> mergeBitmaps sym c n1 bs1 bs2

mergeBitmaps :: Backend sym =>
  sym ->
  SBit sym ->
  Integer ->
  SeqMap sym (SBit sym) ->
  SeqMap sym (SBit sym) ->
  SEval sym (WordValue sym)
mergeBitmaps sym c sz bs1 bs2 =
  do bs <- memoMap sym (Nat sz) (mergeSeqMap sym (iteBit sym) c bs1 bs2)
     bitmapWordVal sym sz bs

{-# INLINE mergeWord' #-}
mergeWord' :: Backend sym =>
  sym ->
  SBit sym ->
  SEval sym (WordValue sym) ->
  SEval sym (WordValue sym) ->
  SEval sym (WordValue sym)
mergeWord' sym c x y
  | Just b <- bitAsLit sym c = if b then x else y
  | otherwise = mergeEval sym (mergeWord sym) c x y
