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
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Cryptol.Eval.Value
  ( -- * GenericValue
    GenValue(..)
  , forceWordValue
  , forceValue
  , Backend(..)
  , asciiMode

  , EvalOpts(..)
    -- ** Value introduction operations
  , word
  , lam
  , flam
  , tlam
  , nlam
  , ilam
  , mkSeq
    -- ** Value eliminators
  , fromVBit
  , fromVInteger
  , fromVRational
  , fromVFloat
  , fromVSeq
  , fromSeq
  , fromWordVal
  , asIndex
  , fromVWord
  , vWordLen
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
  , SeqMap (..)
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

    -- * WordValue
  , WordValue
  , wordVal
  , largeBitsVal
  , largeBitsVal'
  , asWordList
  , asWordVal
  , asBitsMap
  , asBitsMap'
  , joinWordVal
  , splitWordVal
  , extractWordVal
  , wordValLogicOp
  , wordValUnaryOp
  , assertWordValueInBounds
  , enumerateWordValue
  , enumerateWordValueRev
  , wordValueSize
  , indexWordValue
  , updateWordValue
  , viewWordOrBits
  , viewWordOrBitsMap
  , lazyViewWordOrBits
  , lazyViewWordOrBitsMap
  , delayWordValue
  , joinWords
  , wordShiftByInt
  , wordShiftByWord
  , wordValAsLit

    -- * Merge and if/then/else
  , iteValue
  , mergeWord
  , mergeValue
  , barrelShifter

  , enumerateIntBits'
  ) where

import Control.Monad (join, unless)
import Data.Bits
import Data.Ratio
import Numeric (showIntAtBase)

import Cryptol.Backend
import Cryptol.Backend.Concrete (Concrete(..))
import Cryptol.Backend.SeqMap
import qualified Cryptol.Backend.Arch as Arch
import Cryptol.Backend.Monad
  ( evalPanic, wordTooWide, CallStack, combineCallStacks, EvalError(..) )
import Cryptol.Backend.FloatHelpers (fpPP)
import Cryptol.Eval.Type

import Cryptol.TypeCheck.Solver.InfNat(Nat'(..), widthInteger)

import Cryptol.Utils.Ident (Ident)
import Cryptol.Utils.Logger(Logger)
import Cryptol.Utils.Panic(panic)
import Cryptol.Utils.PP
import Cryptol.Utils.RecordMap

import GHC.Generics (Generic)

-- | Some options for evalutaion
data EvalOpts = EvalOpts
  { evalLogger :: Logger    -- ^ Where to print stuff (e.g., for @trace@)
  , evalPPOpts :: PPOpts    -- ^ How to pretty print things.
  }

-- Values ----------------------------------------------------------------------

-- | An arbitrarily-chosen number of elements where we switch from a dense
--   sequence representation of bit-level words to 'SeqMap' representation.
largeBitSize :: Integer
largeBitSize = 1 `shiftL` 48

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
  | LargeBitsVal !Integer !(SeqMap sym (SBit sym))
                                              -- ^ A large bitvector sequence, represented as a
                                              --   'SeqMap' of bits.
 deriving (Generic)

wordVal :: SWord sym -> WordValue sym
wordVal = WordVal

largeBitsVal :: Backend sym => Integer -> SeqMap sym (GenValue sym) -> WordValue sym
largeBitsVal sz xs = LargeBitsVal sz (fmap fromVBit xs)

largeBitsVal' :: Backend sym => Integer -> SeqMap sym (SBit sym) -> WordValue sym
largeBitsVal' = LargeBitsVal


{-# INLINE joinWordVal #-}
joinWordVal :: Backend sym => sym -> WordValue sym -> WordValue sym -> SEval sym (WordValue sym)
joinWordVal sym (WordVal w1) (WordVal w2)
  | wordLen sym w1 + wordLen sym w2 < largeBitSize
  = WordVal <$> joinWord sym w1 w2

joinWordVal sym (ThunkWordVal _ m1) w2
  = do w1 <- m1
       joinWordVal sym w1 w2

joinWordVal sym w1 (ThunkWordVal _ m2)
  = do w2 <- m2
       joinWordVal sym w1 w2

joinWordVal sym w1 w2
  = pure $ LargeBitsVal (n1+n2) (concatSeqMap n1 (asBitsMap sym w1) (asBitsMap sym w2))
 where n1 = wordValueSize sym w1
       n2 = wordValueSize sym w2


{-# INLINE splitWordVal #-}

splitWordVal ::
  Backend sym =>
  sym ->
  Integer ->
  Integer ->
  WordValue sym ->
  SEval sym (WordValue sym, WordValue sym)
splitWordVal sym leftWidth rightWidth (WordVal w) =
  do (lw, rw) <- splitWord sym leftWidth rightWidth w
     pure (WordVal lw, WordVal rw)

splitWordVal sym leftWidth rightWidth (ThunkWordVal n m)
  | isReady sym m = splitWordVal sym leftWidth rightWidth =<< m
  | otherwise =
      do m' <- sDelay sym (splitWordVal sym leftWidth rightWidth =<< m)
         return (ThunkWordVal n (fst <$> m'), ThunkWordVal n (snd <$> m'))

splitWordVal _ leftWidth rightWidth (LargeBitsVal _n xs) =
  let (lxs, rxs) = splitSeqMap leftWidth xs
   in pure (LargeBitsVal leftWidth lxs, LargeBitsVal rightWidth rxs)

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
extractWordVal sym len start (ThunkWordVal n m)
  | isReady sym m = extractWordVal sym len start =<< m
  | otherwise =
      do m' <- sDelay sym (extractWordVal sym len start =<< m)
         pure (ThunkWordVal n m')
extractWordVal _ len start (LargeBitsVal n xs) =
   let xs' = dropSeqMap (n - start - len) xs
    in pure $ LargeBitsVal len xs'

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

wordValLogicOp sym bop wop (ThunkWordVal _ m1) w2 =
  do w1 <- m1
     wordValLogicOp sym bop wop w1 w2

wordValLogicOp sym bop wop w1 (ThunkWordVal _ m2) =
  do w2 <- m2
     wordValLogicOp sym bop wop w1 w2

wordValLogicOp sym bop _ w1 w2 = LargeBitsVal (wordValueSize sym w1) <$> zs
     where zs = memoMap sym $ IndexSeqMap $ \i -> join (bop <$> (lookupSeqMap xs i) <*> (lookupSeqMap ys i))
           xs = asBitsMap sym w1
           ys = asBitsMap sym w2

{-# INLINE wordValUnaryOp #-}
wordValUnaryOp ::
  Backend sym =>
  sym ->
  (SBit sym -> SEval sym (SBit sym)) ->
  (SWord sym -> SEval sym (SWord sym)) ->
  WordValue sym ->
  SEval sym (WordValue sym)
wordValUnaryOp _ _ wop (WordVal w)  = WordVal <$> (wop w)
wordValUnaryOp sym bop wop (ThunkWordVal _ m) = wordValUnaryOp sym bop wop =<< m
wordValUnaryOp sym bop _ (LargeBitsVal n xs) = LargeBitsVal n <$> mapSeqMap sym bop xs

{-# SPECIALIZE joinWords ::
  Concrete ->
  Integer ->
  Integer ->
  SeqMap Concrete (GenValue Concrete)->
  SEval Concrete (GenValue Concrete)
  #-}
joinWords :: forall sym.
  Backend sym =>
  sym ->
  Integer ->
  Integer ->
  SeqMap sym (GenValue sym) ->
  SEval sym (GenValue sym)

-- small enough to pack
joinWords sym nParts nEach xs | nParts * nEach < largeBitSize =
  loop (wordVal <$> wordLit sym 0 0) (enumerateSeqMap nParts xs)

 where
 loop :: SEval sym (WordValue sym) -> [SEval sym (GenValue sym)] -> SEval sym (GenValue sym)
 loop !wv [] =
    let len = (nParts * nEach) in
    VWord len <$> delayWordValue sym len wv
 loop !wv (w : ws) =
    w >>= \case
      VWord _ w' ->
        do let wv' = join (joinWordVal sym <$> wv <*> pure w')
           loop wv' ws
      _ -> evalPanic "joinWords: expected word value" []

-- too large to pack
joinWords sym nParts nEach xs =
   return $ VWord (nParts * nEach) $ LargeBitsVal (nParts * nEach) zs
  where
    zs = IndexSeqMap $ \i ->
            do let (q,r) = divMod i nEach
               ys <- fromWordVal "join seq" <$> lookupSeqMap xs q
               indexWordValue sym ys r

wordValAsLit :: Backend sym => sym -> WordValue sym -> Maybe Integer
wordValAsLit sym (WordVal w) = snd <$> wordAsLit sym w
wordValAsLit _ _ = Nothing

-- | Force a word value into packed word form
asWordVal :: Backend sym => sym -> WordValue sym -> SEval sym (SWord sym)
asWordVal _   (WordVal w)         = return w
asWordVal sym (ThunkWordVal _ m)  = asWordVal sym =<< m
asWordVal sym (LargeBitsVal n xs) = packWord sym =<< sequence (enumerateSeqMap n xs)

asWordList :: forall sym. Backend sym => sym -> [WordValue sym] -> SEval sym (Maybe [SWord sym])
asWordList sym = loop id
 where
   loop :: ([SWord sym] -> [SWord sym]) -> [WordValue sym] -> SEval sym (Maybe [SWord sym])
   loop f [] = pure (Just (f []))
   loop f (WordVal x : vs) = loop (f . (x:)) vs
   loop f (ThunkWordVal _ m : vs)
     | isReady sym m = do m' <- m; loop f (m' : vs)
   loop _ _ = pure Nothing

-- | Force a word value into a sequence of bits
asBitsMap :: Backend sym => sym -> WordValue sym -> SeqMap sym (SBit sym)
asBitsMap sym (WordVal w)         = IndexSeqMap $ \i -> wordBit sym w i
asBitsMap sym (ThunkWordVal _ m)  = IndexSeqMap $ \i -> do mp <- asBitsMap sym <$> m; lookupSeqMap mp i
asBitsMap _   (LargeBitsVal _ xs) = xs

-- | Force a word value into a sequence of bits
asBitsMap' :: Backend sym => sym -> WordValue sym -> SeqMap sym (GenValue sym)
asBitsMap' sym w = IndexSeqMap $ \i -> VBit <$> lookupSeqMap mp i
 where mp = asBitsMap sym w

-- | Turn a word value into a sequence of bits, forcing each bit.
--   The sequence is returned in big-endian order.
enumerateWordValue :: Backend sym => sym -> WordValue sym -> SEval sym [SBit sym]
enumerateWordValue sym (WordVal w) = unpackWord sym w
enumerateWordValue sym (ThunkWordVal _ m) = enumerateWordValue sym =<< m
enumerateWordValue _ (LargeBitsVal n xs)  = sequence (enumerateSeqMap n xs)

-- | Turn a word value into a sequence of bits, forcing each bit.
--   The sequence is returned in reverse of the usual order, which is little-endian order.
enumerateWordValueRev :: Backend sym => sym -> WordValue sym -> SEval sym [SBit sym]
enumerateWordValueRev sym (WordVal w)  = reverse <$> unpackWord sym w
enumerateWordValueRev sym (ThunkWordVal _ m)  = enumerateWordValueRev sym =<< m
enumerateWordValueRev _   (LargeBitsVal n xs) = sequence (enumerateSeqMap n (reverseSeqMap n xs))

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
assertWordValueInBounds sym n (LargeBitsVal w bits) =
  do bitsList <- sequence (enumerateSeqMap w bits)
     p <- bitsValueLessThan sym w bitsList n
     assertSideCondition sym p (InvalidIndex Nothing)


lazyViewWordOrBitsMap ::
  Backend sym =>
  sym ->
  (SWord sym -> SEval sym (WordValue sym)) ->
  (Integer -> SeqMap sym (SBit sym) -> SEval sym (WordValue sym)) ->
  WordValue sym -> SEval sym (WordValue sym)

lazyViewWordOrBitsMap sym wop bop (ThunkWordVal sz m)
  | isReady sym m = viewWordOrBitsMap sym wop bop =<< m
  | otherwise     = delayWordValue sym sz (viewWordOrBitsMap sym wop bop =<< m)

lazyViewWordOrBitsMap _sym wop _bop (WordVal w) =
  wop w
lazyViewWordOrBitsMap _sym _wop bop (LargeBitsVal n bs) =
  bop n bs


viewWordOrBitsMap ::
  Backend sym =>
  sym ->
  (SWord sym -> SEval sym a) ->
  (Integer -> SeqMap sym (SBit sym) -> SEval sym a) ->
  WordValue sym -> SEval sym a
viewWordOrBitsMap sym wop bop (ThunkWordVal _ m) =
  viewWordOrBitsMap sym wop bop =<< m
viewWordOrBitsMap _sym wop _bop (WordVal w) =
  wop w
viewWordOrBitsMap _sym _wop bop (LargeBitsVal n bs) =
  bop n bs

viewWordOrBits ::
  Backend sym =>
  sym ->
  (SWord sym -> SEval sym a) ->
  ([SBit sym] -> SEval sym a) ->
  WordValue sym -> SEval sym a

viewWordOrBits sym wop bop (ThunkWordVal _ m) =
  viewWordOrBits sym wop bop =<< m
viewWordOrBits _sym wop _bop (WordVal w) =
  wop w
viewWordOrBits _sym _wop bop (LargeBitsVal n bs) =
  bop =<< sequence (enumerateSeqMap n bs)

lazyViewWordOrBits ::
  Backend sym =>
  sym ->
  (SWord sym -> SEval sym (WordValue sym)) ->
  ([SBit sym] -> SEval sym (WordValue sym)) ->
  WordValue sym -> SEval sym (WordValue sym)

lazyViewWordOrBits sym wop bop (ThunkWordVal sz m)
  | isReady sym m = viewWordOrBits sym wop bop =<< m
  | otherwise     = delayWordValue sym sz (viewWordOrBits sym wop bop =<< m)

lazyViewWordOrBits _sym wop _bop (WordVal w) =
  wop w
lazyViewWordOrBits _sym _wop bop (LargeBitsVal n bs) =
  bop =<< sequence (enumerateSeqMap n bs)


delayWordValue :: Backend sym => sym -> Integer -> SEval sym (WordValue sym) -> SEval sym (WordValue sym)
delayWordValue sym sz m
  | isReady sym m = m
  | otherwise     = ThunkWordVal sz <$> sDelay sym m


wordShiftByInt ::
  Backend sym =>
  sym ->
  (SWord sym -> SWord sym -> SEval sym (SWord sym)) ->
  (Integer -> Integer -> Maybe Integer) ->
  SInteger sym ->
  WordValue sym ->
  SEval sym (WordValue sym)

wordShiftByInt sym wop reindex idx x =
  case x of
    ThunkWordVal w wm
      | isReady sym wm ->
          wordShiftByInt sym wop reindex idx =<< wm
      | otherwise ->
         do m' <- sDelay sym (wordShiftByInt sym wop reindex idx =<< wm)
            return (ThunkWordVal w m')

    WordVal x' -> WordVal <$> (wop x' =<< wordFromInt sym (wordLen sym x') idx)

    LargeBitsVal n bs0 ->
         do idx_bits <- enumerateIntBits' sym n idx
            LargeBitsVal n <$> barrelShifter sym (iteBit sym) shiftOp bs0 idx_bits

 where
   shiftOp vs shft =
      memoMap sym $ IndexSeqMap $ \i ->
        case reindex i shft of
          Nothing -> pure $ bitLit sym False
          Just i' -> lookupSeqMap vs i'




wordShiftByWord ::
  Backend sym =>
  sym ->
  (SWord sym -> SWord sym -> SEval sym (SWord sym)) ->
  (Integer -> Integer -> Maybe Integer) ->
  WordValue sym ->
  WordValue sym ->
  SEval sym (WordValue sym)
wordShiftByWord sym wop reindex idx x =
  case x of
    ThunkWordVal w wm
      | isReady sym wm ->
          wordShiftByWord sym wop reindex idx =<< wm
      | otherwise ->
         do m' <- sDelay sym (wordShiftByWord sym wop reindex idx =<< wm)
            return (ThunkWordVal w m')

    WordVal x' -> WordVal <$> (wop x' =<< asWordVal sym idx)

    LargeBitsVal n bs0 ->
      do idx_bits <- enumerateWordValue sym idx
         LargeBitsVal n <$> barrelShifter sym (iteBit sym) shiftOp bs0 idx_bits

 where
   shiftOp vs shft =
      memoMap sym $ IndexSeqMap $ \i ->
        case reindex i shft of
          Nothing -> pure $ bitLit sym False
          Just i' -> lookupSeqMap vs i'


-- | Compute the size of a word value
-- TODO, can we get rid of this? If feels like it should be
--  unnecessary.
wordValueSize :: Backend sym => sym -> WordValue sym -> Integer
wordValueSize sym (WordVal w)  = wordLen sym w
wordValueSize _ (ThunkWordVal n _) = n
wordValueSize _ (LargeBitsVal n _) = n

-- | Select an individual bit from a word value
indexWordValue :: Backend sym => sym -> WordValue sym -> Integer -> SEval sym (SBit sym)
indexWordValue sym (ThunkWordVal _ m) idx = do m' <- m ; indexWordValue sym m' idx
indexWordValue sym (WordVal w) idx
   | 0 <= idx && idx < wordLen sym w = wordBit sym w idx
   | otherwise = invalidIndex sym idx
indexWordValue sym (LargeBitsVal n xs) idx
   | 0 <= idx && idx < n = lookupSeqMap xs idx
   | otherwise = invalidIndex sym idx

-- | Produce a new 'WordValue' from the one given by updating the @i@th bit with the
--   given bit value.
updateWordValue :: Backend sym =>
  sym -> WordValue sym -> Integer -> SEval sym (SBit sym) -> SEval sym (WordValue sym)
updateWordValue sym (WordVal w) idx b
   | idx < 0 || idx >= wordLen sym w = invalidIndex sym idx
   | isReady sym b = WordVal <$> (wordUpdate sym w idx =<< b)

updateWordValue sym wv idx b
   | 0 <= idx && idx < wordValueSize sym wv =
        pure $ LargeBitsVal (wordValueSize sym wv) $ updateSeqMap (asBitsMap sym wv) idx b
   | otherwise = invalidIndex sym idx

-- | Compute the list of bits in an integer in big-endian order.
--   The integer argument is a concrete upper bound for
--   the symbolic integer.
enumerateIntBits' :: Backend sym =>
  sym ->
  Integer ->
  SInteger sym ->
  SEval sym [SBit sym]
enumerateIntBits' sym n idx =
  do w <- wordFromInt sym (widthInteger n) idx
     unpackWord sym w


-- | Generic value type, parameterized by bit and word types.
--
--   NOTE: we maintain an important invariant regarding sequence types.
--   'VSeq' must never be used for finite sequences of bits.
--   Always use the 'VWord' constructor instead!  Infinite sequences of bits
--   are handled by the 'VStream' constructor, just as for other types.
data GenValue sym
  = VRecord !(RecordMap Ident (SEval sym (GenValue sym))) -- ^ @ { .. } @
  | VTuple ![SEval sym (GenValue sym)]              -- ^ @ ( .. ) @
  | VBit !(SBit sym)                           -- ^ @ Bit    @
  | VInteger !(SInteger sym)                   -- ^ @ Integer @ or @ Z n @
  | VRational !(SRational sym)                 -- ^ @ Rational @
  | VFloat !(SFloat sym)
  | VSeq !Integer !(SeqMap sym (GenValue sym)) -- ^ @ [n]a   @
                                               --   Invariant: VSeq is never a sequence of bits
  | VWord !Integer !(WordValue sym)            -- ^ @ [n]Bit @
  | VStream !(SeqMap sym (GenValue sym))       -- ^ @ [inf]a @
  | VFun  CallStack (SEval sym (GenValue sym) -> SEval sym (GenValue sym)) -- ^ functions
  | VPoly CallStack (TValue -> SEval sym (GenValue sym))   -- ^ polymorphic values (kind *)
  | VNumPoly CallStack (Nat' -> SEval sym (GenValue sym))  -- ^ polymorphic values (kind #)
 deriving Generic


-- | Force the evaluation of a word value
forceWordValue :: Backend sym => WordValue sym -> SEval sym ()
forceWordValue (WordVal w)  = seq w (return ())
forceWordValue (ThunkWordVal _ m)  = forceWordValue =<< m
forceWordValue (LargeBitsVal n xs) = mapM_ (\x -> const () <$> x) (enumerateSeqMap n xs)

-- | Force the evaluation of a value
forceValue :: Backend sym => GenValue sym -> SEval sym ()
forceValue v = case v of
  VRecord fs  -> mapM_ (forceValue =<<) fs
  VTuple xs   -> mapM_ (forceValue =<<) xs
  VSeq n xs   -> mapM_ (forceValue =<<) (enumerateSeqMap n xs)
  VBit b      -> seq b (return ())
  VInteger i  -> seq i (return ())
  VRational q -> seq q (return ())
  VFloat f    -> seq f (return ())
  VWord _ wv  -> forceWordValue wv
  VStream _   -> return ()
  VFun{}      -> return ()
  VPoly{}     -> return ()
  VNumPoly{}  -> return ()



instance Backend sym => Show (GenValue sym) where
  show v = case v of
    VRecord fs -> "record:" ++ show (displayOrder fs)
    VTuple xs  -> "tuple:" ++ show (length xs)
    VBit _     -> "bit"
    VInteger _ -> "integer"
    VRational _ -> "rational"
    VFloat _   -> "float"
    VSeq n _   -> "seq:" ++ show n
    VWord n _  -> "word:"  ++ show n
    VStream _  -> "stream"
    VFun{}     -> "fun"
    VPoly{}    -> "poly"
    VNumPoly{} -> "numpoly"


-- Pretty Printing -------------------------------------------------------------

ppValue :: forall sym.
  Backend sym =>
  sym ->
  PPOpts ->
  GenValue sym ->
  SEval sym Doc
ppValue x opts = loop
  where
  loop :: GenValue sym -> SEval sym Doc
  loop val = case val of
    VRecord fs         -> do fs' <- traverse (>>= loop) fs
                             return $ braces (sep (punctuate comma (map ppField (displayFields fs'))))
      where
      ppField (f,r) = pp f <+> char '=' <+> r
    VTuple vals        -> do vals' <- traverse (>>=loop) vals
                             return $ parens (sep (punctuate comma vals'))
    VBit b             -> ppSBit x b
    VInteger i         -> ppSInteger x i
    VRational q        -> ppSRational x q
    VFloat i           -> ppSFloat x opts i
    VSeq sz vals       -> ppWordSeq sz vals
    VWord _ wv         -> ppWordVal wv
    VStream vals       -> do vals' <- traverse (>>=loop) $ enumerateSeqMap (useInfLength opts) vals
                             return $ brackets $ fsep
                                   $ punctuate comma
                                   ( vals' ++ [text "..."]
                                   )
    VFun{}             -> return $ text "<function>"
    VPoly{}            -> return $ text "<polymorphic value>"
    VNumPoly{}         -> return $ text "<polymorphic value>"

  ppWordVal :: WordValue sym -> SEval sym Doc
  ppWordVal w = ppSWord x opts =<< asWordVal x w

  ppWordSeq :: Integer -> SeqMap sym (GenValue sym) -> SEval sym Doc
  ppWordSeq sz vals = do
    ws <- sequence (enumerateSeqMap sz vals)
    case ws of
      w : _
        | Just l <- vWordLen w
        , asciiMode opts l
        -> do vs <- traverse (fromVWord x "ppWordSeq") ws
              case traverse (wordAsChar x) vs of
                Just str -> return $ text (show str)
                _ -> do vs' <- mapM (ppSWord x opts) vs
                        return $ brackets (fsep (punctuate comma vs'))
      _ -> do ws' <- traverse loop ws
              return $ brackets (fsep (punctuate comma ws'))

ppSBit :: Backend sym => sym -> SBit sym -> SEval sym Doc
ppSBit sym b =
  case bitAsLit sym b of
    Just True  -> pure (text "True")
    Just False -> pure (text "False")
    Nothing    -> pure (text "?")

ppSInteger :: Backend sym => sym -> SInteger sym -> SEval sym Doc
ppSInteger sym x =
  case integerAsLit sym x of
    Just i  -> pure (integer i)
    Nothing -> pure (text "[?]")

ppSFloat :: Backend sym => sym -> PPOpts -> SFloat sym -> SEval sym Doc
ppSFloat sym opts x =
  case fpAsLit sym x of
    Just fp -> pure (fpPP opts fp)
    Nothing -> pure (text "[?]")

ppSRational :: Backend sym => sym -> SRational sym -> SEval sym Doc
ppSRational sym (SRational n d)
  | Just ni <- integerAsLit sym n
  , Just di <- integerAsLit sym d
  = let q = ni % di in
      pure (text "(ratio" <+> integer (numerator q) <+> (integer (denominator q) <> text ")"))

  | otherwise
  = do n' <- ppSInteger sym n
       d' <- ppSInteger sym d
       pure (text "(ratio" <+> n' <+> (d' <> text ")"))

ppSWord :: Backend sym => sym -> PPOpts -> SWord sym -> SEval sym Doc
ppSWord sym opts bv
  | asciiMode opts width =
      case wordAsLit sym bv of
        Just (_,i) -> pure (text (show (toEnum (fromInteger i) :: Char)))
        Nothing    -> pure (text "?")

  | otherwise =
      case wordAsLit sym bv of
        Just (_,i) ->
          let val = value i in
          pure (prefix (length val) <.> text val)
        Nothing
          | base == 2  -> sliceDigits 1 "0b"
          | base == 8  -> sliceDigits 3 "0o"
          | base == 16 -> sliceDigits 4 "0x"
          | otherwise  -> pure (text "[?]")

  where
  width = wordLen sym bv

  base = if useBase opts > 36 then 10 else useBase opts

  padding bitsPerDigit len = text (replicate padLen '0')
    where
    padLen | m > 0     = d + 1
           | otherwise = d

    (d,m) = (fromInteger width - (len * bitsPerDigit))
                   `divMod` bitsPerDigit

  prefix len = case base of
    2  -> text "0b" <.> padding 1 len
    8  -> text "0o" <.> padding 3 len
    10 -> empty
    16 -> text "0x" <.> padding 4 len
    _  -> text "0"  <.> char '<' <.> int base <.> char '>'

  value i = showIntAtBase (toInteger base) (digits !!) i ""
  digits  = "0123456789abcdefghijklmnopqrstuvwxyz"

  toDigit w =
    case wordAsLit sym w of
      Just (_,i) | i <= 36 -> digits !! fromInteger i
      _ -> '?'

  sliceDigits bits pfx =
    do ws <- goDigits bits [] bv
       let ds = map toDigit ws
       pure (text pfx <.> text ds)

  goDigits bits ds w
    | wordLen sym w > bits =
        do (hi,lo) <- splitWord sym (wordLen sym w - bits) bits w
           goDigits bits (lo:ds) hi

    | wordLen sym w > 0 = pure (w:ds)

    | otherwise          = pure ds

-- Value Constructors ----------------------------------------------------------

-- | Create a packed word of n bits.
word :: Backend sym => sym -> Integer -> Integer -> SEval sym (GenValue sym)
word sym n i
  | n >= Arch.maxBigIntWidth = wordTooWide n
  | otherwise                = VWord n . WordVal <$> wordLit sym n i


-- | Construct a function value
lam :: Backend sym => sym -> (SEval sym (GenValue sym) -> SEval sym (GenValue sym)) -> SEval sym (GenValue sym)
lam sym f = VFun <$> sGetCallStack sym <*> pure f

-- | Functions that assume floating point inputs
flam :: Backend sym => sym ->
        (SFloat sym -> SEval sym (GenValue sym)) -> SEval sym (GenValue sym)
flam sym f = VFun <$> sGetCallStack sym <*> pure (\arg -> arg >>= f . fromVFloat)

-- | A type lambda that expects a 'Type'.
tlam :: Backend sym => sym -> (TValue -> SEval sym (GenValue sym)) -> SEval sym (GenValue sym)
tlam sym f = VPoly <$> sGetCallStack sym <*> pure f

-- | A type lambda that expects a 'Type' of kind #.
nlam :: Backend sym => sym -> (Nat' -> SEval sym (GenValue sym)) -> SEval sym (GenValue sym)
nlam sym f = VNumPoly <$> sGetCallStack sym <*> pure f

-- | A type lambda that expects a finite numeric type.
ilam :: Backend sym => sym -> (Integer -> SEval sym (GenValue sym)) -> SEval sym (GenValue sym)
ilam sym f =
   nlam sym (\n -> case n of
                     Nat i -> f i
                     Inf   -> panic "ilam" [ "Unexpected `inf`" ])

-- | Construct either a finite sequence, or a stream.  In the finite case,
-- record whether or not the elements were bits, to aid pretty-printing.
mkSeq :: Backend sym => Nat' -> TValue -> SeqMap sym (GenValue sym) -> GenValue sym
mkSeq len elty vals = case len of
  Nat n
    | isTBit elty -> VWord n $ largeBitsVal n vals
    | otherwise   -> VSeq n vals
  Inf             -> VStream vals


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
fromVSeq :: GenValue sym -> SeqMap sym (GenValue sym)
fromVSeq val = case val of
  VSeq _ vs -> vs
  _         -> evalPanic "fromVSeq" ["not a sequence"]

-- | Extract a sequence.
fromSeq :: Backend sym => String -> GenValue sym -> SEval sym (SeqMap sym (GenValue sym))
fromSeq msg val = case val of
  VSeq _ vs   -> return vs
  VStream vs  -> return vs
  _           -> evalPanic "fromSeq" ["not a sequence", msg]

fromWordVal :: Backend sym => String -> GenValue sym -> WordValue sym
fromWordVal _msg (VWord _ wval) = wval
fromWordVal msg _ = evalPanic "fromWordVal" ["not a word value", msg]

asIndex :: Backend sym =>
  sym -> String -> TValue -> GenValue sym -> Either (SInteger sym) (WordValue sym)
asIndex _sym _msg TVInteger (VInteger i) = Left i
asIndex _sym _msg _ (VWord _ wval) = Right wval
asIndex _sym  msg _ _ = evalPanic "asIndex" ["not an index value", msg]

-- | Extract a packed word.
fromVWord :: Backend sym => sym -> String -> GenValue sym -> SEval sym (SWord sym)
fromVWord sym _msg (VWord _ wval) = asWordVal sym wval
fromVWord _ msg _ = evalPanic "fromVWord" ["not a word", msg]

vWordLen :: Backend sym => GenValue sym -> Maybe Integer
vWordLen val = case val of
  VWord n _wv              -> Just n
  _                        -> Nothing

-- | If the given list of values are all fully-evaluated thunks
--   containing bits, return a packed word built from the same bits.
--   However, if any value is not a fully-evaluated bit, return 'Nothing'.
tryFromBits :: Backend sym => sym -> [SEval sym (GenValue sym)] -> Maybe (SEval sym (SWord sym))
tryFromBits sym = go id
  where
  go f [] = Just (packWord sym =<< sequence (f []))
  go f (v : vs) | isReady sym v = go (f . ((fromVBit <$> v):)) vs
  go _ (_ : _) = Nothing

-- | Extract a function from a value.
fromVFun :: Backend sym => sym -> GenValue sym -> (SEval sym (GenValue sym) -> SEval sym (GenValue sym))
fromVFun sym val = case val of
  VFun fnstk f ->
    \x -> sModifyCallStack sym (\stk -> combineCallStacks stk fnstk) (f x)
  _ -> evalPanic "fromVFun" ["not a function"]

-- | Extract a polymorphic function from a value.
fromVPoly :: Backend sym => sym -> GenValue sym -> (TValue -> SEval sym (GenValue sym))
fromVPoly sym val = case val of
  VPoly fnstk f ->
    \x -> sModifyCallStack sym (\stk -> combineCallStacks stk fnstk) (f x)
  _ -> evalPanic "fromVPoly" ["not a polymorphic value"]

-- | Extract a polymorphic function from a value.
fromVNumPoly :: Backend sym => sym -> GenValue sym -> (Nat' -> SEval sym (GenValue sym))
fromVNumPoly sym val = case val of
  VNumPoly fnstk f ->
    \x -> sModifyCallStack sym (\stk -> combineCallStacks stk fnstk) (f x)
  _  -> evalPanic "fromVNumPoly" ["not a polymorphic value"]

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
  SBit sym ->
  SEval sym (GenValue sym) ->
  SEval sym (GenValue sym) ->
  SEval sym (GenValue sym)
iteValue sym b x y
  | Just True  <- bitAsLit sym b = x
  | Just False <- bitAsLit sym b = y
  | otherwise = mergeValue' sym b x y

{-# INLINE mergeWord #-}
mergeWord :: Backend sym =>
  sym ->
  SBit sym ->
  WordValue sym ->
  WordValue sym ->
  SEval sym (WordValue sym)
mergeWord sym c (ThunkWordVal _ m1) (ThunkWordVal _ m2) =
  mergeWord' sym c m1 m2
mergeWord sym c (ThunkWordVal _ m1) w2 =
  mergeWord' sym c m1 (pure w2)
mergeWord sym c w1 (ThunkWordVal _ m2) =
  mergeWord' sym c (pure w1) m2
mergeWord sym c (WordVal w1) (WordVal w2) =
  WordVal <$> iteWord sym c w1 w2
mergeWord sym c w1 w2 =
  LargeBitsVal (wordValueSize sym w1) <$>
    memoMap sym (mergeSeqMap sym (iteBit sym) c (asBitsMap sym w1) (asBitsMap sym w2))

{-# INLINE mergeWord' #-}
mergeWord' :: Backend sym =>
  sym ->
  SBit sym ->
  SEval sym (WordValue sym) ->
  SEval sym (WordValue sym) ->
  SEval sym (WordValue sym)
mergeWord' sym = mergeEval sym (mergeWord sym)

{-# INLINE mergeValue' #-}
mergeValue' :: Backend sym =>
  sym ->
  SBit sym ->
  SEval sym (GenValue sym) ->
  SEval sym (GenValue sym) ->
  SEval sym (GenValue sym)
mergeValue' sym = mergeEval sym (mergeValue sym)

mergeValue :: Backend sym =>
  sym ->
  SBit sym ->
  GenValue sym ->
  GenValue sym ->
  SEval sym (GenValue sym)
mergeValue sym c v1 v2 =
  case (v1, v2) of
    (VRecord fs1 , VRecord fs2 ) ->
      do let res = zipRecords (\_lbl -> mergeValue' sym c) fs1 fs2
         case res of
           Left f -> panic "Cryptol.Eval.Generic" [ "mergeValue: incompatible record values", show f ]
           Right r -> pure (VRecord r)
    (VTuple vs1  , VTuple vs2  ) | length vs1 == length vs2  ->
                                  pure $ VTuple $ zipWith (mergeValue' sym c) vs1 vs2
    (VBit b1     , VBit b2     ) -> VBit <$> iteBit sym c b1 b2
    (VInteger i1 , VInteger i2 ) -> VInteger <$> iteInteger sym c i1 i2
    (VRational q1, VRational q2) -> VRational <$> iteRational sym c q1 q2
    (VFloat f1   , VFloat f2)    -> VFloat <$> iteFloat sym c f1 f2
    (VWord n1 w1 , VWord n2 w2 ) | n1 == n2 -> VWord n1 <$> mergeWord sym c w1 w2
    (VSeq n1 vs1 , VSeq n2 vs2 ) | n1 == n2 -> VSeq n1 <$> memoMap sym (mergeSeqMapVal sym c vs1 vs2)
    (VStream vs1 , VStream vs2 ) -> VStream <$> memoMap sym (mergeSeqMapVal sym c vs1 vs2)
    (f1@VFun{}   , f2@VFun{}   ) -> lam sym $ \x -> mergeValue' sym c (fromVFun sym f1 x) (fromVFun sym f2 x)
    (f1@VPoly{}  , f2@VPoly{}  ) -> tlam sym $ \x -> mergeValue' sym c (fromVPoly sym f1 x) (fromVPoly sym f2 x)
    (_           , _           ) -> panic "Cryptol.Eval.Generic"
                                  [ "mergeValue: incompatible values" ]

{-# INLINE mergeSeqMapVal #-}
mergeSeqMapVal :: Backend sym =>
  sym ->
  SBit sym ->
  SeqMap sym (GenValue sym)->
  SeqMap sym (GenValue sym)->
  SeqMap sym (GenValue sym)
mergeSeqMapVal sym c x y =
  IndexSeqMap $ \i ->
    iteValue sym c (lookupSeqMap x i) (lookupSeqMap y i)

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

barrelShifter :: Backend sym =>
  sym ->
  (SBit sym -> a -> a -> SEval sym a) ->
  (SeqMap sym a -> Integer -> SEval sym (SeqMap sym a))
     {- ^ concrete shifting operation -} ->
  SeqMap sym a {- ^ initial value -} ->
  [SBit sym]  {- ^ bits of shift amount, in big-endian order -} ->
  SEval sym (SeqMap sym a)
barrelShifter sym mux shift_op = go
  where
  go x [] = return x

  go x (b:bs)
    | Just True <- bitAsLit sym b
    = do x_shft <- shift_op x (2 ^ length bs)
         go x_shft bs

    | Just False <- bitAsLit sym b
    = do go x bs

    | otherwise
    = do x_shft <- shift_op x (2 ^ length bs)
         x' <- memoMap sym (mergeSeqMap sym mux b x_shft x)
         go x' bs
