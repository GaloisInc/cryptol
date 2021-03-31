-- |
-- Module      :  Cryptol.Eval.SBV
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
module Cryptol.Eval.SBV
  ( primTable
  ) where

import qualified Control.Exception as X
import           Control.Monad.IO.Class (MonadIO(..))
import           Data.Bits (bit)
import qualified Data.Map as Map
import qualified Data.Text as T

import Data.SBV.Dynamic as SBV

import Cryptol.Backend
import Cryptol.Backend.Monad (Unsupported(..) )
import Cryptol.Backend.SBV
import Cryptol.Backend.SeqMap
import Cryptol.Backend.WordValue

import Cryptol.Eval.Type (TValue(..))
import Cryptol.Eval.Generic
import Cryptol.Eval.Prims
import Cryptol.Eval.Value
import Cryptol.TypeCheck.Solver.InfNat (Nat'(..))
import Cryptol.Utils.Ident

-- Values ----------------------------------------------------------------------

type Value = GenValue SBV

-- Primitives ------------------------------------------------------------------

-- See also Cryptol.Eval.Concrete.primTable
primTable :: SBV -> IO EvalOpts -> Map.Map PrimIdent (Prim SBV)
primTable sym getEOpts =
  Map.union (genericPrimTable sym getEOpts) $
  Map.fromList $ map (\(n, v) -> (prelPrim (T.pack n), v))

  [ (">>$"         , sshrV sym)

    -- Shifts and rotates
  , ("<<"          , logicShift sym "<<"
                       shiftShrink
                       (\x y -> pure (shl x y))
                       (\x y -> pure (lshr x y))
                       shiftLeftReindex shiftRightReindex)

  , (">>"          , logicShift sym ">>"
                       shiftShrink
                       (\x y -> pure (lshr x y))
                       (\x y -> pure (shl x y))
                       shiftRightReindex shiftLeftReindex)

  , ("<<<"         , logicShift sym "<<<"
                       rotateShrink
                       (\x y -> pure (SBV.svRotateLeft x y))
                       (\x y -> pure (SBV.svRotateRight x y))
                       rotateLeftReindex rotateRightReindex)

  , (">>>"         , logicShift sym ">>>"
                       rotateShrink
                       (\x y -> pure (SBV.svRotateRight x y))
                       (\x y -> pure (SBV.svRotateLeft x y))
                       rotateRightReindex rotateLeftReindex)

    -- Indexing and updates
  , ("@"           , indexPrim sym IndexForward  (indexFront sym) (indexFront_segs sym))
  , ("!"           , indexPrim sym IndexBackward (indexFront sym) (indexFront_segs sym))

  , ("update"      , updatePrim sym (updateFrontSym_word sym) (updateFrontSym sym))
  , ("updateEnd"   , updatePrim sym (updateBackSym_word sym) (updateBackSym sym))

  ]

indexFront ::
  SBV ->
  Nat' ->
  TValue ->
  SeqMap SBV (GenValue SBV) ->
  TValue ->
  SVal ->
  SEval SBV Value
indexFront sym mblen a xs _ix idx
  | Just i <- SBV.svAsInteger idx
  = lookupSeqMap xs i

  | Nat n <- mblen
  , TVSeq wlen TVBit <- a
  = do wvs <- traverse (fromWordVal "indexFront" <$>) (enumerateSeqMap n xs)
       asWordList sym wvs >>= \case
         Just ws ->
           do z <- wordLit sym wlen 0
              return $ VWord wlen $ wordVal $ SBV.svSelect ws z idx
         Nothing -> folded

  | otherwise
  = folded

 where
    k = SBV.kindOf idx
    def = zeroV sym a
    f n y = iteValue sym (SBV.svEqual idx (SBV.svInteger k n)) (lookupSeqMap xs n) y
    folded =
      case k of
        KBounded _ w ->
          case mblen of
            Nat n | n < 2^w -> foldr f def [0 .. n-1]
            _ -> foldr f def [0 .. 2^w - 1]
        _ ->
          case mblen of
            Nat n -> foldr f def [0 .. n-1]
            Inf -> liftIO (X.throw (UnsupportedSymbolicOp "unbounded integer indexing"))

indexFront_segs ::
  SBV ->
  Nat' ->
  TValue ->
  SeqMap SBV (GenValue SBV) ->
  TValue ->
  Integer ->
  [IndexSegment SBV] ->
  SEval SBV Value
indexFront_segs sym mblen a xs ix _idx_bits [WordIndexSegment w] =
  indexFront sym mblen a xs ix w

indexFront_segs sym _mblen _a xs _ix idx_bits segs =
  do xs' <- barrelShifter sym (mergeValue sym) shiftOp xs idx_bits segs
     lookupSeqMap xs' 0
  where
    shiftOp vs amt = pure (indexSeqMap (\i -> lookupSeqMap vs $! amt+i))


updateFrontSym ::
  SBV ->
  Nat' ->
  TValue ->
  SeqMap SBV (GenValue SBV) ->
  Either (SInteger SBV) (WordValue SBV) ->
  SEval SBV (GenValue SBV) ->
  SEval SBV (SeqMap SBV (GenValue SBV))
updateFrontSym sym _len _eltTy vs (Left idx) val =
  case SBV.svAsInteger idx of
    Just i -> return $ updateSeqMap vs i val
    Nothing -> return $ indexSeqMap $ \i ->
      do b <- intEq sym idx =<< integerLit sym i
         iteValue sym b val (lookupSeqMap vs i)

updateFrontSym sym _len _eltTy vs (Right wv) val
  | Just j <- wordValAsLit sym wv =
      return $ updateSeqMap vs j val
  | otherwise =
      return $ indexSeqMap $ \i ->
      do b <- wordValueEqualsInteger sym wv i
         iteValue sym b val (lookupSeqMap vs i)

updateFrontSym_word ::
  SBV ->
  Nat' ->
  TValue ->
  WordValue SBV ->
  Either (SInteger SBV) (WordValue SBV) ->
  SEval SBV (GenValue SBV) ->
  SEval SBV (WordValue SBV)
updateFrontSym_word _ Inf _ _ _ _ = evalPanic "Expected finite sequence" ["updateFrontSym_bits"]

updateFrontSym_word sym (Nat n) eltTy w lridx val =
  lazyViewWordOrBitsMap sym
    -- Sequence to update is a packed word
    (\bv ->
      case lridx of
        -- index value is an integer
        Left idxint ->
          goword bv =<< wordFromInt sym n idxint
        -- index value is a bitvector
        Right idxwv ->
          goword bv =<< asWordVal sym idxwv)
    -- Sequence to update is a SeqMap
    (\_ bs -> largeBitsVal n . fmap fromVBit <$>
      updateFrontSym sym (Nat n) eltTy (fmap VBit bs) lridx val)
    w

  where
  goword bw idx
    | Just j <- SBV.svAsInteger idx =
        updateWordValue sym (wordVal bw) j (fromVBit <$> val)

    | otherwise =
        wordVal <$>
          do b <- fromVBit <$> val
             let sz   = SBV.intSizeOf bw
             let z    = literalSWord sz 0
             let znot = SBV.svNot z
             let q    = SBV.svSymbolicMerge (SBV.kindOf bw) True b znot z
             let msk  = SBV.svShiftRight (literalSWord sz (bit (sz-1))) idx
             let bw'  = SBV.svAnd bw (SBV.svNot msk)
             return $! SBV.svXOr bw' (SBV.svAnd q msk)

updateBackSym ::
  SBV ->
  Nat' ->
  TValue ->
  SeqMap SBV (GenValue SBV) ->
  Either (SInteger SBV) (WordValue SBV) ->
  SEval SBV (GenValue SBV) ->
  SEval SBV (SeqMap SBV (GenValue SBV))
updateBackSym _ Inf _ _ _ _ = evalPanic "Expected finite sequence" ["updateBackSym"]

updateBackSym sym (Nat n) _eltTy vs (Left idx) val =
  case SBV.svAsInteger idx of
    Just i -> return $ updateSeqMap vs (n - 1 - i) val
    Nothing -> return $ indexSeqMap $ \i ->
      do b <- intEq sym idx =<< integerLit sym (n - 1 - i)
         iteValue sym b val (lookupSeqMap vs i)

updateBackSym sym (Nat n) _eltTy vs (Right wv) val
  | Just j <- wordValAsLit sym wv =
      return $ updateSeqMap vs (n - 1 - j) val
  | otherwise =
      return $ indexSeqMap $ \i ->
      do b <- wordValueEqualsInteger sym wv (n - 1 - i)
         iteValue sym b val (lookupSeqMap vs i)


updateBackSym_word ::
  SBV ->
  Nat' ->
  TValue ->
  WordValue SBV ->
  Either (SInteger SBV) (WordValue SBV) ->
  SEval SBV (GenValue SBV) ->
  SEval SBV (WordValue SBV)
updateBackSym_word _ Inf _ _ _ _ = evalPanic "Expected finite sequence" ["updateBackSym_bits"]

updateBackSym_word sym (Nat n) eltTy w lridx val =
  lazyViewWordOrBitsMap sym
    -- Sequence to update is a packed word
    (\bv ->
      case lridx of
        -- index value is an integer
        Left idxint ->
          goword bv =<< wordFromInt sym n idxint
        -- index value is a bitvector
        Right idxwv ->
          goword bv =<< asWordVal sym idxwv)
    -- Sequence to update is a SeqMap
    (\_ bs -> largeBitsVal n . fmap fromVBit <$>
      updateBackSym sym (Nat n) eltTy (fmap VBit bs) lridx val)
    w

  where
  goword bw idx
    | Just j <- SBV.svAsInteger idx =
        updateWordValue sym (wordVal bw) (n - 1 - j) (fromVBit <$> val)

    | otherwise =
        wordVal <$>
          do b <- fromVBit <$> val
             let sz   = SBV.intSizeOf bw
             let z    = literalSWord sz 0
             let znot = SBV.svNot z
             let q    = SBV.svSymbolicMerge (SBV.kindOf bw) True b znot z
             let msk  = SBV.svShiftLeft (literalSWord sz 1) idx
             let bw'  = SBV.svAnd bw (SBV.svNot msk)
             return $! SBV.svXOr bw' (SBV.svAnd q msk)

sshrV :: SBV -> Prim SBV
sshrV sym =
  PNumPoly \n ->
  PTyPoly  \ix ->
  PWordFun \x ->
  PStrict  \y ->
  PPrim $
   case asIndex sym ">>$" ix y of
     Left idx ->
       do let w = toInteger (SBV.intSizeOf x)
          let pneg = svLessThan idx (svInteger KUnbounded 0)
          zneg <- shl x  . svFromInteger w <$> shiftShrink sym n ix (SBV.svUNeg idx)
          zpos <- ashr x . svFromInteger w <$> shiftShrink sym n ix idx
          let z = svSymbolicMerge (kindOf x) True pneg zneg zpos
          return . VWord w . wordVal $ z

     Right wv ->
       do z <- ashr x <$> asWordVal sym wv
          return . VWord (toInteger (SBV.intSizeOf x)) . wordVal $ z
