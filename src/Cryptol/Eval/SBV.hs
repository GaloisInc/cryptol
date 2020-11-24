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
import           Data.Bits (bit, shiftL)
import qualified Data.Map as Map
import qualified Data.Text as T

import Data.SBV.Dynamic as SBV

import Cryptol.Backend
import Cryptol.Backend.Monad ( EvalError(..), Unsupported(..) )
import Cryptol.Backend.SBV

import Cryptol.Eval.Type (TValue(..))
import Cryptol.Eval.Generic
import Cryptol.Eval.Prims
import Cryptol.Eval.Value
import Cryptol.TypeCheck.Solver.InfNat (Nat'(..), widthInteger)
import Cryptol.Utils.Ident

-- Values ----------------------------------------------------------------------

type Value = GenValue SBV

-- Primitives ------------------------------------------------------------------

-- See also Cryptol.Eval.Concrete.primTable
primTable :: SBV -> Map.Map PrimIdent (Prim SBV)
primTable sym = 
  Map.union (genericPrimTable sym) $
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
  , ("@"           , indexPrim sym (indexFront sym) (indexFront_bits sym) (indexFront sym))
  , ("!"           , indexPrim sym (indexBack sym) (indexBack_bits sym) (indexBack sym))

  , ("update"      , updatePrim sym (updateFrontSym_word sym) (updateFrontSym sym))
  , ("updateEnd"   , updatePrim sym (updateBackSym_word sym) (updateBackSym sym))

     -- The trace function simply forces its first two
     -- values before returing the third in the symbolic
     -- evaluator.
  , ("trace",
      PNumPoly \_n ->
      PTyPoly  \_a ->
      PTyPoly  \_b ->
      PFun     \s ->
      PFun     \x ->
      PFun     \y ->
      PPrim
       do _ <- s
          _ <- x
          y)
  ]

indexFront ::
  SBV ->
  Nat' ->
  TValue ->
  SeqMap SBV ->
  TValue ->
  SVal ->
  SEval SBV Value
indexFront sym mblen a xs _ix idx
  | Just i <- SBV.svAsInteger idx
  = lookupSeqMap xs i

  | Nat n <- mblen
  , TVSeq wlen TVBit <- a
  = do wvs <- traverse (fromWordVal "indexFront" =<<) (enumerateSeqMap n xs)
       case asWordList wvs of
         Just ws ->
           do z <- wordLit sym wlen 0
              return $ VWord wlen $ pure $ WordVal $ SBV.svSelect ws z idx
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

indexBack ::
  SBV ->
  Nat' ->
  TValue ->
  SeqMap SBV ->
  TValue ->
  SWord SBV ->
  SEval SBV Value
indexBack sym (Nat n) a xs ix idx = indexFront sym (Nat n) a (reverseSeqMap n xs) ix idx
indexBack _ Inf _ _ _ _ = evalPanic "Expected finite sequence" ["indexBack"]

indexFront_bits ::
  SBV ->
  Nat' ->
  TValue ->
  SeqMap SBV ->
  TValue ->
  [SBit SBV] ->
  SEval SBV Value
indexFront_bits sym mblen _a xs _ix bits0 = go 0 (length bits0) bits0
 where
  go :: Integer -> Int -> [SBit SBV] -> SEval SBV Value
  go i _k []
    -- For indices out of range, fail
    | Nat n <- mblen
    , i >= n
    = raiseError sym (InvalidIndex (Just i))

    | otherwise
    = lookupSeqMap xs i

  go i k (b:bs)
    -- Fail early when all possible indices we could compute from here
    -- are out of bounds
    | Nat n <- mblen
    , (i `shiftL` k) >= n
    = raiseError sym (InvalidIndex Nothing)

    | otherwise
    = iteValue sym b
         (go ((i `shiftL` 1) + 1) (k-1) bs)
         (go  (i `shiftL` 1)      (k-1) bs)


indexBack_bits ::
  SBV ->
  Nat' ->
  TValue ->
  SeqMap SBV ->
  TValue ->
  [SBit SBV] ->
  SEval SBV Value
indexBack_bits sym (Nat n) a xs ix idx = indexFront_bits sym (Nat n) a (reverseSeqMap n xs) ix idx
indexBack_bits _ Inf _ _ _ _ = evalPanic "Expected finite sequence" ["indexBack_bits"]


-- | Compare a symbolic word value with a concrete integer.
wordValueEqualsInteger :: SBV -> WordValue SBV -> Integer -> SEval SBV (SBit SBV)
wordValueEqualsInteger sym wv i
  | wordValueSize sym wv < widthInteger i = return SBV.svFalse
  | otherwise =
    case wv of
      WordVal w -> return $ SBV.svEqual w (literalSWord (SBV.intSizeOf w) i)
      _ -> bitsAre i <$> enumerateWordValueRev sym wv -- little-endian
  where
    bitsAre :: Integer -> [SBit SBV] -> SBit SBV
    bitsAre n [] = SBV.svBool (n == 0)
    bitsAre n (b : bs) = SBV.svAnd (bitIs (odd n) b) (bitsAre (n `div` 2) bs)

    bitIs :: Bool -> SBit SBV -> SBit SBV
    bitIs b x = if b then x else SBV.svNot x


updateFrontSym ::
  SBV ->
  Nat' ->
  TValue ->
  SeqMap SBV ->
  Either (SInteger SBV) (WordValue SBV) ->
  SEval SBV (GenValue SBV) ->
  SEval SBV (SeqMap SBV)
updateFrontSym sym _len _eltTy vs (Left idx) val =
  case SBV.svAsInteger idx of
    Just i -> return $ updateSeqMap vs i val
    Nothing -> return $ IndexSeqMap $ \i ->
      do b <- intEq sym idx =<< integerLit sym i
         iteValue sym b val (lookupSeqMap vs i)

updateFrontSym sym _len _eltTy vs (Right wv) val =
  case wv of
    WordVal w | Just j <- SBV.svAsInteger w ->
      return $ updateSeqMap vs j val
    _ ->
      return $ IndexSeqMap $ \i ->
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

updateFrontSym_word sym (Nat _) eltTy (LargeBitsVal n bv) idx val =
  LargeBitsVal n <$> updateFrontSym sym (Nat n) eltTy bv idx val

updateFrontSym_word sym (Nat n) eltTy (WordVal bv) (Left idx) val =
  do idx' <- wordFromInt sym n idx
     updateFrontSym_word sym (Nat n) eltTy (WordVal bv) (Right (WordVal idx')) val

updateFrontSym_word sym (Nat n) eltTy bv (Right wv) val =
  case wv of
    WordVal idx
      | Just j <- SBV.svAsInteger idx ->
          updateWordValue sym bv j (fromVBit <$> val)

      | WordVal bw <- bv ->
        WordVal <$>
          do b <- fromVBit <$> val
             let sz   = SBV.intSizeOf bw
             let z    = literalSWord sz 0
             let znot = SBV.svNot z
             let q    = SBV.svSymbolicMerge (SBV.kindOf bw) True b znot z
             let msk  = SBV.svShiftRight (literalSWord sz (bit (sz-1))) idx
             let bw'  = SBV.svAnd bw (SBV.svNot msk)
             return $! SBV.svXOr bw' (SBV.svAnd q msk)

    _ -> LargeBitsVal n <$> updateFrontSym sym (Nat n) eltTy (asBitsMap sym bv) (Right wv) val


updateBackSym ::
  SBV ->
  Nat' ->
  TValue ->
  SeqMap SBV ->
  Either (SInteger SBV) (WordValue SBV) ->
  SEval SBV (GenValue SBV) ->
  SEval SBV (SeqMap SBV)
updateBackSym _ Inf _ _ _ _ = evalPanic "Expected finite sequence" ["updateBackSym"]

updateBackSym sym (Nat n) _eltTy vs (Left idx) val =
  case SBV.svAsInteger idx of
    Just i -> return $ updateSeqMap vs (n - 1 - i) val
    Nothing -> return $ IndexSeqMap $ \i ->
      do b <- intEq sym idx =<< integerLit sym (n - 1 - i)
         iteValue sym b val (lookupSeqMap vs i)

updateBackSym sym (Nat n) _eltTy vs (Right wv) val =
  case wv of
    WordVal w | Just j <- SBV.svAsInteger w ->
      return $ updateSeqMap vs (n - 1 - j) val
    _ ->
      return $ IndexSeqMap $ \i ->
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

updateBackSym_word sym (Nat _) eltTy (LargeBitsVal n bv) idx val =
  LargeBitsVal n <$> updateBackSym sym (Nat n) eltTy bv idx val

updateBackSym_word sym (Nat n) eltTy (WordVal bv) (Left idx) val =
  do idx' <- wordFromInt sym n idx
     updateBackSym_word sym (Nat n) eltTy (WordVal bv) (Right (WordVal idx')) val

updateBackSym_word sym (Nat n) eltTy bv (Right wv) val = do
  case wv of
    WordVal idx
      | Just j <- SBV.svAsInteger idx ->
          updateWordValue sym bv (n - 1 - j) (fromVBit <$> val)

      | WordVal bw <- bv ->
        WordVal <$>
          do b <- fromVBit <$> val
             let sz   = SBV.intSizeOf bw
             let z    = literalSWord sz 0
             let znot = SBV.svNot z
             let q    = SBV.svSymbolicMerge (SBV.kindOf bw) True b znot z
             let msk  = SBV.svShiftLeft (literalSWord sz 1) idx
             let bw'  = SBV.svAnd bw (SBV.svNot msk)
             return $! SBV.svXOr bw' (SBV.svAnd q msk)

    _ -> LargeBitsVal n <$> updateBackSym sym (Nat n) eltTy (asBitsMap sym bv) (Right wv) val


asWordList :: [WordValue SBV] -> Maybe [SWord SBV]
asWordList = go id
 where go :: ([SWord SBV] -> [SWord SBV]) -> [WordValue SBV] -> Maybe [SWord SBV]
       go f [] = Just (f [])
       go f (WordVal x :vs) = go (f . (x:)) vs
       go _f (LargeBitsVal _ _ : _) = Nothing

sshrV :: SBV -> Prim SBV
sshrV sym =
  PNumPoly \n ->
  PTyPoly  \ix ->
  PWordFun \x ->
  PStrictFun \y ->
  PPrim $
   asIndex sym ">>$" ix y >>= \case
     Left idx ->
       do let w = toInteger (SBV.intSizeOf x)
          let pneg = svLessThan idx (svInteger KUnbounded 0)
          zneg <- shl x  . svFromInteger w <$> shiftShrink sym n ix (SBV.svUNeg idx)
          zpos <- ashr x . svFromInteger w <$> shiftShrink sym n ix idx
          let z = svSymbolicMerge (kindOf x) True pneg zneg zpos
          return . VWord w . pure . WordVal $ z

     Right wv ->
       do z <- ashr x <$> asWordVal sym wv
          return . VWord (toInteger (SBV.intSizeOf x)) . pure . WordVal $ z
