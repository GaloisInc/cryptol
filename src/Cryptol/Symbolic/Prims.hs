-- |
-- Module      :  Cryptol.Symbolic.Prims
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Cryptol.Symbolic.Prims where

import Control.Monad (unless)
import Data.Bits
import qualified Data.Sequence as Seq
import qualified Data.Foldable as Fold

import Cryptol.Eval.Monad (Eval(..), ready, invalidIndex, cryUserError)
import Cryptol.Eval.Type  (finNat', TValue(..))
import Cryptol.Eval.Value (BitWord(..), EvalPrims(..), enumerateSeqMap, SeqMap(..),
                          reverseSeqMap, wlam, nlam, WordValue(..),
                          asWordVal, fromWordVal, fromBit,
                          enumerateWordValue, enumerateWordValueRev,
                          wordValueSize,
                          updateWordValue,
                          updateSeqMap, lookupSeqMap, memoMap )
import Cryptol.Prims.Eval (binary, unary, arithUnary,
                           arithBinary, Binary, BinArith,
                           logicBinary, logicUnary, zeroV,
                           ccatV, splitAtV, joinV, ecSplitV,
                           reverseV, infFromV, infFromThenV,
                           fromToV, fromThenToV,
                           transposeV, indexPrim,
                           ecToIntegerV, ecFromIntegerV,
                           ecNumberV, updatePrim, randomV, liftWord,
                           cmpValue, lg2)
import Cryptol.Symbolic.Value
import Cryptol.TypeCheck.AST (Decl(..))
import Cryptol.TypeCheck.Solver.InfNat (Nat'(..), widthInteger)
import Cryptol.ModuleSystem.Name (asPrim)
import Cryptol.Utils.Ident (Ident,mkIdent)

import qualified Data.SBV         as SBV
import qualified Data.SBV.Dynamic as SBV
import qualified Data.Map as Map
import qualified Data.Text as T

import Prelude ()
import Prelude.Compat
import Control.Monad (join)

traverseSnd :: Functor f => (a -> f b) -> (t, a) -> f (t, b)
traverseSnd f (x, y) = (,) x <$> f y

-- Primitives ------------------------------------------------------------------

instance EvalPrims SBV where
  evalPrim Decl { dName = n, .. } =
    do prim <- asPrim n
       Map.lookup prim primTable

  iteValue _ b x1 x2
    | Just b' <- SBV.svAsBool b = if b' then x1 else x2
    | otherwise = do v1 <- x1
                     v2 <- x2
                     iteSValue b v1 v2

-- See also Cryptol.Prims.Eval.primTable
primTable :: Map.Map Ident Value
primTable  = Map.fromList $ map (\(n, v) -> (mkIdent (T.pack n), v))
  [ ("True"        , VBit SBV.svTrue)
  , ("False"       , VBit SBV.svFalse)
  , ("number"      , ecNumberV SBV) -- Converts a numeric type into its corresponding value.
                                   -- { val, rep } (Literal val rep) => rep
  , ("+"           , binary (arithBinary SBV (liftBinArith SBV.svPlus) (liftBin SBV.svPlus)
                             sModAdd)) -- {a} (Arith a) => a -> a -> a
  , ("-"           , binary (arithBinary SBV (liftBinArith SBV.svMinus) (liftBin SBV.svMinus)
                             sModSub)) -- {a} (Arith a) => a -> a -> a
  , ("*"           , binary (arithBinary SBV (liftBinArith SBV.svTimes) (liftBin SBV.svTimes)
                             sModMult)) -- {a} (Arith a) => a -> a -> a
  , ("/"           , binary (arithBinary SBV (liftBinArith SBV.svQuot) (liftBin SBV.svQuot)
                             (liftModBin SBV.svQuot))) -- {a} (Arith a) => a -> a -> a
  , ("%"           , binary (arithBinary SBV (liftBinArith SBV.svRem) (liftBin SBV.svRem)
                             (liftModBin SBV.svRem))) -- {a} (Arith a) => a -> a -> a
  , ("^^"          , binary (arithBinary SBV sExp (liftBin SBV.svExp)
                             sModExp)) -- {a} (Arith a) => a -> a -> a
  , ("lg2"         , unary (arithUnary SBV sLg2 svLg2 svModLg2)) -- {a} (Arith a) => a -> a
  , ("negate"      , unary (arithUnary SBV (\_ -> ready . SBV.svUNeg) (ready . SBV.svUNeg)
                            (const (ready . SBV.svUNeg))))
  , ("<"           , binary (cmpBinary cmpLt cmpLt cmpLt (cmpMod cmpLt) SBV.svFalse))
  , (">"           , binary (cmpBinary cmpGt cmpGt cmpGt (cmpMod cmpGt) SBV.svFalse))
  , ("<="          , binary (cmpBinary cmpLtEq cmpLtEq cmpLtEq (cmpMod cmpLtEq) SBV.svTrue))
  , (">="          , binary (cmpBinary cmpGtEq cmpGtEq cmpGtEq (cmpMod cmpGtEq) SBV.svTrue))
  , ("=="          , binary (cmpBinary cmpEq cmpEq cmpEq cmpModEq SBV.svTrue))
  , ("!="          , binary (cmpBinary cmpNotEq cmpNotEq cmpNotEq cmpModNotEq SBV.svFalse))
  , ("<$"          , let boolFail = evalPanic "<$" ["Attempted signed comparison on bare Bit values"]
                         intFail = evalPanic "<$" ["Attempted signed comparison on Integer values"]
                      in binary (cmpBinary boolFail cmpSignedLt intFail (const intFail) SBV.svFalse))
  , ("/$"          , binary (arithBinary SBV (liftBinArith signedQuot) (liftBin SBV.svQuot)
                             (liftModBin SBV.svQuot))) -- {a} (Arith a) => a -> a -> a
  , ("%$"          , binary (arithBinary SBV (liftBinArith signedRem) (liftBin SBV.svRem)
                             (liftModBin SBV.svRem)))
  , (">>$"         , sshrV)
  , ("&&"          , binary (logicBinary SBV SBV.svAnd SBV.svAnd))
  , ("||"          , binary (logicBinary SBV SBV.svOr SBV.svOr))
  , ("^"           , binary (logicBinary SBV SBV.svXOr SBV.svXOr))
  , ("complement"  , unary (logicUnary SBV.svNot SBV.svNot))
  , ("zero"        , tlam (zeroV SBV))
  , ("toInteger"   , ecToIntegerV SBV)
  , ("fromInteger" , ecFromIntegerV SBV (const id))
  , ("fromZ"      , nlam $ \ modulus ->
                    lam  $ \ x -> do
                      val <- x
                      case (modulus, val) of
                        (Nat n, VInteger i) -> return $ VInteger (SBV.svRem i (integerLit SBV n))
                        _                   -> evalPanic "fromZ" ["Invalid arguments"])
  , ("<<"          , logicShift "<<"
                       SBV.svShiftLeft
                       (\sz i shft ->
                         case sz of
                           Inf             -> Just (i+shft)
                           Nat n
                             | i+shft >= n -> Nothing
                             | otherwise   -> Just (i+shft)))
  , (">>"          , logicShift ">>"
                       SBV.svShiftRight
                       (\_sz i shft ->
                          if i-shft < 0 then Nothing else Just (i-shft)))
  , ("<<<"         , logicShift "<<<"
                       SBV.svRotateLeft
                       (\sz i shft ->
                          case sz of
                            Inf -> evalPanic "cannot rotate infinite sequence" []
                            Nat n -> Just ((i+shft) `mod` n)))
  , (">>>"         , logicShift ">>>"
                       SBV.svRotateRight
                       (\sz i shft ->
                          case sz of
                            Inf -> evalPanic "cannot rotate infinite sequence" []
                            Nat n -> Just ((i+n-shft) `mod` n)))

  , ("carry"      , liftWord SBV carry)
  , ("scarry"     , liftWord SBV scarry)

  , ("#"          , -- {a,b,d} (fin a) => [a] d -> [b] d -> [a + b] d
     nlam $ \ front ->
     nlam $ \ back  ->
     tlam $ \ elty  ->
     lam  $ \ l     -> return $
     lam  $ \ r     -> join (ccatV SBV front back elty <$> l <*> r))

  , ("splitAt"    ,
     nlam $ \ front ->
     nlam $ \ back  ->
     tlam $ \ a     ->
     lam  $ \ x     ->
       splitAtV SBV front back a =<< x)

  , ("join"       ,
     nlam $ \ parts ->
     nlam $ \ (finNat' -> each)  ->
     tlam $ \ a     ->
     lam  $ \ x     ->
       joinV SBV parts each a =<< x)

  , ("split"       , ecSplitV SBV)

  , ("reverse"    , nlam $ \_a ->
                    tlam $ \_b ->
                     lam $ \xs -> reverseV SBV =<< xs)

  , ("transpose"  , nlam $ \a ->
                    nlam $ \b ->
                    tlam $ \c ->
                     lam $ \xs -> transposeV SBV a b c =<< xs)

  , ("fromTo"      , fromToV SBV)
  , ("fromThenTo"  , fromThenToV SBV)
  , ("infFrom"     , infFromV SBV)
  , ("infFromThen" , infFromThenV SBV)

  , ("@"           , indexPrim SBV indexFront_bits indexFront)
  , ("!"           , indexPrim SBV indexBack_bits indexBack)

  , ("update"      , updatePrim updateFrontSym_word updateFrontSym)
  , ("updateEnd"   , updatePrim updateBackSym_word updateBackSym)

    -- {at,len} (fin len) => [len][8] -> at
  , ("error"       ,
      tlam $ \at ->
      nlam $ \(finNat' -> _len) ->
      VFun $ \_msg ->
        return $ zeroV SBV at) -- error/undefined, is arbitrarily translated to 0

  , ("random"      ,
      tlam $ \a ->
      wlam SBV $ \x ->
         case SBV.svAsInteger x of
           Just i  -> return $ randomV SBV a i
           Nothing -> cryUserError "cannot evaluate 'random' with symbolic inputs")

     -- The trace function simply forces its first two
     -- values before returing the third in the symbolic
     -- evaluator.
  , ("trace",
      nlam $ \_n ->
      tlam $ \_a ->
      tlam $ \_b ->
       lam $ \s -> return $
       lam $ \x -> return $
       lam $ \y -> do
         _ <- s
         _ <- x
         y)
  ]


-- | Barrel-shifter algorithm. Takes a list of bits in big-endian order.
shifter :: Monad m => (SBit SBV -> a -> a -> a) -> (a -> Integer -> m a) -> a -> [SBit SBV] -> m a
shifter mux op = go
  where
    go x [] = return x
    go x (b : bs) = do
      x' <- op x (2 ^ length bs)
      go (mux b x' x) bs

logicShift :: String
           -> (SWord SBV -> SWord SBV -> SWord SBV)
           -> (Nat' -> Integer -> Integer -> Maybe Integer)
           -> Value
logicShift nm wop reindex =
      nlam $ \_m ->
      nlam $ \_n ->
      tlam $ \a ->
      VFun $ \xs -> return $
      VFun $ \y -> do
        idx <- fromWordVal "logicShift" =<< y

        xs >>= \case
          VWord w x ->
             return $ VWord w $ do
               x >>= \case
                 WordVal x' -> WordVal . wop x' <$> asWordVal SBV idx
                 BitsVal bs0 ->
                   do idx_bits <- enumerateWordValue SBV idx
                      let op bs shft = return $ Seq.fromFunction (Seq.length bs) $ \i ->
                                             case reindex (Nat w) (toInteger i) shft of
                                               Nothing -> return $ bitLit SBV False
                                               Just i' -> Seq.index bs (fromInteger i')
                      BitsVal <$> shifter (mergeBits True) op bs0 idx_bits
                 LargeBitsVal n bs0 ->
                   do idx_bits <- enumerateWordValue SBV idx
                      let op bs shft = memoMap $ IndexSeqMap $ \i ->
                                         case reindex (Nat w) i shft of
                                           Nothing -> return $ VBit $ bitLit SBV False
                                           Just i' -> lookupSeqMap bs i'
                      LargeBitsVal n <$> shifter (mergeSeqMap True) op bs0 idx_bits

          VSeq w vs0 ->
             do idx_bits <- enumerateWordValue SBV idx
                let op vs shft = memoMap $ IndexSeqMap $ \i ->
                                   case reindex (Nat w) i shft of
                                     Nothing -> return $ zeroV SBV a
                                     Just i' -> lookupSeqMap vs i'
                VSeq w <$> shifter (mergeSeqMap True) op vs0 idx_bits

          VStream vs0 ->
             do idx_bits <- enumerateWordValue SBV idx
                let op vs shft = memoMap $ IndexSeqMap $ \i ->
                                   case reindex Inf i shft of
                                     Nothing -> return $ zeroV SBV a
                                     Just i' -> lookupSeqMap vs i'
                VStream <$> shifter (mergeSeqMap True) op vs0 idx_bits

          _ -> evalPanic "expected sequence value in shift operation" [nm]


indexFront :: Maybe Integer
           -> TValue
           -> SeqMap SBV
           -> SWord SBV
           -> Eval Value
indexFront mblen a xs idx
  | Just i <- SBV.svAsInteger idx
  = lookupSeqMap xs i

  | Just n <- mblen
  , TVSeq wlen TVBit <- a
  = do wvs <- traverse (fromWordVal "indexFront" =<<) (enumerateSeqMap n xs)
       case asWordList wvs of
         Just ws ->
           return $ VWord wlen $ ready $ WordVal $ SBV.svSelect ws (wordLit SBV wlen 0) idx
         Nothing -> foldr f def idxs

  | otherwise
  = foldr f def idxs

 where
    k = SBV.kindOf idx
    w = SBV.intSizeOf idx
    def = ready $ zeroV SBV a
    f n y = iteValue SBV (SBV.svEqual idx (SBV.svInteger k n)) (lookupSeqMap xs n) y
    idxs = case mblen of
      Just n | n < 2^w -> [0 .. n-1]
      _ -> [0 .. 2^w - 1]


indexBack :: Maybe Integer
          -> TValue
          -> SeqMap SBV
          -> SWord SBV
          -> Eval Value
indexBack (Just n) a xs idx = indexFront (Just n) a (reverseSeqMap n xs) idx
indexBack Nothing _ _ _ = evalPanic "Expected finite sequence" ["indexBack"]

indexFront_bits :: Maybe Integer
                -> TValue
                -> SeqMap SBV
                -> Seq.Seq (SBit SBV)
                -> Eval Value
indexFront_bits mblen a xs bits0 = go 0 (length bits0) (Fold.toList bits0)
 where
  go :: Integer -> Int -> [SBit SBV] -> Eval Value
  go i _k []
    -- For indices out of range, return 0 arbitrarily
    | Just n <- mblen
    , i >= n
    = return $ zeroV SBV a

    | otherwise
    = lookupSeqMap xs i

  go i k (b:bs)
    | Just n <- mblen
    , (i `shiftL` k) >= n
    = return $ zeroV SBV a

    | otherwise
    = iteValue SBV b
         (go ((i `shiftL` 1) + 1) (k-1) bs)
         (go  (i `shiftL` 1)      (k-1) bs)

indexBack_bits :: Maybe Integer
               -> TValue
               -> SeqMap SBV
               -> Seq.Seq (SBit SBV)
               -> Eval Value
indexBack_bits (Just n) a xs idx = indexFront_bits (Just n) a (reverseSeqMap n xs) idx
indexBack_bits Nothing _ _ _ = evalPanic "Expected finite sequence" ["indexBack_bits"]


-- | Compare a symbolic word value with a concrete integer.
wordValueEqualsInteger :: WordValue SBV -> Integer -> Eval (SBit SBV)
wordValueEqualsInteger wv i
  | wordValueSize SBV wv < widthInteger i = return SBV.svFalse
  | otherwise =
    case wv of
      WordVal w -> return $ SBV.svEqual w (literalSWord (SBV.intSizeOf w) i)
      _ -> bitsAre i <$> enumerateWordValueRev SBV wv -- little-endian
  where
    bitsAre :: Integer -> [SBit SBV] -> SBit SBV
    bitsAre n [] = SBV.svBool (n == 0)
    bitsAre n (b : bs) = SBV.svAnd (bitIs (odd n) b) (bitsAre (n `div` 2) bs)

    bitIs :: Bool -> SBit SBV -> SBit SBV
    bitIs b x = if b then x else SBV.svNot x

lazyMergeBit :: SBit SBV -> Eval (SBit SBV) -> Eval (SBit SBV) -> Eval (SBit SBV)
lazyMergeBit c x y =
  case SBV.svAsBool c of
    Just True -> x
    Just False -> y
    Nothing -> mergeBit False c <$> x <*> y

updateFrontSym
  :: Nat'
  -> TValue
  -> SeqMap SBV
  -> WordValue SBV
  -> Eval (GenValue SBV)
  -> Eval (SeqMap SBV)
updateFrontSym len _eltTy vs wv val =
  case wv of
    WordVal w | Just j <- SBV.svAsInteger w ->
      do case len of
           Inf -> return ()
           Nat n -> unless (j < n) (invalidIndex j)
         return $ updateSeqMap vs j val
    _ ->
      return $ IndexSeqMap $ \i ->
      do b <- wordValueEqualsInteger wv i
         iteValue SBV b val (lookupSeqMap vs i)

updateFrontSym_word
  :: Nat'
  -> TValue
  -> WordValue SBV
  -> WordValue SBV
  -> Eval (GenValue SBV)
  -> Eval (WordValue SBV)
updateFrontSym_word Inf _ _ _ _ = evalPanic "Expected finite sequence" ["updateFrontSym_bits"]
updateFrontSym_word (Nat n) eltTy bv wv val =
  case wv of
    WordVal w | Just j <- SBV.svAsInteger w ->
      do unless (j < n) (invalidIndex j)
         updateWordValue SBV bv j (fromVBit <$> val)
    _ ->
      case bv of
        WordVal bw -> return $ BitsVal $ Seq.mapWithIndex f bs
                        where bs = fmap return $ Seq.fromList $ unpackWord SBV bw
        BitsVal bs -> return $ BitsVal $ Seq.mapWithIndex f bs
        LargeBitsVal l vs -> LargeBitsVal l <$> updateFrontSym (Nat n) eltTy vs wv val
  where
    f :: Int -> Eval (SBit SBV) -> Eval (SBit SBV)
    f i x = do c <- wordValueEqualsInteger wv (toInteger i)
               lazyMergeBit c (fromBit =<< val) x

updateBackSym
  :: Nat'
  -> TValue
  -> SeqMap SBV
  -> WordValue SBV
  -> Eval (GenValue SBV)
  -> Eval (SeqMap SBV)
updateBackSym Inf _ _ _ _ = evalPanic "Expected finite sequence" ["updateBackSym"]
updateBackSym (Nat n) _eltTy vs wv val =
  case wv of
    WordVal w | Just j <- SBV.svAsInteger w ->
      do unless (j < n) (invalidIndex j)
         return $ updateSeqMap vs (n - 1 - j) val
    _ ->
      return $ IndexSeqMap $ \i ->
      do b <- wordValueEqualsInteger wv (n - 1 - i)
         iteValue SBV b val (lookupSeqMap vs i)

updateBackSym_word
  :: Nat'
  -> TValue
  -> WordValue SBV
  -> WordValue SBV
  -> Eval (GenValue SBV)
  -> Eval (WordValue SBV)
updateBackSym_word Inf _ _ _ _ = evalPanic "Expected finite sequence" ["updateBackSym_bits"]
updateBackSym_word (Nat n) eltTy bv wv val = do
  case wv of
    WordVal w | Just j <- SBV.svAsInteger w ->
      do unless (j < n) (invalidIndex j)
         updateWordValue SBV bv (n - 1 - j) (fromVBit <$> val)
    _ ->
      case bv of
        WordVal bw -> return $ BitsVal $ Seq.mapWithIndex f bs
                        where bs = fmap return $ Seq.fromList $ unpackWord SBV bw
        BitsVal bs -> return $ BitsVal $ Seq.mapWithIndex f bs
        LargeBitsVal l vs -> LargeBitsVal l <$> updateBackSym (Nat n) eltTy vs wv val
  where
    f :: Int -> Eval (SBit SBV) -> Eval (SBit SBV)
    f i x = do c <- wordValueEqualsInteger wv (n - 1 - toInteger i)
               lazyMergeBit c (fromBit =<< val) x

asBitList :: [Eval (SBit SBV)] -> Maybe [SBit SBV]
asBitList = go id
 where go :: ([SBit SBV] -> [SBit SBV]) -> [Eval (SBit SBV)] -> Maybe [SBit SBV]
       go f [] = Just (f [])
       go f (Ready b:vs) = go (f . (b:)) vs
       go _ _ = Nothing


asWordList :: [WordValue SBV] -> Maybe [SWord SBV]
asWordList = go id
 where go :: ([SWord SBV] -> [SWord SBV]) -> [WordValue SBV] -> Maybe [SWord SBV]
       go f [] = Just (f [])
       go f (WordVal x :vs) = go (f . (x:)) vs
       go f (BitsVal bs:vs) =
              case asBitList (Fold.toList bs) of
                  Just xs -> go (f . (packWord SBV xs:)) vs
                  Nothing -> Nothing
       go _f (LargeBitsVal _ _ : _) = Nothing

liftBinArith :: (SWord SBV -> SWord SBV -> SWord SBV) -> BinArith SBV
liftBinArith op _ x y = ready $ op x y

liftBin :: (a -> b -> c) -> a -> b -> Eval c
liftBin op x y = ready $ op x y

liftModBin :: (SInteger SBV -> SInteger SBV -> a) -> Integer -> SInteger SBV -> SInteger SBV -> Eval a
liftModBin op modulus x y = ready $ op (SBV.svRem x m) (SBV.svRem y m)
  where m = integerLit SBV modulus

sExp :: Integer -> SWord SBV -> SWord SBV -> Eval (SWord SBV)
sExp _w x y = ready $ go (reverse (unpackWord SBV y)) -- bits in little-endian order
  where go []       = literalSWord (SBV.intSizeOf x) 1
        go (b : bs) = SBV.svIte b (SBV.svTimes x s) s
            where a = go bs
                  s = SBV.svTimes a a

sModAdd :: Integer -> SInteger SBV -> SInteger SBV -> Eval (SInteger SBV)
sModAdd modulus x y =
  case (SBV.svAsInteger x, SBV.svAsInteger y) of
    (Just i, Just j) -> ready $ integerLit SBV ((i + j) `mod` modulus)
    _                -> ready $ SBV.svPlus x y

sModSub :: Integer -> SInteger SBV -> SInteger SBV -> Eval (SInteger SBV)
sModSub modulus x y =
  case (SBV.svAsInteger x, SBV.svAsInteger y) of
    (Just i, Just j) -> ready $ integerLit SBV ((i - j) `mod` modulus)
    _                -> ready $ SBV.svMinus x y

sModMult :: Integer -> SInteger SBV -> SInteger SBV -> Eval (SInteger SBV)
sModMult modulus x y =
  case (SBV.svAsInteger x, SBV.svAsInteger y) of
    (Just i, Just j) -> ready $ integerLit SBV ((i * j) `mod` modulus)
    _                -> ready $ SBV.svTimes x y

sModExp :: Integer -> SInteger SBV -> SInteger SBV -> Eval (SInteger SBV)
sModExp modulus x y = ready $ SBV.svExp x (SBV.svRem y m)
  where m = integerLit SBV modulus

-- | Ceiling (log_2 x)
sLg2 :: Integer -> SWord SBV -> Eval (SWord SBV)
sLg2 _w x = ready $ go 0
  where
    lit n = literalSWord (SBV.intSizeOf x) n
    go i | i < SBV.intSizeOf x = SBV.svIte (SBV.svLessEq x (lit (2^i))) (lit (toInteger i)) (go (i + 1))
         | otherwise           = lit (toInteger i)

-- | Ceiling (log_2 x)
svLg2 :: SInteger SBV -> Eval (SInteger SBV)
svLg2 x =
  case SBV.svAsInteger x of
    Just n -> ready $ SBV.svInteger SBV.KUnbounded (lg2 n)
    Nothing -> evalPanic "cannot compute lg2 of symbolic unbounded integer" []

svModLg2 :: Integer -> SInteger SBV -> Eval (SInteger SBV)
svModLg2 modulus x = svLg2 (SBV.svRem x m)
  where m = integerLit SBV modulus

-- Cmp -------------------------------------------------------------------------

cmpEq :: SWord SBV -> SWord SBV -> Eval (SBit SBV) -> Eval (SBit SBV)
cmpEq x y k = SBV.svAnd (SBV.svEqual x y) <$> k

cmpNotEq :: SWord SBV -> SWord SBV -> Eval (SBit SBV) -> Eval (SBit SBV)
cmpNotEq x y k = SBV.svOr (SBV.svNotEqual x y) <$> k

cmpSignedLt :: SWord SBV -> SWord SBV -> Eval (SBit SBV) -> Eval (SBit SBV)
cmpSignedLt x y k = SBV.svOr (SBV.svLessThan sx sy) <$> (cmpEq sx sy k)
  where sx = SBV.svSign x
        sy = SBV.svSign y

cmpLt, cmpGt :: SWord SBV -> SWord SBV -> Eval (SBit SBV) -> Eval (SBit SBV)
cmpLt x y k = SBV.svOr (SBV.svLessThan x y) <$> (cmpEq x y k)
cmpGt x y k = SBV.svOr (SBV.svGreaterThan x y) <$> (cmpEq x y k)

cmpLtEq, cmpGtEq :: SWord SBV -> SWord SBV -> Eval (SBit SBV) -> Eval (SBit SBV)
cmpLtEq x y k = SBV.svAnd (SBV.svLessEq x y) <$> (cmpNotEq x y k)
cmpGtEq x y k = SBV.svAnd (SBV.svGreaterEq x y) <$> (cmpNotEq x y k)

cmpMod ::
  (SInteger SBV -> SInteger SBV -> Eval (SBit SBV) -> Eval (SBit SBV)) ->
  (Integer -> SInteger SBV -> SInteger SBV -> Eval (SBit SBV) -> Eval (SBit SBV))
cmpMod cmp modulus x y k = cmp (SBV.svRem x m) (SBV.svRem y m) k
  where m = integerLit SBV modulus

cmpModEq :: Integer -> SInteger SBV -> SInteger SBV -> Eval (SBit SBV) -> Eval (SBit SBV)
cmpModEq m x y k = SBV.svAnd (svDivisible m (SBV.svMinus x y)) <$> k

cmpModNotEq :: Integer -> SInteger SBV -> SInteger SBV -> Eval (SBit SBV) -> Eval (SBit SBV)
cmpModNotEq m x y k = SBV.svOr (SBV.svNot (svDivisible m (SBV.svMinus x y))) <$> k

svDivisible :: Integer -> SInteger SBV -> (SBit SBV)
svDivisible m x = SBV.svEqual (SBV.svRem x (integerLit SBV m)) (integerLit SBV 0)

cmpBinary :: (SBit SBV -> SBit SBV -> Eval (SBit SBV) -> Eval (SBit SBV))
          -> (SWord SBV -> SWord SBV -> Eval (SBit SBV) -> Eval (SBit SBV))
          -> (SInteger SBV -> SInteger SBV -> Eval (SBit SBV) -> Eval (SBit SBV))
          -> (Integer -> SInteger SBV -> SInteger SBV -> Eval (SBit SBV) -> Eval (SBit SBV))
          -> SBit SBV -> Binary SBV
cmpBinary fb fw fi fz b ty v1 v2 = VBit <$> cmpValue SBV fb fw fi fz ty v1 v2 (return b)

-- Signed arithmetic -----------------------------------------------------------

signedQuot :: SWord SBV -> SWord SBV -> SWord SBV
signedQuot x y = SBV.svUnsign (SBV.svQuot (SBV.svSign x) (SBV.svSign y))

signedRem :: SWord SBV -> SWord SBV -> SWord SBV
signedRem x y = SBV.svUnsign (SBV.svRem (SBV.svSign x) (SBV.svSign y))


sshrV :: Value
sshrV =
  nlam $ \_n ->
  nlam $ \_k ->
  wlam SBV $ \x -> return $
  wlam SBV $ \y ->
   case SBV.svAsInteger y of
     Just i ->
       let z = SBV.svUnsign (SBV.svShr (SBV.svSign x) (fromInteger i))
        in return . VWord (toInteger (SBV.intSizeOf x)) . ready . WordVal $ z
     Nothing ->
       let z = SBV.svUnsign (SBV.svShiftRight (SBV.svSign x) y)
        in return . VWord (toInteger (SBV.intSizeOf x)) . ready . WordVal $ z

carry :: SWord SBV -> SWord SBV -> Eval Value
carry x y = return $ VBit c
 where
  c = SBV.svLessThan (SBV.svPlus x y) x

scarry :: SWord SBV -> SWord SBV -> Eval Value
scarry x y = return $ VBit sc
 where
  n = SBV.intSizeOf x
  z = SBV.svPlus (SBV.svSign x) (SBV.svSign y)
  xsign = SBV.svTestBit x (n-1)
  ysign = SBV.svTestBit y (n-1)
  zsign = SBV.svTestBit z (n-1)
  sc = SBV.svAnd (SBV.svEqual xsign ysign) (SBV.svNotEqual xsign zsign)
