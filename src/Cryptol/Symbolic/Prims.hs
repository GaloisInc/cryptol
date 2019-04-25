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

instance EvalPrims SBool SWord SInteger where
  evalPrim Decl { dName = n, .. } =
    do prim <- asPrim n
       Map.lookup prim primTable

  iteValue b x1 x2
    | Just b' <- SBV.svAsBool b = if b' then x1 else x2
    | otherwise = do v1 <- x1
                     v2 <- x2
                     iteSValue b v1 v2

-- See also Cryptol.Prims.Eval.primTable
primTable :: Map.Map Ident Value
primTable  = Map.fromList $ map (\(n, v) -> (mkIdent (T.pack n), v))
  [ ("True"        , VBit SBV.svTrue)
  , ("False"       , VBit SBV.svFalse)
  , ("number"      , ecNumberV) -- Converts a numeric type into its corresponding value.
                                -- { val, rep } (Literal val rep) => rep
  , ("+"           , binary (arithBinary (liftBinArith SBV.svPlus) (liftBin SBV.svPlus)
                             sModAdd)) -- {a} (Arith a) => a -> a -> a
  , ("-"           , binary (arithBinary (liftBinArith SBV.svMinus) (liftBin SBV.svMinus)
                             sModSub)) -- {a} (Arith a) => a -> a -> a
  , ("*"           , binary (arithBinary (liftBinArith SBV.svTimes) (liftBin SBV.svTimes)
                             sModMult)) -- {a} (Arith a) => a -> a -> a
  , ("/"           , binary (arithBinary (liftBinArith SBV.svQuot) (liftBin SBV.svQuot)
                             (liftModBin SBV.svQuot))) -- {a} (Arith a) => a -> a -> a
  , ("%"           , binary (arithBinary (liftBinArith SBV.svRem) (liftBin SBV.svRem)
                             (liftModBin SBV.svRem))) -- {a} (Arith a) => a -> a -> a
  , ("^^"          , binary (arithBinary sExp (liftBin SBV.svExp)
                             sModExp)) -- {a} (Arith a) => a -> a -> a
  , ("lg2"         , unary (arithUnary sLg2 svLg2 svModLg2)) -- {a} (Arith a) => a -> a
  , ("negate"      , unary (arithUnary (\_ -> ready . SBV.svUNeg) (ready . SBV.svUNeg)
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
  , ("/$"          , binary (arithBinary (liftBinArith signedQuot) (liftBin SBV.svQuot)
                             (liftModBin SBV.svQuot))) -- {a} (Arith a) => a -> a -> a
  , ("%$"          , binary (arithBinary (liftBinArith signedRem) (liftBin SBV.svRem)
                             (liftModBin SBV.svRem)))
  , (">>$"         , sshrV)
  , ("&&"          , binary (logicBinary SBV.svAnd SBV.svAnd))
  , ("||"          , binary (logicBinary SBV.svOr SBV.svOr))
  , ("^"           , binary (logicBinary SBV.svXOr SBV.svXOr))
  , ("complement"  , unary (logicUnary SBV.svNot SBV.svNot))
  , ("zero"        , tlam zeroV)
  , ("toInteger"   , ecToIntegerV)
  , ("fromInteger" , ecFromIntegerV (const id))
  , ("fromZ"      , nlam $ \ modulus ->
                    lam  $ \ x -> do
                      val <- x
                      case (modulus, val) of
                        (Nat n, VInteger i) -> return $ VInteger (SBV.svRem i (integerLit n))
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

  , ("carry"      , liftWord carry)
  , ("scarry"     , liftWord scarry)

  , ("#"          , -- {a,b,d} (fin a) => [a] d -> [b] d -> [a + b] d
     nlam $ \ front ->
     nlam $ \ back  ->
     tlam $ \ elty  ->
     lam  $ \ l     -> return $
     lam  $ \ r     -> join (ccatV front back elty <$> l <*> r))

  , ("splitAt"    ,
     nlam $ \ front ->
     nlam $ \ back  ->
     tlam $ \ a     ->
     lam  $ \ x     ->
       splitAtV front back a =<< x)

  , ("join"       ,
     nlam $ \ parts ->
     nlam $ \ (finNat' -> each)  ->
     tlam $ \ a     ->
     lam  $ \ x     ->
       joinV parts each a =<< x)

  , ("split"       , ecSplitV)

  , ("reverse"    , nlam $ \_a ->
                    tlam $ \_b ->
                     lam $ \xs -> reverseV =<< xs)

  , ("transpose"  , nlam $ \a ->
                    nlam $ \b ->
                    tlam $ \c ->
                     lam $ \xs -> transposeV a b c =<< xs)

  , ("fromTo"      , fromToV)
  , ("fromThenTo"  , fromThenToV)
  , ("infFrom"     , infFromV)
  , ("infFromThen" , infFromThenV)

  , ("@"           , indexPrim indexFront_bits indexFront)
  , ("!"           , indexPrim indexBack_bits indexBack)

  , ("update"      , updatePrim updateFrontSym_word updateFrontSym)
  , ("updateEnd"   , updatePrim updateBackSym_word updateBackSym)

    -- {at,len} (fin len) => [len][8] -> at
  , ("error"       ,
      tlam $ \at ->
      nlam $ \(finNat' -> _len) ->
      VFun $ \_msg ->
        return $ zeroV at) -- error/undefined, is arbitrarily translated to 0

  , ("random"      ,
      tlam $ \a ->
      wlam $ \x ->
         case SBV.svAsInteger x of
           Just i  -> return $ randomV a i
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
shifter :: Monad m => (SBool -> a -> a -> a) -> (a -> Integer -> m a) -> a -> [SBool] -> m a
shifter mux op = go
  where
    go x [] = return x
    go x (b : bs) = do
      x' <- op x (2 ^ length bs)
      go (mux b x' x) bs

logicShift :: String
           -> (SWord -> SWord -> SWord)
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
                 WordVal x' -> WordVal . wop x' <$> asWordVal idx
                 BitsVal bs0 ->
                   do idx_bits <- enumerateWordValue idx
                      let op bs shft = return $ Seq.fromFunction (Seq.length bs) $ \i ->
                                             case reindex (Nat w) (toInteger i) shft of
                                               Nothing -> return $ bitLit False
                                               Just i' -> Seq.index bs (fromInteger i')
                      BitsVal <$> shifter (mergeBits True) op bs0 idx_bits
                 LargeBitsVal n bs0 ->
                   do idx_bits <- enumerateWordValue idx
                      let op bs shft = memoMap $ IndexSeqMap $ \i ->
                                         case reindex (Nat w) i shft of
                                           Nothing -> return $ VBit $ bitLit False
                                           Just i' -> lookupSeqMap bs i'
                      LargeBitsVal n <$> shifter (mergeSeqMap True) op bs0 idx_bits

          VSeq w vs0 ->
             do idx_bits <- enumerateWordValue idx
                let op vs shft = memoMap $ IndexSeqMap $ \i ->
                                   case reindex (Nat w) i shft of
                                     Nothing -> return $ zeroV a
                                     Just i' -> lookupSeqMap vs i'
                VSeq w <$> shifter (mergeSeqMap True) op vs0 idx_bits

          VStream vs0 ->
             do idx_bits <- enumerateWordValue idx
                let op vs shft = memoMap $ IndexSeqMap $ \i ->
                                   case reindex Inf i shft of
                                     Nothing -> return $ zeroV a
                                     Just i' -> lookupSeqMap vs i'
                VStream <$> shifter (mergeSeqMap True) op vs0 idx_bits

          _ -> evalPanic "expected sequence value in shift operation" [nm]


indexFront :: Maybe Integer
           -> TValue
           -> SeqMap SBool SWord SInteger
           -> SWord
           -> Eval Value
indexFront mblen a xs idx
  | Just i <- SBV.svAsInteger idx
  = lookupSeqMap xs i

  | Just n <- mblen
  , TVSeq wlen TVBit <- a
  = do wvs <- traverse (fromWordVal "indexFront" =<<) (enumerateSeqMap n xs)
       case asWordList wvs of
         Just ws ->
           return $ VWord wlen $ ready $ WordVal $ SBV.svSelect ws (wordLit wlen 0) idx
         Nothing -> foldr f def idxs

  | otherwise
  = foldr f def idxs

 where
    k = SBV.kindOf idx
    w = SBV.intSizeOf idx
    def = ready $ zeroV a
    f n y = iteValue (SBV.svEqual idx (SBV.svInteger k n)) (lookupSeqMap xs n) y
    idxs = case mblen of
      Just n | n < 2^w -> [0 .. n-1]
      _ -> [0 .. 2^w - 1]


indexBack :: Maybe Integer
          -> TValue
          -> SeqMap SBool SWord SInteger
          -> SWord
          -> Eval Value
indexBack (Just n) a xs idx = indexFront (Just n) a (reverseSeqMap n xs) idx
indexBack Nothing _ _ _ = evalPanic "Expected finite sequence" ["indexBack"]

indexFront_bits :: Maybe Integer
                -> TValue
                -> SeqMap SBool SWord SInteger
                -> Seq.Seq SBool
                -> Eval Value
indexFront_bits mblen a xs bits0 = go 0 (length bits0) (Fold.toList bits0)
 where
  go :: Integer -> Int -> [SBool] -> Eval Value
  go i _k []
    -- For indices out of range, return 0 arbitrarily
    | Just n <- mblen
    , i >= n
    = return $ zeroV a

    | otherwise
    = lookupSeqMap xs i

  go i k (b:bs)
    | Just n <- mblen
    , (i `shiftL` k) >= n
    = return $ zeroV a

    | otherwise
    = iteValue b (go ((i `shiftL` 1) + 1) (k-1) bs)
                 (go  (i `shiftL` 1)      (k-1) bs)

indexBack_bits :: Maybe Integer
               -> TValue
               -> SeqMap SBool SWord SInteger
               -> Seq.Seq SBool
               -> Eval Value
indexBack_bits (Just n) a xs idx = indexFront_bits (Just n) a (reverseSeqMap n xs) idx
indexBack_bits Nothing _ _ _ = evalPanic "Expected finite sequence" ["indexBack_bits"]


-- | Compare a symbolic word value with a concrete integer.
wordValueEqualsInteger :: WordValue SBool SWord SInteger -> Integer -> Eval SBool
wordValueEqualsInteger wv i
  | wordValueSize wv < widthInteger i = return SBV.svFalse
  | otherwise =
    case wv of
      WordVal w -> return $ SBV.svEqual w (literalSWord (SBV.intSizeOf w) i)
      _ -> bitsAre i <$> enumerateWordValueRev wv -- little-endian
  where
    bitsAre :: Integer -> [SBool] -> SBool
    bitsAre n [] = SBV.svBool (n == 0)
    bitsAre n (b : bs) = SBV.svAnd (bitIs (odd n) b) (bitsAre (n `div` 2) bs)

    bitIs :: Bool -> SBool -> SBool
    bitIs b x = if b then x else SBV.svNot x

lazyMergeBit :: SBool -> Eval SBool -> Eval SBool -> Eval SBool
lazyMergeBit c x y =
  case SBV.svAsBool c of
    Just True -> x
    Just False -> y
    Nothing -> mergeBit False c <$> x <*> y

updateFrontSym
  :: Nat'
  -> TValue
  -> SeqMap SBool SWord SInteger
  -> WordValue SBool SWord SInteger
  -> Eval (GenValue SBool SWord SInteger)
  -> Eval (SeqMap SBool SWord SInteger)
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
         iteValue b val (lookupSeqMap vs i)

updateFrontSym_word
  :: Nat'
  -> TValue
  -> WordValue SBool SWord SInteger
  -> WordValue SBool SWord SInteger
  -> Eval (GenValue SBool SWord SInteger)
  -> Eval (WordValue SBool SWord SInteger)
updateFrontSym_word Inf _ _ _ _ = evalPanic "Expected finite sequence" ["updateFrontSym_bits"]
updateFrontSym_word (Nat n) eltTy bv wv val =
  case wv of
    WordVal w | Just j <- SBV.svAsInteger w ->
      do unless (j < n) (invalidIndex j)
         updateWordValue bv j (fromVBit <$> val)
    _ ->
      case bv of
        WordVal bw -> return $ BitsVal $ Seq.mapWithIndex f bs
                        where bs = fmap return $ Seq.fromList $ unpackWord bw
        BitsVal bs -> return $ BitsVal $ Seq.mapWithIndex f bs
        LargeBitsVal l vs -> LargeBitsVal l <$> updateFrontSym (Nat n) eltTy vs wv val
  where
    f :: Int -> Eval SBool -> Eval SBool
    f i x = do c <- wordValueEqualsInteger wv (toInteger i)
               lazyMergeBit c (fromBit =<< val) x

updateBackSym
  :: Nat'
  -> TValue
  -> SeqMap SBool SWord SInteger
  -> WordValue SBool SWord SInteger
  -> Eval (GenValue SBool SWord SInteger)
  -> Eval (SeqMap SBool SWord SInteger)
updateBackSym Inf _ _ _ _ = evalPanic "Expected finite sequence" ["updateBackSym"]
updateBackSym (Nat n) _eltTy vs wv val =
  case wv of
    WordVal w | Just j <- SBV.svAsInteger w ->
      do unless (j < n) (invalidIndex j)
         return $ updateSeqMap vs (n - 1 - j) val
    _ ->
      return $ IndexSeqMap $ \i ->
      do b <- wordValueEqualsInteger wv (n - 1 - i)
         iteValue b val (lookupSeqMap vs i)

updateBackSym_word
  :: Nat'
  -> TValue
  -> WordValue SBool SWord SInteger
  -> WordValue SBool SWord SInteger
  -> Eval (GenValue SBool SWord SInteger)
  -> Eval (WordValue SBool SWord SInteger)
updateBackSym_word Inf _ _ _ _ = evalPanic "Expected finite sequence" ["updateBackSym_bits"]
updateBackSym_word (Nat n) eltTy bv wv val = do
  case wv of
    WordVal w | Just j <- SBV.svAsInteger w ->
      do unless (j < n) (invalidIndex j)
         updateWordValue bv (n - 1 - j) (fromVBit <$> val)
    _ ->
      case bv of
        WordVal bw -> return $ BitsVal $ Seq.mapWithIndex f bs
                        where bs = fmap return $ Seq.fromList $ unpackWord bw
        BitsVal bs -> return $ BitsVal $ Seq.mapWithIndex f bs
        LargeBitsVal l vs -> LargeBitsVal l <$> updateBackSym (Nat n) eltTy vs wv val
  where
    f :: Int -> Eval SBool -> Eval SBool
    f i x = do c <- wordValueEqualsInteger wv (n - 1 - toInteger i)
               lazyMergeBit c (fromBit =<< val) x

asBitList :: [Eval SBool] -> Maybe [SBool]
asBitList = go id
 where go :: ([SBool] -> [SBool]) -> [Eval SBool] -> Maybe [SBool]
       go f [] = Just (f [])
       go f (Ready b:vs) = go (f . (b:)) vs
       go _ _ = Nothing


asWordList :: [WordValue SBool SWord SInteger] -> Maybe [SWord]
asWordList = go id
 where go :: ([SWord] -> [SWord]) -> [WordValue SBool SWord SInteger] -> Maybe [SWord]
       go f [] = Just (f [])
       go f (WordVal x :vs) = go (f . (x:)) vs
       go f (BitsVal bs:vs) =
              case asBitList (Fold.toList bs) of
                  Just xs -> go (f . (packWord xs:)) vs
                  Nothing -> Nothing
       go _f (LargeBitsVal _ _ : _) = Nothing

liftBinArith :: (SWord -> SWord -> SWord) -> BinArith SWord
liftBinArith op _ x y = ready $ op x y

liftBin :: (a -> b -> c) -> a -> b -> Eval c
liftBin op x y = ready $ op x y

liftModBin :: (SInteger -> SInteger -> a) -> Integer -> SInteger -> SInteger -> Eval a
liftModBin op modulus x y = ready $ op (SBV.svRem x m) (SBV.svRem y m)
  where m = integerLit modulus

sExp :: Integer -> SWord -> SWord -> Eval SWord
sExp _w x y = ready $ go (reverse (unpackWord y)) -- bits in little-endian order
  where go []       = literalSWord (SBV.intSizeOf x) 1
        go (b : bs) = SBV.svIte b (SBV.svTimes x s) s
            where a = go bs
                  s = SBV.svTimes a a

sModAdd :: Integer -> SInteger -> SInteger -> Eval SInteger
sModAdd modulus x y =
  case (SBV.svAsInteger x, SBV.svAsInteger y) of
    (Just i, Just j) -> ready $ integerLit ((i + j) `mod` modulus)
    _                -> ready $ SBV.svPlus x y

sModSub :: Integer -> SInteger -> SInteger -> Eval SInteger
sModSub modulus x y =
  case (SBV.svAsInteger x, SBV.svAsInteger y) of
    (Just i, Just j) -> ready $ integerLit ((i - j) `mod` modulus)
    _                -> ready $ SBV.svMinus x y

sModMult :: Integer -> SInteger -> SInteger -> Eval SInteger
sModMult modulus x y =
  case (SBV.svAsInteger x, SBV.svAsInteger y) of
    (Just i, Just j) -> ready $ integerLit ((i * j) `mod` modulus)
    _                -> ready $ SBV.svTimes x y

sModExp :: Integer -> SInteger -> SInteger -> Eval SInteger
sModExp modulus x y = ready $ SBV.svExp x (SBV.svRem y m)
  where m = integerLit modulus

-- | Ceiling (log_2 x)
sLg2 :: Integer -> SWord -> Eval SWord
sLg2 _w x = ready $ go 0
  where
    lit n = literalSWord (SBV.intSizeOf x) n
    go i | i < SBV.intSizeOf x = SBV.svIte (SBV.svLessEq x (lit (2^i))) (lit (toInteger i)) (go (i + 1))
         | otherwise           = lit (toInteger i)

-- | Ceiling (log_2 x)
svLg2 :: SInteger -> Eval SInteger
svLg2 x =
  case SBV.svAsInteger x of
    Just n -> ready $ SBV.svInteger SBV.KUnbounded (lg2 n)
    Nothing -> evalPanic "cannot compute lg2 of symbolic unbounded integer" []

svModLg2 :: Integer -> SInteger -> Eval SInteger
svModLg2 modulus x = svLg2 (SBV.svRem x m)
  where m = integerLit modulus

-- Cmp -------------------------------------------------------------------------

cmpEq :: SWord -> SWord -> Eval SBool -> Eval SBool
cmpEq x y k = SBV.svAnd (SBV.svEqual x y) <$> k

cmpNotEq :: SWord -> SWord -> Eval SBool -> Eval SBool
cmpNotEq x y k = SBV.svOr (SBV.svNotEqual x y) <$> k

cmpSignedLt :: SWord -> SWord -> Eval SBool -> Eval SBool
cmpSignedLt x y k = SBV.svOr (SBV.svLessThan sx sy) <$> (cmpEq sx sy k)
  where sx = SBV.svSign x
        sy = SBV.svSign y

cmpLt, cmpGt :: SWord -> SWord -> Eval SBool -> Eval SBool
cmpLt x y k = SBV.svOr (SBV.svLessThan x y) <$> (cmpEq x y k)
cmpGt x y k = SBV.svOr (SBV.svGreaterThan x y) <$> (cmpEq x y k)

cmpLtEq, cmpGtEq :: SWord -> SWord -> Eval SBool -> Eval SBool
cmpLtEq x y k = SBV.svAnd (SBV.svLessEq x y) <$> (cmpNotEq x y k)
cmpGtEq x y k = SBV.svAnd (SBV.svGreaterEq x y) <$> (cmpNotEq x y k)

cmpMod ::
  (SInteger -> SInteger -> Eval SBool -> Eval SBool) ->
  (Integer -> SInteger -> SInteger -> Eval SBool -> Eval SBool)
cmpMod cmp modulus x y k = cmp (SBV.svRem x m) (SBV.svRem y m) k
  where m = integerLit modulus

cmpModEq :: Integer -> SInteger -> SInteger -> Eval SBool -> Eval SBool
cmpModEq m x y k = SBV.svAnd (svDivisible m (SBV.svMinus x y)) <$> k

cmpModNotEq :: Integer -> SInteger -> SInteger -> Eval SBool -> Eval SBool
cmpModNotEq m x y k = SBV.svOr (SBV.svNot (svDivisible m (SBV.svMinus x y))) <$> k

svDivisible :: Integer -> SInteger -> SBool
svDivisible m x = SBV.svEqual (SBV.svRem x (integerLit m)) (integerLit 0)

cmpBinary :: (SBool -> SBool -> Eval SBool -> Eval SBool)
          -> (SWord -> SWord -> Eval SBool -> Eval SBool)
          -> (SInteger -> SInteger -> Eval SBool -> Eval SBool)
          -> (Integer -> SInteger -> SInteger -> Eval SBool -> Eval SBool)
          -> SBool -> Binary SBool SWord SInteger
cmpBinary fb fw fi fz b ty v1 v2 = VBit <$> cmpValue fb fw fi fz ty v1 v2 (return b)

-- Signed arithmetic -----------------------------------------------------------

signedQuot :: SWord -> SWord -> SWord
signedQuot x y = SBV.svUnsign (SBV.svQuot (SBV.svSign x) (SBV.svSign y))

signedRem :: SWord -> SWord -> SWord
signedRem x y = SBV.svUnsign (SBV.svRem (SBV.svSign x) (SBV.svSign y))


sshrV :: Value
sshrV =
  nlam $ \_n ->
  nlam $ \_k ->
  wlam $ \x -> return $
  wlam $ \y ->
   case SBV.svAsInteger y of
     Just i ->
       let z = SBV.svUnsign (SBV.svShr (SBV.svSign x) (fromInteger i))
        in return . VWord (toInteger (SBV.intSizeOf x)) . ready . WordVal $ z
     Nothing ->
       let z = SBV.svUnsign (SBV.svShiftRight (SBV.svSign x) y)
        in return . VWord (toInteger (SBV.intSizeOf x)) . ready . WordVal $ z

carry :: SWord -> SWord -> Eval Value
carry x y = return $ VBit c
 where
  c = SBV.svLessThan (SBV.svPlus x y) x

scarry :: SWord -> SWord -> Eval Value
scarry x y = return $ VBit sc
 where
  n = SBV.intSizeOf x
  z = SBV.svPlus (SBV.svSign x) (SBV.svSign y)
  xsign = SBV.svTestBit x (n-1)
  ysign = SBV.svTestBit y (n-1)
  zsign = SBV.svTestBit z (n-1)
  sc = SBV.svAnd (SBV.svEqual xsign ysign) (SBV.svNotEqual xsign zsign)
