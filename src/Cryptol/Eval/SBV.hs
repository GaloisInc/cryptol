-- |
-- Module      :  Cryptol.Eval.SBV
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
module Cryptol.Eval.SBV
  ( SBV(..), Value
{-  , SBVResult(..), SBVEval(..)-}
  , evalPrim
  , forallBV_, existsBV_
  , forallSBool_, existsSBool_
  , forallSInteger_, existsSInteger_
  ) where

import           Control.Monad (join, unless)
import           Control.Monad.IO.Class (MonadIO(..))
import           Data.Bits (bit, complement, shiftL)
import qualified Data.Foldable as Fold
import           Data.List (foldl')
import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import qualified Data.Text as T

import Data.SBV (symbolicEnv)
import Data.SBV.Dynamic as SBV

import Cryptol.Eval.Type (TValue(..), finNat')
import Cryptol.Eval.Generic
import Cryptol.Eval.Monad
  ( Eval(..), cryUserError, invalidIndex, delay, blackhole, delayFill
  , EvalError
  )
import Cryptol.Eval.Value
import Cryptol.Eval.Concrete ( integerToChar, ppBV, BV(..) )
import Cryptol.Testing.Random( randomV )
import Cryptol.TypeCheck.Solver.InfNat (Nat'(..), widthInteger)
import Cryptol.Utils.Ident
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.PP

import Control.Monad.Trans  (liftIO)

-- SBool and SWord -------------------------------------------------------------

data SBV = SBV

fromBitsLE :: [SBit SBV] -> SWord SBV
fromBitsLE bs = foldl' f (literalSWord 0 0) bs
  where f w b = svJoin (svToWord1 b) w

literalSWord :: Int -> Integer -> SWord SBV
literalSWord w i = svInteger (KBounded False w) i

forallBV_ :: Int -> Symbolic (SWord SBV)
forallBV_ w = symbolicEnv >>= liftIO . svMkSymVar (Just ALL) (KBounded False w) Nothing

existsBV_ :: Int -> Symbolic (SWord SBV)
existsBV_ w = symbolicEnv >>= liftIO . svMkSymVar (Just EX) (KBounded False w) Nothing

forallSBool_ :: Symbolic (SBit SBV)
forallSBool_ = symbolicEnv >>= liftIO . svMkSymVar (Just ALL) KBool Nothing

existsSBool_ :: Symbolic (SBit SBV)
existsSBool_ = symbolicEnv >>= liftIO . svMkSymVar (Just EX) KBool Nothing

forallSInteger_ :: Symbolic (SBit SBV)
forallSInteger_ = symbolicEnv >>= liftIO . svMkSymVar (Just ALL) KUnbounded Nothing

existsSInteger_ :: Symbolic (SBit SBV)
existsSInteger_ = symbolicEnv >>= liftIO . svMkSymVar (Just EX) KUnbounded Nothing

-- Values ----------------------------------------------------------------------

type Value = GenValue SBV

-- Symbolic Conditionals -------------------------------------------------------

packSBV :: [SBit SBV] -> SWord SBV
packSBV bs = fromBitsLE (reverse bs)

unpackSBV :: SWord SBV -> [SBit SBV]
unpackSBV x = [ svTestBit x i | i <- reverse [0 .. intSizeOf x - 1] ]

{-
data SBVResult a
  = SBVError !EvalError
  | SBVResult !SVal !a -- safety predicate and result

instance Functor SBVResult where
  fmap _ (SBVError err) = SBVError err
  fmap f (SBVResult p x) = SBVResult p (f x)

instance Applicative SBVResult where
  pure = SBVResult svTrue
  SBVError err <*> _ = SBVError err
  _ <*> SBVError err = SBVError err
  SBVResult p1 f <*> SBVResult p2 x = SBVResult (svAnd p1 p2) (f x)

instance Monad SBVResult where
  return = pure
  SBVError err >>= _ = SBVError err
  SBVResult px x >>= m =
    case m x of
      SBVError err   -> SBVError err
      SBVResult pm z -> SBVResult (svAnd px pm) z


newtype SBVEval a = SBVEval{ sbvEval :: Eval (SBVResult a) }
  deriving (Functor)

instance Applicative SBVEval where
  pure = SBVEval . pure . pure
  f <*> x = SBVEval $
    do f' <- sbvEval f
       x' <- sbvEval x
       pure (f' <*> x')

instance Monad SBVEval where
  return = pure
  x >>= f = SBVEval $
    sbvEval x >>= \case
      SBVError err -> pure (SBVError err)
      SBVResult px x' ->
        sbvEval (f x') >>= \case
          SBVError err -> pure (SBVError err)
          SBVResult pz z -> pure (SBVResult (svAnd px pz) z)

instance MonadIO SBVEval where
  liftIO m = SBVEval $ fmap pure (liftIO m)
-}

-- Symbolic Big-endian Words -------------------------------------------------------

instance Backend SBV where
  type SBit SBV = SVal
  type SWord SBV = SVal
  type SInteger SBV = SVal
  type SEval SBV = Eval

  isReady _ (Ready _) = True
  isReady _ _ = False

  mergeEval _sym f c mx my =
    do x <- mx
       y <- my
       f c x y

  sDelay _ = delay
  sDeclareHole _ = blackhole
  sDelayFill _ = delayFill

--  type SEval SBV = SBVEval

{-
  isReady _ (SBVEval (Ready _)) = True
  isReady _ _ = False

  sDelay _ msg m = SBVEval $
    do m' <- delay msg (sbvEval m)
       pure (pure (SBVEval m'))

  sDelayFill _ m retry = SBVEval $
    do m' <- delayFill (sbvEval m) (sbvEval retry)
       pure (pure (SBVEval m'))

  sDeclareHole _ msg = SBVEval $
    do (hole, fill) <- blackhole msg
       return (pure (SBVEval hole, \m -> SBVEval (fmap pure (fill (sbvEval m)))))
-}

  wordLen _ v = toInteger (intSizeOf v)
  wordAsChar _ v = integerToChar <$> svAsInteger v

  ppBit _ v
     | Just b <- svAsBool v = text $! if b then "True" else "False"
     | otherwise            = text "?"
  ppWord _ opts v
     | Just x <- svAsInteger v = ppBV opts (BV (wordLen SBV v) x)
     | otherwise               = text "[?]"
  ppInteger _ _opts v
     | Just x <- svAsInteger v = integer x
     | otherwise               = text "[?]"

  bitAsLit _ b = svAsBool b

  bitLit _ b     = pure $! svBool b
  wordLit _ n x  = pure $! svInteger (KBounded False (fromInteger n)) x
  integerLit _ x = pure $! svInteger KUnbounded x

  wordBit _ x idx = pure $! svTestBit x (intSizeOf x - 1 - fromInteger idx)

  wordUpdate _ x idx b = pure $! svSymbolicMerge (kindOf x) False b wtrue wfalse
    where
     i' = intSizeOf x - 1 - fromInteger idx
     wtrue  = x `svOr`  svInteger (kindOf x) (bit i' :: Integer)
     wfalse = x `svAnd` svInteger (kindOf x) (complement (bit i' :: Integer))

  packWord _ bs  = pure $! packSBV bs
  unpackWord _ x = pure $! unpackSBV x

  joinWord _ x y = pure $! svJoin x y

  splitWord _ _leftW rightW w = pure
    ( svExtract (intSizeOf w - 1) (fromInteger rightW) w
    , svExtract (fromInteger rightW - 1) 0 w
    )

  extractWord _ len start w =
    pure $! svExtract (fromInteger start + fromInteger len - 1) (fromInteger start) w

  wordPlus  _ a b = pure $! svPlus a b
  wordMinus _ a b = pure $! svMinus a b
  wordMult  _ a b = pure $! svTimes a b

  intPlus  _ a b = pure $! svPlus a b
  intMinus _ a b = pure $! svMinus a b
  intMult  _ a b = pure $! svTimes a b

  intModPlus  _ m a b = sModAdd m a b
  intModMinus _ m a b = sModSub m a b
  intModMult  _ m a b = sModMult m a b

  wordToInt _ x = pure $! svToInteger x
  wordFromInt _ w i = pure $! svFromInteger w i

  iteBit _ b x y = pure $! svSymbolicMerge KBool True b x y
  iteWord _ b x y = pure $! svSymbolicMerge (kindOf x) True b x y
  iteInteger _ b x y = pure $! svSymbolicMerge KUnbounded True b x y


-- TODO: implement this properly in SBV using "bv2int"
svToInteger :: SWord SBV -> SInteger SBV
svToInteger w =
  case svAsInteger w of
    Nothing -> svFromIntegral KUnbounded w
    Just x  -> svInteger KUnbounded x

-- TODO: implement this properly in SBV using "int2bv"
svFromInteger :: Integer -> SInteger SBV -> SWord SBV
svFromInteger 0 _ = literalSWord 0 0
svFromInteger n i =
  case svAsInteger i of
    Nothing -> svFromIntegral (KBounded False (fromInteger n)) i
    Just x  -> literalSWord (fromInteger n) x

-- Errors ----------------------------------------------------------------------

evalPanic :: String -> [String] -> a
evalPanic cxt = panic ("[Symbolic]" ++ cxt)


-- Primitives ------------------------------------------------------------------

evalPrim :: Ident -> Maybe Value
evalPrim prim = Map.lookup prim primTable

-- See also Cryptol.Prims.Eval.primTable
primTable :: Map.Map Ident Value
primTable  = Map.fromList $ map (\(n, v) -> (mkIdent (T.pack n), v))
  [ ("True"        , VBit SBV.svTrue)
  , ("False"       , VBit SBV.svFalse)
  , ("number"      , ecNumberV SBV) -- Converts a numeric type into its corresponding value.
                                   -- { val, rep } (Literal val rep) => rep
  , ("+"           , binary (addV SBV)) -- {a} (Arith a) => a -> a -> a
  , ("-"           , binary (subV SBV)) -- {a} (Arith a) => a -> a -> a
  , ("*"           , binary (mulV SBV)) -- {a} (Arith a) => a -> a -> a
  , ("/"           , binary (arithBinary SBV (liftBinArith SBV.svQuot) (liftBin SBV.svQuot)
                             (liftModBin SBV.svQuot))) -- {a} (Arith a) => a -> a -> a
  , ("%"           , binary (arithBinary SBV (liftBinArith SBV.svRem) (liftBin SBV.svRem)
                             (liftModBin SBV.svRem))) -- {a} (Arith a) => a -> a -> a
  , ("^^"          , binary (arithBinary SBV sExp (liftBin SBV.svExp)
                             sModExp)) -- {a} (Arith a) => a -> a -> a
  , ("lg2"         , unary (arithUnary SBV sLg2 svLg2 svModLg2)) -- {a} (Arith a) => a -> a
  , ("negate"      , unary (arithUnary SBV (\_ -> pure . SBV.svUNeg) (pure . SBV.svUNeg)
                            (const (pure . SBV.svUNeg))))
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
  , ("&&"          , binary (logicBinary SBV (\x y -> pure $ SBV.svAnd x y) (\x y -> pure $ SBV.svAnd x y)))
  , ("||"          , binary (logicBinary SBV (\x y -> pure $ SBV.svOr x y) (\x y -> pure $ SBV.svOr x y)))
  , ("^"           , binary (logicBinary SBV (\x y -> pure $ SBV.svXOr x y) (\x y -> pure $ SBV.svXOr x y)))
  , ("complement"  , unary (logicUnary SBV SBV.svNot SBV.svNot))
  , ("zero"        , VPoly (zeroV SBV))
  , ("toInteger"   , ecToIntegerV SBV)
  , ("fromInteger" , ecFromIntegerV SBV (const id))
  , ("fromZ"      , nlam $ \ modulus ->
                    lam  $ \ x -> do
                      val <- x
                      case (modulus, val) of
                        (Nat n, VInteger i) -> VInteger . SBV.svRem i <$> integerLit SBV n
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

  , ("update"      , updatePrim SBV updateFrontSym_word updateFrontSym)
  , ("updateEnd"   , updatePrim SBV updateBackSym_word updateBackSym)

    -- {at,len} (fin len) => [len][8] -> at
  , ("error"       ,
      tlam $ \at ->
      nlam $ \(finNat' -> _len) ->
      VFun $ \_msg ->
        zeroV SBV at) -- error/undefined, is arbitrarily translated to 0

  , ("random"      ,
      tlam $ \a ->
      wlam SBV $ \x ->
         case SBV.svAsInteger x of
           Just i  -> randomV SBV a i
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
                 LargeBitsVal n bs0 ->
                   do idx_bits <- enumerateWordValue SBV idx
                      let op bs shft = memoMap $ IndexSeqMap $ \i ->
                                         case reindex (Nat w) i shft of
                                           Nothing -> VBit <$> bitLit SBV False
                                           Just i' -> lookupSeqMap bs i'
                      LargeBitsVal n <$> shifter (mergeSeqMap SBV) op bs0 idx_bits

          VSeq w vs0 ->
             do idx_bits <- enumerateWordValue SBV idx
                let op vs shft = memoMap $ IndexSeqMap $ \i ->
                                   case reindex (Nat w) i shft of
                                     Nothing -> zeroV SBV a
                                     Just i' -> lookupSeqMap vs i'
                VSeq w <$> shifter (mergeSeqMap SBV) op vs0 idx_bits

          VStream vs0 ->
             do idx_bits <- enumerateWordValue SBV idx
                let op vs shft = memoMap $ IndexSeqMap $ \i ->
                                   case reindex Inf i shft of
                                     Nothing -> zeroV SBV a
                                     Just i' -> lookupSeqMap vs i'
                VStream <$> shifter (mergeSeqMap SBV) op vs0 idx_bits

          _ -> evalPanic "expected sequence value in shift operation" [nm]


indexFront :: Maybe Integer
           -> TValue
           -> SeqMap SBV
           -> SWord SBV
           -> SEval SBV Value
indexFront mblen a xs idx
  | Just i <- SBV.svAsInteger idx
  = lookupSeqMap xs i

  | Just n <- mblen
  , TVSeq wlen TVBit <- a
  = do wvs <- traverse (fromWordVal "indexFront" =<<) (enumerateSeqMap n xs)
       case asWordList wvs of
         Just ws ->
           do z <- wordLit SBV wlen 0
              return $ VWord wlen $ pure $ WordVal $ SBV.svSelect ws z idx
         Nothing -> foldr f def idxs

  | otherwise
  = foldr f def idxs

 where
    k = SBV.kindOf idx
    w = SBV.intSizeOf idx
    def = zeroV SBV a
    f n y = iteValue SBV (SBV.svEqual idx (SBV.svInteger k n)) (lookupSeqMap xs n) y
    idxs = case mblen of
      Just n | n < 2^w -> [0 .. n-1]
      _ -> [0 .. 2^w - 1]


indexBack :: Maybe Integer
          -> TValue
          -> SeqMap SBV
          -> SWord SBV
          -> SEval SBV Value
indexBack (Just n) a xs idx = indexFront (Just n) a (reverseSeqMap n xs) idx
indexBack Nothing _ _ _ = evalPanic "Expected finite sequence" ["indexBack"]

indexFront_bits :: Maybe Integer
                -> TValue
                -> SeqMap SBV
                -> Seq.Seq (SBit SBV)
                -> SEval SBV Value
indexFront_bits mblen a xs bits0 = go 0 (length bits0) (Fold.toList bits0)
 where
  go :: Integer -> Int -> [SBit SBV] -> SEval SBV Value
  go i _k []
    -- For indices out of range, return 0 arbitrarily
    | Just n <- mblen
    , i >= n
    = zeroV SBV a

    | otherwise
    = lookupSeqMap xs i

  go i k (b:bs)
    | Just n <- mblen
    , (i `shiftL` k) >= n
    = zeroV SBV a

    | otherwise
    = iteValue SBV b
         (go ((i `shiftL` 1) + 1) (k-1) bs)
         (go  (i `shiftL` 1)      (k-1) bs)

indexBack_bits :: Maybe Integer
               -> TValue
               -> SeqMap SBV
               -> Seq.Seq (SBit SBV)
               -> SEval SBV Value
indexBack_bits (Just n) a xs idx = indexFront_bits (Just n) a (reverseSeqMap n xs) idx
indexBack_bits Nothing _ _ _ = evalPanic "Expected finite sequence" ["indexBack_bits"]


-- | Compare a symbolic word value with a concrete integer.
wordValueEqualsInteger :: WordValue SBV -> Integer -> SEval SBV (SBit SBV)
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


updateFrontSym
  :: Nat'
  -> TValue
  -> SeqMap SBV
  -> WordValue SBV
  -> SEval SBV (GenValue SBV)
  -> SEval SBV (SeqMap SBV)
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
  -> SEval SBV (GenValue SBV)
  -> SEval SBV (WordValue SBV)
updateFrontSym_word Inf _ _ _ _ = evalPanic "Expected finite sequence" ["updateFrontSym_bits"]
updateFrontSym_word (Nat n) eltTy bv wv val =
  case wv of
    WordVal idx
      | Just j <- SBV.svAsInteger idx ->
        do unless (j < n) (invalidIndex j)
           updateWordValue SBV bv j (fromVBit <$> val)

      | WordVal bw <- bv ->
        WordVal <$> 
          do b <- fromVBit <$> val
             let sz = SBV.intSizeOf bw
             let q = SBV.svSymbolicMerge (SBV.kindOf bw) True b bw (literalSWord sz 0)
             let msk = SBV.svShiftRight (literalSWord sz (bit (sz-1))) idx
             let bw' = SBV.svXOr bw (SBV.svAnd q msk)
             return $! bw'

    _ -> LargeBitsVal (wordValueSize SBV wv) <$> updateFrontSym (Nat n) eltTy (asBitsMap SBV bv) wv val


updateBackSym
  :: Nat'
  -> TValue
  -> SeqMap SBV
  -> WordValue SBV
  -> SEval SBV (GenValue SBV)
  -> SEval SBV (SeqMap SBV)
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
  -> SEval SBV (GenValue SBV)
  -> SEval SBV (WordValue SBV)
updateBackSym_word Inf _ _ _ _ = evalPanic "Expected finite sequence" ["updateBackSym_bits"]
updateBackSym_word (Nat n) eltTy bv wv val = do
  case wv of
    WordVal idx
      | Just j <- SBV.svAsInteger idx ->
          do unless (j < n) (invalidIndex j)
             updateWordValue SBV bv (n - 1 - j) (fromVBit <$> val)

      | WordVal bw <- bv ->
        WordVal <$>
          do b <- fromVBit <$> val
             let sz = SBV.intSizeOf bw
             let q = SBV.svSymbolicMerge (SBV.kindOf bw) True b bw (literalSWord sz 0)
             let msk = SBV.svShiftLeft (literalSWord sz (bit 1)) idx
             let bw' = SBV.svXOr bw (SBV.svAnd q msk)
             return $! bw'

    _ -> LargeBitsVal (wordValueSize SBV wv) <$> updateBackSym (Nat n) eltTy (asBitsMap SBV bv) wv val


asWordList :: [WordValue SBV] -> Maybe [SWord SBV]
asWordList = go id
 where go :: ([SWord SBV] -> [SWord SBV]) -> [WordValue SBV] -> Maybe [SWord SBV]
       go f [] = Just (f [])
       go f (WordVal x :vs) = go (f . (x:)) vs
       go _f (LargeBitsVal _ _ : _) = Nothing

liftBinArith :: (SWord SBV -> SWord SBV -> SWord SBV) -> BinArith SBV
liftBinArith op _ x y = pure $ op x y

liftBin :: (a -> b -> c) -> a -> b -> SEval SBV c
liftBin op x y = pure $ op x y

liftModBin :: (SInteger SBV -> SInteger SBV -> a) -> Integer -> SInteger SBV -> SInteger SBV -> SEval SBV a
liftModBin op modulus x y =
   do m <- integerLit SBV modulus
      pure $ op (SBV.svRem x m) (SBV.svRem y m)

sExp :: Integer -> SWord SBV -> SWord SBV -> SEval SBV (SWord SBV)
sExp _w x y =
   do ys <- reverse <$> unpackWord SBV y -- bits in little-endian order
      pure $ go ys

  where go []       = literalSWord (SBV.intSizeOf x) 1
        go (b : bs) = SBV.svIte b (SBV.svTimes x s) s
            where a = go bs
                  s = SBV.svTimes a a

sModAdd :: Integer -> SInteger SBV -> SInteger SBV -> SEval SBV (SInteger SBV)
sModAdd modulus x y =
  case (SBV.svAsInteger x, SBV.svAsInteger y) of
    (Just i, Just j) -> integerLit SBV ((i + j) `mod` modulus)
    _                -> pure $ SBV.svPlus x y

sModSub :: Integer -> SInteger SBV -> SInteger SBV -> SEval SBV (SInteger SBV)
sModSub modulus x y =
  case (SBV.svAsInteger x, SBV.svAsInteger y) of
    (Just i, Just j) -> integerLit SBV ((i - j) `mod` modulus)
    _                -> pure $ SBV.svMinus x y

sModMult :: Integer -> SInteger SBV -> SInteger SBV -> SEval SBV (SInteger SBV)
sModMult modulus x y =
  case (SBV.svAsInteger x, SBV.svAsInteger y) of
    (Just i, Just j) -> integerLit SBV ((i * j) `mod` modulus)
    _                -> pure $ SBV.svTimes x y

sModExp :: Integer -> SInteger SBV -> SInteger SBV -> SEval SBV (SInteger SBV)
sModExp modulus x y =
   do m <- integerLit SBV modulus
      pure $ SBV.svExp x (SBV.svRem y m)

-- | Ceiling (log_2 x)
sLg2 :: Integer -> SWord SBV -> SEval SBV (SWord SBV)
sLg2 _w x = pure $ go 0
  where
    lit n = literalSWord (SBV.intSizeOf x) n
    go i | i < SBV.intSizeOf x = SBV.svIte (SBV.svLessEq x (lit (2^i))) (lit (toInteger i)) (go (i + 1))
         | otherwise           = lit (toInteger i)

-- | Ceiling (log_2 x)
svLg2 :: SInteger SBV -> SEval SBV (SInteger SBV)
svLg2 x =
  case SBV.svAsInteger x of
    Just n -> pure $ SBV.svInteger SBV.KUnbounded (lg2 n)
    Nothing -> evalPanic "cannot compute lg2 of symbolic unbounded integer" []

svModLg2 :: Integer -> SInteger SBV -> SEval SBV (SInteger SBV)
svModLg2 modulus x =
   do m <- integerLit SBV modulus
      svLg2 (SBV.svRem x m)

-- Cmp -------------------------------------------------------------------------

cmpEq :: SWord SBV -> SWord SBV -> SEval SBV (SBit SBV) -> SEval SBV (SBit SBV)
cmpEq x y k = SBV.svAnd (SBV.svEqual x y) <$> k

cmpNotEq :: SWord SBV -> SWord SBV -> SEval SBV (SBit SBV) -> SEval SBV (SBit SBV)
cmpNotEq x y k = SBV.svOr (SBV.svNotEqual x y) <$> k

cmpSignedLt :: SWord SBV -> SWord SBV -> SEval SBV (SBit SBV) -> SEval SBV (SBit SBV)
cmpSignedLt x y k = SBV.svOr (SBV.svLessThan sx sy) <$> (cmpEq sx sy k)
  where sx = SBV.svSign x
        sy = SBV.svSign y

cmpLt, cmpGt :: SWord SBV -> SWord SBV -> SEval SBV (SBit SBV) -> SEval SBV (SBit SBV)
cmpLt x y k = SBV.svOr (SBV.svLessThan x y) <$> (cmpEq x y k)
cmpGt x y k = SBV.svOr (SBV.svGreaterThan x y) <$> (cmpEq x y k)

cmpLtEq, cmpGtEq :: SWord SBV -> SWord SBV -> SEval SBV (SBit SBV) -> SEval SBV (SBit SBV)
cmpLtEq x y k = SBV.svAnd (SBV.svLessEq x y) <$> (cmpNotEq x y k)
cmpGtEq x y k = SBV.svAnd (SBV.svGreaterEq x y) <$> (cmpNotEq x y k)

cmpMod ::
  (SInteger SBV -> SInteger SBV -> SEval SBV (SBit SBV) -> SEval SBV (SBit SBV)) ->
  (Integer -> SInteger SBV -> SInteger SBV -> SEval SBV (SBit SBV) -> SEval SBV (SBit SBV))
cmpMod cmp modulus x y k =
   do m <- integerLit SBV modulus
      cmp (SBV.svRem x m) (SBV.svRem y m) k

cmpModEq :: Integer -> SInteger SBV -> SInteger SBV -> SEval SBV (SBit SBV) -> SEval SBV (SBit SBV)
cmpModEq m x y k = SBV.svAnd <$> (svDivisible m (SBV.svMinus x y)) <*> k

cmpModNotEq :: Integer -> SInteger SBV -> SInteger SBV -> SEval SBV (SBit SBV) -> SEval SBV (SBit SBV)
cmpModNotEq m x y k = SBV.svOr <$> (SBV.svNot <$> (svDivisible m (SBV.svMinus x y))) <*> k

svDivisible :: Integer -> SInteger SBV -> SEval SBV (SBit SBV)
svDivisible m x =
  do m' <- integerLit SBV m
     z  <- integerLit SBV 0
     pure $ SBV.svEqual (SBV.svRem x m') z

cmpBinary :: (SBit SBV -> SBit SBV -> SEval SBV (SBit SBV) -> SEval SBV (SBit SBV))
          -> (SWord SBV -> SWord SBV -> SEval SBV (SBit SBV) -> SEval SBV (SBit SBV))
          -> (SInteger SBV -> SInteger SBV -> SEval SBV (SBit SBV) -> SEval SBV (SBit SBV))
          -> (Integer -> SInteger SBV -> SInteger SBV -> SEval SBV (SBit SBV) -> SEval SBV (SBit SBV))
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
        in return . VWord (toInteger (SBV.intSizeOf x)) . pure . WordVal $ z
     Nothing ->
       let z = SBV.svUnsign (SBV.svShiftRight (SBV.svSign x) y)
        in return . VWord (toInteger (SBV.intSizeOf x)) . pure . WordVal $ z

carry :: SWord SBV -> SWord SBV -> SEval SBV Value
carry x y = return $ VBit c
 where
  c = SBV.svLessThan (SBV.svPlus x y) x

scarry :: SWord SBV -> SWord SBV -> SEval SBV Value
scarry x y = return $ VBit sc
 where
  n = SBV.intSizeOf x
  z = SBV.svPlus (SBV.svSign x) (SBV.svSign y)
  xsign = SBV.svTestBit x (n-1)
  ysign = SBV.svTestBit y (n-1)
  zsign = SBV.svTestBit z (n-1)
  sc = SBV.svAnd (SBV.svEqual xsign ysign) (SBV.svNotEqual xsign zsign)
