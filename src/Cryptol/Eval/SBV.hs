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
  , SBVEval(..), SBVResult(..)
  , evalPrim
  , forallBV_, existsBV_
  , forallSBool_, existsSBool_
  , forallSInteger_, existsSInteger_
  ) where

import           Control.Monad (join, unless)
import           Control.Monad.IO.Class (MonadIO(..))
import           Data.Bits (bit, complement, shiftL)
import           Data.List (foldl')
import qualified Data.Map as Map
import qualified Data.Text as T

import Data.SBV (symbolicEnv)
import Data.SBV.Dynamic as SBV

import Cryptol.Eval.Type (TValue(..), finNat')
import Cryptol.Eval.Backend
import Cryptol.Eval.Generic
import Cryptol.Eval.Monad
  ( Eval(..), blackhole, delayFill, EvalError(..) )
import Cryptol.Eval.Value
import Cryptol.Eval.Concrete ( integerToChar, ppBV, BV(..), lg2 )
import Cryptol.Testing.Random( randomV )
import Cryptol.TypeCheck.Solver.InfNat (Nat'(..), widthInteger)
import Cryptol.Utils.Ident
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.PP

data SBV = SBV

-- Utility operations -------------------------------------------------------------

fromBitsLE :: [SBit SBV] -> SWord SBV
fromBitsLE bs = foldl' f (literalSWord 0 0) bs
  where f w b = svJoin (svToWord1 b) w

packSBV :: [SBit SBV] -> SWord SBV
packSBV bs = fromBitsLE (reverse bs)

unpackSBV :: SWord SBV -> [SBit SBV]
unpackSBV x = [ svTestBit x i | i <- reverse [0 .. intSizeOf x - 1] ]

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

-- SBV Evaluation monad -------------------------------------------------------

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


-- Symbolic Big-endian Words -------------------------------------------------------

instance Backend SBV where
  type SBit SBV = SVal
  type SWord SBV = SVal
  type SInteger SBV = SVal

  type SEval SBV = SBVEval

  raiseError _ err = SBVEval (pure (SBVError err))

  assertSideCondition _ cond err
    | Just False <- svAsBool cond = SBVEval (pure (SBVError err))
    | otherwise = SBVEval (pure (SBVResult cond ()))

  isReady _ (SBVEval (Ready _)) = True
  isReady _ _ = False

  sDelayFill _ m retry = SBVEval $
    do m' <- delayFill (sbvEval m) (sbvEval retry)
       pure (pure (SBVEval m'))

  sDeclareHole _ msg = SBVEval $
    do (hole, fill) <- blackhole msg
       pure (pure (SBVEval hole, \m -> SBVEval (fmap pure $ fill (sbvEval m))))

  mergeEval _sym f c mx my = SBVEval $
    do rx <- sbvEval mx
       ry <- sbvEval my
       case (rx, ry) of
         (SBVError err, SBVError _) ->
           pure $ SBVError err -- arbitrarily choose left error to report
         (SBVError _, SBVResult p y) ->
           pure $ SBVResult (svAnd (svNot c) p) y
         (SBVResult p x, SBVError _) ->
           pure $ SBVResult (svAnd c p) x
         (SBVResult px x, SBVResult py y) ->
           do zr <- sbvEval (f c x y)
              case zr of
                SBVError err -> pure $ SBVError err
                SBVResult pz z ->
                  pure $ SBVResult (svAnd (svIte c px py) pz) z

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

  iteBit _ b x y = pure $! svSymbolicMerge KBool True b x y
  iteWord _ b x y = pure $! svSymbolicMerge (kindOf x) True b x y
  iteInteger _ b x y = pure $! svSymbolicMerge KUnbounded True b x y

  bitAsLit _ b = svAsBool b
  wordAsLit _ w =
    case svAsInteger w of
      Just x -> Just (toInteger (intSizeOf w), x)
      Nothing -> Nothing
  integerAsLit _ v = svAsInteger v

  bitLit _ b     = svBool b
  wordLit _ n x  = pure $! literalSWord (fromInteger n) x
  integerLit _ x = pure $! svInteger KUnbounded x

  bitEq  _ x y = pure $! svEqual x y
  bitOr  _ x y = pure $! svOr x y
  bitAnd _ x y = pure $! svAnd x y
  bitXor _ x y = pure $! svXOr x y
  bitComplement _ x = pure $! svNot x

  wordBit _ x idx = pure $! svTestBit x (intSizeOf x - 1 - fromInteger idx)

  wordUpdate _ x idx b = pure $! svSymbolicMerge (kindOf x) False b wtrue wfalse
    where
     i' = intSizeOf x - 1 - fromInteger idx
     wtrue  = x `svOr`  svInteger (kindOf x) (bit i' :: Integer)
     wfalse = x `svAnd` svInteger (kindOf x) (complement (bit i' :: Integer))

  packWord _ bs  = pure $! packSBV bs
  unpackWord _ x = pure $! unpackSBV x

  wordEq _ x y = pure $! svEqual x y
  wordLessThan _ x y = pure $! svLessThan x y
  wordGreaterThan _ x y = pure $! svGreaterThan x y

  wordSignedLessThan _ x y = pure $! svLessThan sx sy
    where sx = svSign x
          sy = svSign y

  joinWord _ x y = pure $! svJoin x y

  splitWord _ _leftW rightW w = pure
    ( svExtract (intSizeOf w - 1) (fromInteger rightW) w
    , svExtract (fromInteger rightW - 1) 0 w
    )

  extractWord _ len start w =
    pure $! svExtract (fromInteger start + fromInteger len - 1) (fromInteger start) w

  wordAnd _ a b = pure $! svAnd a b
  wordOr  _ a b = pure $! svOr a b
  wordXor _ a b = pure $! svXOr a b
  wordComplement _ a = pure $! svNot a

  wordPlus  _ a b = pure $! svPlus a b
  wordMinus _ a b = pure $! svMinus a b
  wordMult  _ a b = pure $! svTimes a b
  wordNegate _ a  = pure $! svUNeg a

  wordDiv sym a b =
    do let z = literalSWord (intSizeOf b) 0
       assertSideCondition sym (svNot (svEqual b z)) DivideByZero
       pure $! svQuot a b

  wordMod sym a b =
    do let z = literalSWord (intSizeOf b) 0
       assertSideCondition sym (svNot (svEqual b z)) DivideByZero
       pure $! svRem a b

  wordSignedDiv sym a b =
    do let z = literalSWord (intSizeOf b) 0
       assertSideCondition sym (svNot (svEqual b z)) DivideByZero
       pure $! signedQuot a b

  wordSignedMod sym a b =
    do let z = literalSWord (intSizeOf b) 0
       assertSideCondition sym (svNot (svEqual b z)) DivideByZero
       pure $! signedRem a b

  wordLg2 _ a = sLg2 a

  wordToInt _ x = pure $! svToInteger x
  wordFromInt _ w i = pure $! svFromInteger w i

  intEq _ a b = pure $! svEqual a b
  intLessThan _ a b = pure $! svLessThan a b
  intGreaterThan _ a b = pure $! svGreaterThan a b

  intPlus  _ a b = pure $! svPlus a b
  intMinus _ a b = pure $! svMinus a b
  intMult  _ a b = pure $! svTimes a b
  intNegate _ a  = pure $! SBV.svUNeg a
  intLg2 _ a = svLg2 a

  intDiv sym a b =
    do let z = svInteger KUnbounded 0
       assertSideCondition sym (svNot (svEqual b z)) DivideByZero
       let p = svLessThan z b
       pure $! svSymbolicMerge KUnbounded True p (svQuot a b) (svQuot (svUNeg a) (svUNeg b))
  intMod sym a b =
    do let z = svInteger KUnbounded 0
       assertSideCondition sym (svNot (svEqual b z)) DivideByZero
       let p = svLessThan z b
       pure $! svSymbolicMerge KUnbounded True p (svRem a b) (svUNeg (svRem (svUNeg a) (svUNeg b)))

  -- NB, we don't do reduction here
  intToZn _ _m a = pure a

  znToInt _ 0 _ = evalPanic "znToInt" ["0 modulus not allowed"]
  znToInt _ m a =
    do let m' = svInteger KUnbounded m
       pure $! svRem a m'

  znEq _ 0 _ _ = evalPanic "znEq" ["0 modulus not allowed"]
  znEq _ m a b = svDivisible m (SBV.svMinus a b)

  znPlus  _ m a b = sModAdd m a b
  znMinus _ m a b = sModSub m a b
  znMult  _ m a b = sModMult m a b
  znNegate _ m a  = sModNegate m a

svToInteger :: SWord SBV -> SInteger SBV
svToInteger w =
  case svAsInteger w of
    Nothing -> svFromIntegral KUnbounded w
    Just x  -> svInteger KUnbounded x

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

-- See also Cryptol.Eval.Concrete.primTable
primTable :: Map.Map Ident Value
primTable  = let sym = SBV in
  Map.fromList $ map (\(n, v) -> (mkIdent (T.pack n), v))
  [ -- Literals
    ("True"        , VBit (bitLit sym True))
  , ("False"       , VBit (bitLit sym False))
  , ("number"      , ecNumberV sym) -- Converts a numeric type into its corresponding value.
                                    -- { val, rep } (Literal val rep) => rep

    -- Arith
  , ("fromInteger" , ecFromIntegerV sym)
  , ("+"           , binary (addV sym)) -- {a} (Arith a) => a -> a -> a
  , ("-"           , binary (subV sym)) -- {a} (Arith a) => a -> a -> a
  , ("*"           , binary (mulV sym)) -- {a} (Arith a) => a -> a -> a
  , ("/"           , binary (divV sym)) -- {a} (Arith a) => a -> a -> a
  , ("%"           , binary (modV sym)) -- {a} (Arith a) => a -> a -> a
  , ("/$"          , sdivV sym)
  , ("%$"          , smodV sym)
  , ("lg2"         , unary (lg2V sym))
  , ("negate"      , unary (negateV sym))
  , ("infFrom"     , infFromV sym)
  , ("infFromThen" , infFromThenV sym)

    -- Cmp
  , ("<"           , binary (lessThanV sym))
  , (">"           , binary (greaterThanV sym))
  , ("<="          , binary (lessThanEqV sym))
  , (">="          , binary (greaterThanEqV sym))
  , ("=="          , binary (eqV sym))
  , ("!="          , binary (distinctV sym))

    -- SignedCmp
  , ("<$"          , binary (signedLessThanV sym))

    -- Logic
  , ("&&"          , binary (andV sym))
  , ("||"          , binary (orV sym))
  , ("^"           , binary (xorV sym))
  , ("complement"  , unary  (complementV sym))

    -- Zero
  , ("zero"        , VPoly (zeroV sym))

    -- Finite enumerations
  , ("fromTo"      , fromToV sym)
  , ("fromThenTo"  , fromThenToV sym)

    -- Conversions to Integer
  , ("toInteger"   , ecToIntegerV sym)
  , ("fromZ"       , ecFromZ sym)

    -- Sequence manipulations
  , ("#"          , -- {a,b,d} (fin a) => [a] d -> [b] d -> [a + b] d
     nlam $ \ front ->
     nlam $ \ back  ->
     tlam $ \ elty  ->
     lam  $ \ l     -> return $
     lam  $ \ r     -> join (ccatV sym front back elty <$> l <*> r))

  , ("join"       ,
     nlam $ \ parts ->
     nlam $ \ (finNat' -> each)  ->
     tlam $ \ a     ->
     lam  $ \ x     ->
       joinV sym parts each a =<< x)

  , ("split"       , ecSplitV sym)

  , ("splitAt"    ,
     nlam $ \ front ->
     nlam $ \ back  ->
     tlam $ \ a     ->
     lam  $ \ x     ->
       splitAtV sym front back a =<< x)

  , ("reverse"    , nlam $ \_a ->
                    tlam $ \_b ->
                     lam $ \xs -> reverseV sym =<< xs)

  , ("transpose"  , nlam $ \a ->
                    nlam $ \b ->
                    tlam $ \c ->
                     lam $ \xs -> transposeV sym a b c =<< xs)

    -- Shifts and rotates
  , ("<<"          , logicShift sym "<<"
                       shiftShrink
                       (\x y -> pure (SBV.svShiftLeft x y))
                       shiftLeftReindex)

  , (">>"          , logicShift sym ">>"
                       shiftShrink
                       (\x y -> pure (SBV.svShiftRight x y))
                       shiftRightReindex)

  , ("<<<"         , logicShift sym "<<<"
                       rotateShrink
                       (\x y -> pure (SBV.svRotateLeft x y))
                       rotateLeftReindex)

  , (">>>"         , logicShift sym ">>>"
                       rotateShrink
                       (\x y -> pure (SBV.svRotateRight x y))
                       rotateRightReindex)

  , (">>$"         , sshrV)


    -- Indexing and updates
  , ("@"           , indexPrim sym indexFront indexFront_bits indexFront)
  , ("!"           , indexPrim sym indexBack indexBack_bits indexBack)

  , ("update"      , updatePrim sym updateFrontSym_word updateFrontSym)
  , ("updateEnd"   , updatePrim sym updateBackSym_word updateBackSym)

    -- Misc

    -- {at,len} (fin len) => [len][8] -> at
  , ("error"       ,
      tlam $ \a ->
      nlam $ \_ ->
      VFun $ \s -> errorV sym a =<< (valueToString sym =<< s))

  , ("random"      ,
      tlam $ \a ->
      wlam sym $ \x ->
         case integerAsLit sym x of
           Just i  -> randomV sym a i
           Nothing -> cryUserError sym "cannot evaluate 'random' with symbolic inputs")

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


indexFront ::
  Nat' ->
  TValue ->
  SeqMap SBV ->
  TValue ->
  SVal ->
  SEval SBV Value
indexFront mblen a xs _ix idx
  | Just i <- SBV.svAsInteger idx
  = lookupSeqMap xs i

  | Nat n <- mblen
  , TVSeq wlen TVBit <- a
  = do wvs <- traverse (fromWordVal "indexFront" =<<) (enumerateSeqMap n xs)
       case asWordList wvs of
         Just ws ->
           do z <- wordLit SBV wlen 0
              return $ VWord wlen $ pure $ WordVal $ SBV.svSelect ws z idx
         Nothing -> folded

  | otherwise
  = folded

 where
    k = SBV.kindOf idx
    def = zeroV SBV a
    f n y = iteValue SBV (SBV.svEqual idx (SBV.svInteger k n)) (lookupSeqMap xs n) y
    folded =
      case k of
        KBounded _ w ->
          case mblen of
            Nat n | n < 2^w -> foldr f def [0 .. n-1]
            _ -> foldr f def [0 .. 2^w - 1]
        _ ->
          case mblen of
            Nat n -> foldr f def [0 .. n-1]
            Inf -> raiseError SBV (UnsupportedSymbolicOp "unbounded integer indexing")

indexBack ::
  Nat' ->
  TValue ->
  SeqMap SBV ->
  TValue ->
  SWord SBV ->
  SEval SBV Value
indexBack (Nat n) a xs ix idx = indexFront (Nat n) a (reverseSeqMap n xs) ix idx
indexBack Inf _ _ _ _ = evalPanic "Expected finite sequence" ["indexBack"]

indexFront_bits ::
  Nat' ->
  TValue ->
  SeqMap SBV ->
  TValue ->
  [SBit SBV] ->
  SEval SBV Value
indexFront_bits mblen _a xs _ix bits0 = go 0 (length bits0) bits0
 where
  go :: Integer -> Int -> [SBit SBV] -> SEval SBV Value
  go i _k []
    -- For indices out of range, fail
    | Nat n <- mblen
    , i >= n
    = raiseError SBV (InvalidIndex (Just i))

    | otherwise
    = lookupSeqMap xs i

  go i k (b:bs)
    -- Fail early when all possible indices we could compute from here
    -- are out of bounds
    | Nat n <- mblen
    , (i `shiftL` k) >= n
    = raiseError SBV (InvalidIndex Nothing)

    | otherwise
    = iteValue SBV b
         (go ((i `shiftL` 1) + 1) (k-1) bs)
         (go  (i `shiftL` 1)      (k-1) bs)


indexBack_bits ::
  Nat' ->
  TValue ->
  SeqMap SBV ->
  TValue ->
  [SBit SBV] ->
  SEval SBV Value
indexBack_bits (Nat n) a xs ix idx = indexFront_bits (Nat n) a (reverseSeqMap n xs) ix idx
indexBack_bits Inf _ _ _ _ = evalPanic "Expected finite sequence" ["indexBack_bits"]


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


updateFrontSym ::
  Nat' ->
  TValue ->
  SeqMap SBV ->
  WordValue SBV ->
  SEval SBV (GenValue SBV) ->
  SEval SBV (SeqMap SBV)
updateFrontSym _len _eltTy vs wv val =
  case wv of
    WordVal w | Just j <- SBV.svAsInteger w ->
      return $ updateSeqMap vs j val
    _ ->
      return $ IndexSeqMap $ \i ->
      do b <- wordValueEqualsInteger wv i
         iteValue SBV b val (lookupSeqMap vs i)

updateFrontSym_word ::
  Nat' ->
  TValue ->
  WordValue SBV ->
  WordValue SBV ->
  SEval SBV (GenValue SBV) ->
  SEval SBV (WordValue SBV)
updateFrontSym_word Inf _ _ _ _ = evalPanic "Expected finite sequence" ["updateFrontSym_bits"]
updateFrontSym_word (Nat n) eltTy bv wv val =
  case wv of
    WordVal idx
      | Just j <- SBV.svAsInteger idx ->
          updateWordValue SBV bv j (fromVBit <$> val)

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

    _ -> LargeBitsVal (wordValueSize SBV wv) <$> updateFrontSym (Nat n) eltTy (asBitsMap SBV bv) wv val


updateBackSym ::
  Nat' ->
  TValue ->
  SeqMap SBV ->
  WordValue SBV ->
  SEval SBV (GenValue SBV) ->
  SEval SBV (SeqMap SBV)
updateBackSym Inf _ _ _ _ = evalPanic "Expected finite sequence" ["updateBackSym"]
updateBackSym (Nat n) _eltTy vs wv val =
  case wv of
    WordVal w | Just j <- SBV.svAsInteger w ->
      return $ updateSeqMap vs (n - 1 - j) val
    _ ->
      return $ IndexSeqMap $ \i ->
      do b <- wordValueEqualsInteger wv (n - 1 - i)
         iteValue SBV b val (lookupSeqMap vs i)

updateBackSym_word ::
  Nat' ->
  TValue ->
  WordValue SBV ->
  WordValue SBV ->
  SEval SBV (GenValue SBV) ->
  SEval SBV (WordValue SBV)
updateBackSym_word Inf _ _ _ _ = evalPanic "Expected finite sequence" ["updateBackSym_bits"]
updateBackSym_word (Nat n) eltTy bv wv val = do
  case wv of
    WordVal idx
      | Just j <- SBV.svAsInteger idx ->
          updateWordValue SBV bv (n - 1 - j) (fromVBit <$> val)

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

    _ -> LargeBitsVal (wordValueSize SBV wv) <$> updateBackSym (Nat n) eltTy (asBitsMap SBV bv) wv val


asWordList :: [WordValue SBV] -> Maybe [SWord SBV]
asWordList = go id
 where go :: ([SWord SBV] -> [SWord SBV]) -> [WordValue SBV] -> Maybe [SWord SBV]
       go f [] = Just (f [])
       go f (WordVal x :vs) = go (f . (x:)) vs
       go _f (LargeBitsVal _ _ : _) = Nothing


sModAdd :: Integer -> SInteger SBV -> SInteger SBV -> SEval SBV (SInteger SBV)
sModAdd 0 _ _ = evalPanic "sModAdd" ["0 modulus not allowed"]
sModAdd modulus x y =
  case (SBV.svAsInteger x, SBV.svAsInteger y) of
    (Just i, Just j) -> integerLit SBV ((i + j) `mod` modulus)
    _                -> pure $ SBV.svPlus x y

sModSub :: Integer -> SInteger SBV -> SInteger SBV -> SEval SBV (SInteger SBV)
sModSub 0 _ _ = evalPanic "sModSub" ["0 modulus not allowed"]
sModSub modulus x y =
  case (SBV.svAsInteger x, SBV.svAsInteger y) of
    (Just i, Just j) -> integerLit SBV ((i - j) `mod` modulus)
    _                -> pure $ SBV.svMinus x y

sModNegate :: Integer -> SInteger SBV -> SEval SBV (SInteger SBV)
sModNegate 0 _ = evalPanic "sModNegate" ["0 modulus not allowed"]
sModNegate modulus x =
  case SBV.svAsInteger x of
    Just i -> integerLit SBV ((negate i) `mod` modulus)
    _      -> pure $ SBV.svUNeg x

sModMult :: Integer -> SInteger SBV -> SInteger SBV -> SEval SBV (SInteger SBV)
sModMult 0 _ _ = evalPanic "sModMult" ["0 modulus not allowed"]
sModMult modulus x y =
  case (SBV.svAsInteger x, SBV.svAsInteger y) of
    (Just i, Just j) -> integerLit SBV ((i * j) `mod` modulus)
    _                -> pure $ SBV.svTimes x y

-- | Ceiling (log_2 x)
sLg2 :: SWord SBV -> SEval SBV (SWord SBV)
sLg2 x = pure $ go 0
  where
    lit n = literalSWord (SBV.intSizeOf x) n
    go i | i < SBV.intSizeOf x = SBV.svIte (SBV.svLessEq x (lit (2^i))) (lit (toInteger i)) (go (i + 1))
         | otherwise           = lit (toInteger i)

-- | Ceiling (log_2 x)
svLg2 :: SInteger SBV -> SEval SBV (SInteger SBV)
svLg2 x =
  case SBV.svAsInteger x of
    Just n -> pure $ SBV.svInteger SBV.KUnbounded (lg2 n)
    Nothing -> raiseError SBV (UnsupportedSymbolicOp "integer lg2")

svDivisible :: Integer -> SInteger SBV -> SEval SBV (SBit SBV)
svDivisible m x =
  do m' <- integerLit SBV m
     z  <- integerLit SBV 0
     pure $ SBV.svEqual (SBV.svRem x m') z

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
