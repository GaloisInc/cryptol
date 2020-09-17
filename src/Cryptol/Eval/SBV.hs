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
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
module Cryptol.Eval.SBV
  ( SBV(..), Value
  , SBVEval(..), SBVResult(..)
  , primTable
  , literalSWord
  , freshSBool_
  , freshBV_
  , freshSInteger_
  , addDefEqn
  ) where

import qualified Control.Exception as X
import           Control.Concurrent.MVar
import           Control.Monad (join)
import           Control.Monad.IO.Class (MonadIO(..))
import           Data.Bits (bit, complement, shiftL)
import           Data.Euclidean (gcdExt)
import           Data.List (foldl')
import qualified Data.Map as Map
import qualified Data.Text as T

import Data.SBV.Dynamic as SBV
import qualified Data.SBV.Internals as SBV

import Cryptol.Eval.Type (TValue(..), finNat')
import Cryptol.Eval.Backend
import Cryptol.Eval.Generic
import Cryptol.Eval.Monad
  ( Eval(..), blackhole, delayFill, evalSpark
  , EvalError(..), Unsupported(..)
  )
import Cryptol.Eval.Value
import Cryptol.Eval.Concrete ( integerToChar, ppBV, BV(..) )
import Cryptol.Testing.Random( randomV )
import Cryptol.TypeCheck.Solver.InfNat (Nat'(..), widthInteger)
import Cryptol.Utils.Ident
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.PP

data SBV =
  SBV
  { sbvStateVar     :: MVar (SBV.State)
  , sbvDefRelations :: MVar SVal
  }

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

freshBV_ :: SBV -> Int -> IO (SWord SBV)
freshBV_ (SBV stateVar _) w =
  withMVar stateVar (svMkSymVar Nothing (KBounded False w) Nothing)

freshSBool_ :: SBV -> IO (SBit SBV)
freshSBool_ (SBV stateVar _) =
  withMVar stateVar (svMkSymVar Nothing KBool Nothing)

freshSInteger_ :: SBV -> IO (SInteger SBV)
freshSInteger_ (SBV stateVar _) =
  withMVar stateVar (svMkSymVar Nothing KUnbounded Nothing)


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


addDefEqn :: SBV -> SVal -> IO ()
addDefEqn (SBV _ relsVar) b = modifyMVar_ relsVar (pure . svAnd b)

-- Symbolic Big-endian Words -------------------------------------------------------

instance Backend SBV where
  type SBit SBV = SVal
  type SWord SBV = SVal
  type SInteger SBV = SVal
  type SFloat SBV = ()        -- XXX: not implemented
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

  sSpark _ m = SBVEval $
    do m' <- evalSpark (sbvEval m)
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
  ppWord sym opts v
     | Just x <- svAsInteger v = ppBV opts (BV (wordLen sym v) x)
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
  znEq sym m a b = svDivisible sym m (SBV.svMinus a b)

  znPlus  sym m a b = sModAdd sym m a b
  znMinus sym m a b = sModSub sym m a b
  znMult  sym m a b = sModMult sym m a b
  znNegate sym m a  = sModNegate sym m a
  znRecip = sModRecip

  ppFloat _ _ _           = text "[?]"
  fpExactLit _ _          = unsupported "fpExactLit"
  fpLit _ _ _ _           = unsupported "fpLit"
  fpLogicalEq _ _ _       = unsupported "fpLogicalEq"
  fpEq _ _ _              = unsupported "fpEq"
  fpLessThan _ _ _        = unsupported "fpLessThan"
  fpGreaterThan _ _ _     = unsupported "fpGreaterThan"
  fpPlus _ _ _ _          = unsupported "fpPlus"
  fpMinus _ _ _ _         = unsupported "fpMinus"
  fpMult _  _ _ _         = unsupported "fpMult"
  fpDiv _ _ _ _           = unsupported "fpDiv"
  fpNeg _ _               = unsupported "fpNeg"
  fpFromInteger _ _ _ _ _ = unsupported "fpFromInteger"
  fpToInteger _ _ _ _     = unsupported "fpToInteger"

unsupported :: String -> SEval SBV a
unsupported x = liftIO (X.throw (UnsupportedSymbolicOp x))


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

-- See also Cryptol.Eval.Concrete.primTable
primTable :: SBV -> Map.Map PrimIdent Value
primTable sym =
  Map.fromList $ map (\(n, v) -> (prelPrim (T.pack n), v))

  [ -- Literals
    ("True"        , VBit (bitLit sym True))
  , ("False"       , VBit (bitLit sym False))
  , ("number"      , ecNumberV sym) -- Converts a numeric type into its corresponding value.
                                    -- { val, rep } (Literal val rep) => rep
  , ("fraction"     , ecFractionV sym)
  , ("ratio"       , ratioV sym)

    -- Zero
  , ("zero"        , VPoly (zeroV sym))

    -- Logic
  , ("&&"          , binary (andV sym))
  , ("||"          , binary (orV sym))
  , ("^"           , binary (xorV sym))
  , ("complement"  , unary  (complementV sym))

    -- Ring
  , ("fromInteger" , fromIntegerV sym)
  , ("+"           , binary (addV sym))
  , ("-"           , binary (subV sym))
  , ("negate"      , unary (negateV sym))
  , ("*"           , binary (mulV sym))

    -- Integral
  , ("toInteger"   , toIntegerV sym)
  , ("/"           , binary (divV sym))
  , ("%"           , binary (modV sym))
  , ("^^"          , expV sym)
  , ("infFrom"     , infFromV sym)
  , ("infFromThen" , infFromThenV sym)

    -- Field
  , ("recip"       , recipV sym)
  , ("/."          , fieldDivideV sym)

    -- Round
  , ("floor"       , unary (floorV sym))
  , ("ceiling"     , unary (ceilingV sym))
  , ("trunc"       , unary (truncV sym))
  , ("roundAway"   , unary (roundAwayV sym))
  , ("roundToEven" , unary (roundToEvenV sym))

    -- Word operations
  , ("/$"          , sdivV sym)
  , ("%$"          , smodV sym)
  , ("lg2"         , lg2V sym)
  , (">>$"         , sshrV sym)

    -- Cmp
  , ("<"           , binary (lessThanV sym))
  , (">"           , binary (greaterThanV sym))
  , ("<="          , binary (lessThanEqV sym))
  , (">="          , binary (greaterThanEqV sym))
  , ("=="          , binary (eqV sym))
  , ("!="          , binary (distinctV sym))

    -- SignedCmp
  , ("<$"          , binary (signedLessThanV sym))

    -- Finite enumerations
  , ("fromTo"      , fromToV sym)
  , ("fromThenTo"  , fromThenToV sym)

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

    -- Misc

  , ("fromZ"       , fromZV sym)

  , ("foldl"       , foldlV sym)
  , ("foldl'"      , foldl'V sym)

  , ("deepseq"     ,
      tlam $ \_a ->
      tlam $ \_b ->
       lam $ \x -> pure $
       lam $ \y ->
         do _ <- forceValue =<< x
            y)

  , ("parmap"      , parmapV sym)

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


sModAdd :: SBV -> Integer -> SInteger SBV -> SInteger SBV -> SEval SBV (SInteger SBV)
sModAdd _ 0 _ _ = evalPanic "sModAdd" ["0 modulus not allowed"]
sModAdd sym modulus x y =
  case (SBV.svAsInteger x, SBV.svAsInteger y) of
    (Just i, Just j) -> integerLit sym ((i + j) `mod` modulus)
    _                -> pure $ SBV.svPlus x y

sModSub :: SBV -> Integer -> SInteger SBV -> SInteger SBV -> SEval SBV (SInteger SBV)
sModSub _ 0 _ _ = evalPanic "sModSub" ["0 modulus not allowed"]
sModSub sym modulus x y =
  case (SBV.svAsInteger x, SBV.svAsInteger y) of
    (Just i, Just j) -> integerLit sym ((i - j) `mod` modulus)
    _                -> pure $ SBV.svMinus x y

sModNegate :: SBV -> Integer -> SInteger SBV -> SEval SBV (SInteger SBV)
sModNegate _ 0 _ = evalPanic "sModNegate" ["0 modulus not allowed"]
sModNegate sym modulus x =
  case SBV.svAsInteger x of
    Just i -> integerLit sym ((negate i) `mod` modulus)
    _      -> pure $ SBV.svUNeg x

sModMult :: SBV -> Integer -> SInteger SBV -> SInteger SBV -> SEval SBV (SInteger SBV)
sModMult _ 0 _ _ = evalPanic "sModMult" ["0 modulus not allowed"]
sModMult sym modulus x y =
  case (SBV.svAsInteger x, SBV.svAsInteger y) of
    (Just i, Just j) -> integerLit sym ((i * j) `mod` modulus)
    _                -> pure $ SBV.svTimes x y

-- Create a fresh constant and assert that it is the
-- multiplicitive inverse of x; return the constant.
-- Such an inverse must exist under the precondition
-- that the modulus is prime and the input is nonzero.
sModRecip ::
  SBV ->
  Integer {- ^ modulus: must be prime -} ->
  SInteger SBV ->
  SEval SBV (SInteger SBV)
sModRecip _sym 0 _ = panic "sModRecip" ["0 modulus not allowed"]
sModRecip sym m x
  -- If the input is concrete, evaluate the answer
  | Just xi <- svAsInteger x
  = let (g,s) = gcdExt xi m
     in if | abs g == m -> raiseError sym DivideByZero
           | abs g == 1 -> pure (svInteger KUnbounded (s `mod` m))
           | otherwise ->
             evalPanic "sModRecip"
                [ "illegal modulus: " ++ show m
                , "  gcd("++show xi++", " ++ show m++") = " ++ show g
                ]

  -- If the input is symbolic, create a new symbolic constant
  -- and assert that it is the desired multiplicitive inverse.
  -- Such an inverse will exist under the precondition that
  -- the modulus is prime, and as long as the input is nonzero.
  | otherwise
  = do divZero <- svDivisible sym m x
       assertSideCondition sym (svNot divZero) DivideByZero

       z <- liftIO (freshSInteger_ sym)
       let xz = svTimes x z
       rel <- znEq sym m xz (svInteger KUnbounded 1)
       let range = svAnd (svLessThan (svInteger KUnbounded 0) z)
                         (svLessThan z (svInteger KUnbounded m))
       liftIO (addDefEqn sym (svAnd range (svOr divZero rel)))

       return z

-- | Ceiling (log_2 x)
sLg2 :: SWord SBV -> SEval SBV (SWord SBV)
sLg2 x = pure $ go 0
  where
    lit n = literalSWord (SBV.intSizeOf x) n
    go i | i < SBV.intSizeOf x = SBV.svIte (SBV.svLessEq x (lit (2^i))) (lit (toInteger i)) (go (i + 1))
         | otherwise           = lit (toInteger i)

svDivisible :: SBV -> Integer -> SInteger SBV -> SEval SBV (SBit SBV)
svDivisible sym m x =
  do m' <- integerLit sym m
     z  <- integerLit sym 0
     pure $ SBV.svEqual (SBV.svRem x m') z

signedQuot :: SWord SBV -> SWord SBV -> SWord SBV
signedQuot x y = SBV.svUnsign (SBV.svQuot (SBV.svSign x) (SBV.svSign y))

signedRem :: SWord SBV -> SWord SBV -> SWord SBV
signedRem x y = SBV.svUnsign (SBV.svRem (SBV.svSign x) (SBV.svSign y))

ashr :: SVal -> SVal -> SVal
ashr x idx =
  case SBV.svAsInteger idx of
    Just i  -> SBV.svUnsign (SBV.svShr (SBV.svSign x) (fromInteger i))
    Nothing -> SBV.svUnsign (SBV.svShiftRight (SBV.svSign x) idx)

lshr :: SVal -> SVal -> SVal
lshr x idx =
  case SBV.svAsInteger idx of
    Just i -> SBV.svShr x (fromInteger i)
    Nothing -> SBV.svShiftRight x idx

shl :: SVal -> SVal -> SVal
shl x idx =
  case SBV.svAsInteger idx of
    Just i  -> SBV.svShl x (fromInteger i)
    Nothing -> SBV.svShiftLeft x idx

sshrV :: SBV -> Value
sshrV sym =
  nlam $ \n ->
  tlam $ \ix ->
  wlam sym $ \x -> return $
  lam $ \y ->
   y >>= asIndex sym ">>$" ix >>= \case
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
