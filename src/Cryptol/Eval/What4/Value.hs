-- |
-- Module      :  Cryptol.Eval.What4
-- Copyright   :  (c) 2020 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com

{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
module Cryptol.Eval.What4.Value where


import qualified Control.Exception as X
import           Control.Concurrent.MVar
import           Control.Monad (foldM,ap,liftM)
import           Control.Monad.IO.Class
import           Data.Bits (bit, shiftR, shiftL, testBit)
import qualified Data.BitVector.Sized as BV
import           Data.List
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some

import qualified What4.Interface as W4
import qualified What4.SWord as SW
import qualified Cryptol.Eval.What4.SFloat as FP
import qualified What4.Utils.AbstractDomains as W4

import Cryptol.Eval.Backend
import Cryptol.Eval.Concrete.Value( BV(..), ppBV )
import Cryptol.Eval.Concrete.FloatHelpers
import Cryptol.Eval.Generic
import Cryptol.Eval.Monad
   ( Eval(..), EvalError(..), Unsupported(..)
   , delayFill, blackhole, evalSpark
   )
import Cryptol.Eval.Type (TValue(..))
import Cryptol.Eval.Value
import Cryptol.TypeCheck.Solver.InfNat (Nat'(..), widthInteger)
import Cryptol.Utils.Panic
import Cryptol.Utils.PP


data What4 sym =
  What4
  { w4  :: sym
  , w4defs :: MVar (W4.Pred sym)
  }

type Value sym = GenValue (What4 sym)

{- | This is the monad used for symbolic evaluation. It adds to
aspects to 'Eval'---'WConn' keeps track of the backend and collects
definitional predicates, and 'W4Eval` adds support for partially
defined values -}
newtype W4Eval sym a = W4Eval { evalPartial :: W4Conn sym (W4Result sym a) }

{- | This layer has the symbolic back-end, and can keep track of definitional
predicates used when working with uninterpreted constants defined
via a property. -}
newtype W4Conn sym a = W4Conn { evalConn :: sym -> Eval a }

-- | The symbolic value we computed.
data W4Result sym a
  = W4Error !EvalError
    -- ^ A malformed value

  | W4Result !(W4.Pred sym) !a
    -- ^ safety predicate and result: the result only makes sense when
    -- the predicate holds.


--------------------------------------------------------------------------------
-- Moving between the layers

w4Eval :: W4Eval sym a -> sym -> Eval (W4Result sym a)
w4Eval (W4Eval (W4Conn m)) = m

w4Thunk :: Eval (W4Result sym a) -> W4Eval sym a
w4Thunk m = W4Eval (W4Conn \_ -> m)

-- | A value with no context.
doEval :: W4.IsExprBuilder sym => Eval a -> W4Conn sym a
doEval m = W4Conn \_sym -> m

-- | A total value.
total :: W4.IsExprBuilder sym => W4Conn sym a -> W4Eval sym a
total m = W4Eval
  do sym <- getSym
     W4Result (W4.backendPred sym True) <$> m

--------------------------------------------------------------------------------
-- Operations in WConn

instance W4.IsExprBuilder sym => Functor (W4Conn sym) where
  fmap = liftM

instance W4.IsExprBuilder sym => Applicative (W4Conn sym) where
  pure   = doEval . pure
  (<*>)  = ap

instance W4.IsExprBuilder sym => Monad (W4Conn sym) where
  m1 >>= f = W4Conn \sym ->
    do res1 <- evalConn m1 sym
       evalConn (f res1) sym

instance W4.IsExprBuilder sym => MonadIO (W4Conn sym) where
  liftIO = doEval . liftIO

-- | Access the symbolic back-end
getSym :: W4.IsExprBuilder sym => W4Conn sym sym
getSym = W4Conn \sym -> pure sym

-- | Record a definition.
--addDef :: W4.Pred sym -> W4Conn sym ()
--addDef p = W4Conn \_ -> pure W4Defs { w4Defs = p, w4Result = () }

-- | Compute conjunction.
w4And :: W4.IsExprBuilder sym =>
         W4.Pred sym -> W4.Pred sym -> W4Conn sym (W4.Pred sym)
w4And p q =
  do sym <- getSym
     liftIO (W4.andPred sym p q)

-- | Compute negation.
w4Not :: W4.IsExprBuilder sym => W4.Pred sym -> W4Conn sym (W4.Pred sym)
w4Not p =
  do sym <- getSym
     liftIO (W4.notPred sym p)

-- | Compute if-then-else.
w4ITE :: W4.IsExprBuilder sym =>
         W4.Pred sym -> W4.Pred sym -> W4.Pred sym -> W4Conn sym (W4.Pred sym)
w4ITE ifP ifThen ifElse =
  do sym <- getSym
     liftIO (W4.itePred sym ifP ifThen ifElse)



--------------------------------------------------------------------------------
-- Operations in W4Eval

instance W4.IsExprBuilder sym => Functor (W4Eval sym) where
  fmap = liftM

instance W4.IsExprBuilder sym => Applicative (W4Eval sym) where
  pure  = total . pure
  (<*>) = ap

instance W4.IsExprBuilder sym => Monad (W4Eval sym) where
  m1 >>= f = W4Eval
    do res1 <- evalPartial m1
       case res1 of
         W4Error err -> pure (W4Error err)
         W4Result px x' ->
           do res2 <- evalPartial (f x')
              case res2 of
                W4Result py y ->
                  do pz <- w4And px py
                     pure (W4Result pz y)
                W4Error _ -> pure res2

instance W4.IsExprBuilder sym => MonadIO (W4Eval sym) where
  liftIO = total . liftIO


-- | Add a definitional equation.
-- This will always be asserted when we make queries to the solver.
addDefEqn :: W4.IsExprBuilder sym => What4 sym -> W4.Pred sym -> W4Eval sym ()
addDefEqn (What4 w4sym defVar) p = liftIO (modifyMVar_ defVar (W4.andPred w4sym p))

-- | Add s safety condition.
addSafety :: W4.IsExprBuilder sym => W4.Pred sym -> W4Eval sym ()
addSafety p = W4Eval (pure (W4Result p ()))

-- | A fully undefined symbolic value
evalError :: W4.IsExprBuilder sym => EvalError -> W4Eval sym a
evalError err = W4Eval (pure (W4Error err))
--------------------------------------------------------------------------------


assertBVDivisor :: W4.IsExprBuilder sym => What4 sym -> SW.SWord sym -> W4Eval sym ()
assertBVDivisor sym x =
  do p <- liftIO (SW.bvIsNonzero (w4 sym) x)
     assertSideCondition sym p DivideByZero

assertIntDivisor ::
  W4.IsExprBuilder sym => What4 sym -> W4.SymInteger sym -> W4Eval sym ()
assertIntDivisor sym x =
  do p <- liftIO (W4.notPred (w4 sym) =<< W4.intEq (w4 sym) x =<< W4.intLit (w4 sym) 0)
     assertSideCondition sym p DivideByZero

instance W4.IsExprBuilder sym => Backend (What4 sym) where
  type SBit (What4 sym)     = W4.Pred sym
  type SWord (What4 sym)    = SW.SWord sym
  type SInteger (What4 sym) = W4.SymInteger sym
  type SFloat (What4 sym)   = FP.SFloat sym
  type SEval (What4 sym)    = W4Eval sym

  raiseError _ = evalError

  assertSideCondition _ cond err
    | Just False <- W4.asConstantPred cond = evalError err
    | otherwise = addSafety cond

  isReady (What4 sym _) m =
    case w4Eval m sym of
      Ready _ -> True
      _ -> False

  sDelayFill _ m retry =
    total
    do sym <- getSym
       doEval (w4Thunk <$> delayFill (w4Eval m sym) (w4Eval retry sym))

  sSpark _ m =
    total
    do sym   <- getSym
       doEval (w4Thunk <$> evalSpark (w4Eval m sym))


  sDeclareHole _ msg =
    total
    do (hole, fill) <- doEval (blackhole msg)
       pure ( w4Thunk hole
            , \m -> total
                    do sym <- getSym
                       doEval (fill (w4Eval m sym))
            )

  mergeEval _sym f c mx my = W4Eval
    do rx <- evalPartial mx
       ry <- evalPartial my
       case (rx, ry) of

         (W4Error err, W4Error _) ->
           pure (W4Error err) -- arbitrarily choose left error to report

         (W4Error _, W4Result p y) ->
           do p' <- w4And p =<< w4Not c
              pure (W4Result p' y)

         (W4Result p x, W4Error _) ->
           do p' <- w4And p c
              pure (W4Result p' x)

         (W4Result px x, W4Result py y) ->
           do zr <- evalPartial (f c x y)
              case zr of
                W4Error err -> pure $ W4Error err
                W4Result pz z ->
                  do p' <- w4And pz =<< w4ITE c px py
                     pure (W4Result p' z)

  wordAsChar _ bv
    | SW.bvWidth bv == 8 = toEnum . fromInteger <$> SW.bvAsUnsignedInteger bv
    | otherwise = Nothing

  wordLen _ bv = SW.bvWidth bv

  bitLit (What4 sym _) b = W4.backendPred sym b
  bitAsLit _ v = W4.asConstantPred v

  wordLit (What4 sym _) intw i
    | Just (Some w) <- someNat intw
    = case isPosNat w of
        Nothing -> pure $ SW.ZBV
        Just LeqProof -> SW.DBV <$> liftIO (W4.bvLit sym w (BV.mkBV w i))
    | otherwise = panic "what4: wordLit" ["invalid bit width:", show intw ]

  wordAsLit _ v
    | Just x <- SW.bvAsUnsignedInteger v = Just (SW.bvWidth v, x)
    | otherwise = Nothing

  integerLit (What4 sym _) i = liftIO (W4.intLit sym i)

  integerAsLit _ v = W4.asInteger v

  ppBit _ v
    | Just b <- W4.asConstantPred v = text $! if b then "True" else "False"
    | otherwise                     = text "?"

  ppWord _ opts v
    | Just x <- SW.bvAsUnsignedInteger v
    = ppBV opts (BV (SW.bvWidth v) x)

    | otherwise = text "[?]"

  ppInteger _ _opts v
    | Just x <- W4.asInteger v = integer x
    | otherwise = text "[?]"

  ppFloat _ _opts _ = text "[?]"


  iteBit (What4 sym _) c x y = liftIO (W4.itePred sym c x y)
  iteWord (What4 sym _) c x y = liftIO (SW.bvIte sym c x y)
  iteInteger (What4 sym _) c x y = liftIO (W4.intIte sym c x y)

  bitEq  (What4 sym _) x y = liftIO (W4.eqPred sym x y)
  bitAnd (What4 sym _) x y = liftIO (W4.andPred sym x y)
  bitOr  (What4 sym _) x y = liftIO (W4.orPred sym x y)
  bitXor (What4 sym _) x y = liftIO (W4.xorPred sym x y)
  bitComplement (What4 sym _) x = liftIO (W4.notPred sym x)

  wordBit (What4 sym _) bv idx = liftIO (SW.bvAtBE sym bv idx)
  wordUpdate (What4 sym _) bv idx b = liftIO (SW.bvSetBE sym bv idx b)

  packWord sym bs =
    do z <- wordLit sym (genericLength bs) 0
       let f w (idx,b) = wordUpdate sym w idx b
       foldM f z (zip [0..] bs)

  unpackWord (What4 sym _) bv = liftIO $
    mapM (SW.bvAtBE sym bv) [0 .. SW.bvWidth bv-1]

  joinWord (What4 sym _) x y = liftIO $ SW.bvJoin sym x y

  splitWord _sym 0 _ bv = pure (SW.ZBV, bv)
  splitWord _sym _ 0 bv = pure (bv, SW.ZBV)
  splitWord (What4 sym _) lw rw bv = liftIO $
    do l <- SW.bvSliceBE sym 0 lw bv
       r <- SW.bvSliceBE sym lw rw bv
       return (l, r)

  extractWord (What4 sym _) bits idx bv =
    liftIO $ SW.bvSliceBE sym idx bits bv

  wordEq                (What4 sym _) x y = liftIO (SW.bvEq sym x y)
  wordLessThan          (What4 sym _) x y = liftIO (SW.bvult sym x y)
  wordGreaterThan       (What4 sym _) x y = liftIO (SW.bvugt sym x y)
  wordSignedLessThan    (What4 sym _) x y = liftIO (SW.bvslt sym x y)

  wordOr  (What4 sym _) x y = liftIO (SW.bvOr sym x y)
  wordAnd (What4 sym _) x y = liftIO (SW.bvAnd sym x y)
  wordXor (What4 sym _) x y = liftIO (SW.bvXor sym x y)
  wordComplement (What4 sym _) x = liftIO (SW.bvNot sym x)

  wordPlus  (What4 sym _) x y = liftIO (SW.bvAdd sym x y)
  wordMinus (What4 sym _) x y = liftIO (SW.bvSub sym x y)
  wordMult  (What4 sym _) x y = liftIO (SW.bvMul sym x y)
  wordNegate (What4 sym _) x  = liftIO (SW.bvNeg sym x)
  wordLg2 (What4 sym _) x     = sLg2 sym x
 
  wordDiv sym x y =
     do assertBVDivisor sym y
        liftIO (SW.bvUDiv (w4 sym) x y)
  wordMod sym x y =
     do assertBVDivisor sym y
        liftIO (SW.bvURem (w4 sym) x y)
  wordSignedDiv sym x y =
     do assertBVDivisor sym y
        liftIO (SW.bvSDiv (w4 sym) x y)
  wordSignedMod sym x y =
     do assertBVDivisor sym y
        liftIO (SW.bvSRem (w4 sym) x y)

  wordToInt (What4 sym _) x = liftIO (SW.bvToInteger sym x)
  wordFromInt (What4 sym _) width i = liftIO (SW.integerToBV sym i width)

  intPlus (What4 sym _) x y  = liftIO $ W4.intAdd sym x y
  intMinus (What4 sym _) x y = liftIO $ W4.intSub sym x y
  intMult (What4 sym _) x y  = liftIO $ W4.intMul sym x y
  intNegate (What4 sym _) x  = liftIO $ W4.intNeg sym x

  -- NB: What4's division operation provides SMTLib's euclidean division,
  -- which doesn't match the round-to-neg-infinity semantics of Cryptol,
  -- so we have to do some work to get the desired semantics.
  intDiv sym@(What4 w4sym _) x y =
    do assertIntDivisor sym y
       liftIO $ do
         neg <- liftIO (W4.intLt w4sym y =<< W4.intLit w4sym 0)
         case W4.asConstantPred neg of
           Just False -> W4.intDiv w4sym x y
           Just True  ->
              do xneg <- W4.intNeg w4sym x
                 yneg <- W4.intNeg w4sym y
                 W4.intDiv w4sym xneg yneg
           Nothing ->
              do xneg <- W4.intNeg w4sym x
                 yneg <- W4.intNeg w4sym y
                 zneg <- W4.intDiv w4sym xneg yneg
                 z    <- W4.intDiv w4sym x y
                 W4.intIte w4sym neg zneg z

  -- NB: What4's division operation provides SMTLib's euclidean division,
  -- which doesn't match the round-to-neg-infinity semantics of Cryptol,
  -- so we have to do some work to get the desired semantics.
  intMod sym@(What4 w4sym _) x y =
    do assertIntDivisor sym y
       liftIO $ do
         neg <- liftIO (W4.intLt w4sym y =<< W4.intLit w4sym 0)
         case W4.asConstantPred neg of
           Just False -> W4.intMod w4sym x y
           Just True  ->
              do xneg <- W4.intNeg w4sym x
                 yneg <- W4.intNeg w4sym y
                 W4.intNeg w4sym =<< W4.intMod w4sym xneg yneg
           Nothing ->
              do xneg <- W4.intNeg w4sym x
                 yneg <- W4.intNeg w4sym y
                 z    <- W4.intMod w4sym x y
                 zneg <- W4.intNeg w4sym =<< W4.intMod w4sym xneg yneg
                 W4.intIte w4sym neg zneg z

  intEq (What4 sym _) x y = liftIO $ W4.intEq sym x y
  intLessThan (What4 sym _) x y = liftIO $ W4.intLt sym x y
  intGreaterThan (What4 sym _) x y = liftIO $ W4.intLt sym y x

  -- NB, we don't do reduction here on symbolic values
  intToZn (What4 sym _) m x
    | Just xi <- W4.asInteger x
    = liftIO $ W4.intLit sym (xi `mod` m)

    | otherwise
    = pure x

  znToInt _ 0 _ = evalPanic "znToInt" ["0 modulus not allowed"]
  znToInt (What4 sym _) m x = liftIO (W4.intMod sym x =<< W4.intLit sym m)

  znEq _ 0 _ _ = evalPanic "znEq" ["0 modulus not allowed"]
  znEq (What4 sym _) m x y = liftIO $
     do diff <- W4.intSub sym x y
        W4.intDivisible sym diff (fromInteger m)

  znPlus   (What4 sym _) m x y = liftIO $ sModAdd sym m x y
  znMinus  (What4 sym _) m x y = liftIO $ sModSub sym m x y
  znMult   (What4 sym _) m x y = liftIO $ sModMult sym m x y
  znNegate (What4 sym _) m x   = liftIO $ sModNegate sym m x

  --------------------------------------------------------------

  fpLit (What4 sym _) e p r = liftIO $ FP.fpFromRationalLit sym e p r

  fpExactLit (What4 sym _) BF{ bfExpWidth = e, bfPrecWidth = p, bfValue = bf } =
    liftIO (FP.fpFromBinary sym e p =<< SW.bvLit sym (e+p) (floatToBits e p bf))

  fpEq          (What4 sym _) x y = liftIO $ FP.fpEqIEEE sym x y
  fpLessThan    (What4 sym _) x y = liftIO $ FP.fpLtIEEE sym x y
  fpGreaterThan (What4 sym _) x y = liftIO $ FP.fpGtIEEE sym x y
  fpLogicalEq   (What4 sym _) x y = liftIO $ FP.fpEq sym x y

  fpPlus  = fpBinArith FP.fpAdd
  fpMinus = fpBinArith FP.fpSub
  fpMult  = fpBinArith FP.fpMul
  fpDiv   = fpBinArith FP.fpDiv

  fpNeg (What4 sym _) x = liftIO $ FP.fpNeg sym x

  fpFromInteger sym@(What4 w4sym _) e p r x =
    do rm <- fpRoundingMode sym r
       liftIO $ FP.fpFromInteger w4sym e p rm x

  fpToInteger = fpCvtToInteger

sModAdd :: W4.IsExprBuilder sym =>
  sym -> Integer -> W4.SymInteger sym -> W4.SymInteger sym -> IO (W4.SymInteger sym)
sModAdd _sym 0 _ _ = evalPanic "sModAdd" ["0 modulus not allowed"]
sModAdd sym m x y
  | Just xi <- W4.asInteger x
  , Just yi <- W4.asInteger y
  = W4.intLit sym ((xi+yi) `mod` m)

  | otherwise
  = W4.intAdd sym x y

sModSub :: W4.IsExprBuilder sym =>
  sym -> Integer -> W4.SymInteger sym -> W4.SymInteger sym -> IO (W4.SymInteger sym)
sModSub _sym 0 _ _ = evalPanic "sModSub" ["0 modulus not allowed"]
sModSub sym m x y
  | Just xi <- W4.asInteger x
  , Just yi <- W4.asInteger y
  = W4.intLit sym ((xi-yi) `mod` m)

  | otherwise
  = W4.intSub sym x y


sModMult :: W4.IsExprBuilder sym =>
  sym -> Integer -> W4.SymInteger sym -> W4.SymInteger sym -> IO (W4.SymInteger sym)
sModMult _sym 0 _ _ = evalPanic "sModMult" ["0 modulus not allowed"]
sModMult sym m x y
  | Just xi <- W4.asInteger x
  , Just yi <- W4.asInteger y
  = W4.intLit sym ((xi*yi) `mod` m)

  | otherwise
  = W4.intMul sym x y

sModNegate :: W4.IsExprBuilder sym =>
  sym -> Integer -> W4.SymInteger sym -> IO (W4.SymInteger sym)
sModNegate _sym 0 _ = evalPanic "sModMult" ["0 modulus not allowed"]
sModNegate sym m x
  | Just xi <- W4.asInteger x
  = W4.intLit sym ((negate xi) `mod` m)

  | otherwise
  = W4.intNeg sym x


-- | Try successive powers of 2 to find the first that dominates the input.
--   We could perhaps reduce to using CLZ instead...
sLg2 :: W4.IsExprBuilder sym => sym -> SW.SWord sym -> SEval (What4 sym) (SW.SWord sym)
sLg2 sym x = liftIO $ go 0
  where
  w = SW.bvWidth x
  lit n = SW.bvLit sym w (toInteger n)

  go i | toInteger i < w =
       do p <- SW.bvule sym x =<< lit (bit i)
          lazyIte (SW.bvIte sym) p (lit i) (go (i+1))

  -- base case, should only happen when i = w
  go i = lit i



-- Errors ----------------------------------------------------------------------

evalPanic :: String -> [String] -> a
evalPanic cxt = panic ("[What4 Symbolic]" ++ cxt)


lazyIte ::
  (W4.IsExpr p, Monad m) =>
  (p W4.BaseBoolType -> a -> a -> m a) ->
  p W4.BaseBoolType ->
  m a ->
  m a ->
  m a
lazyIte f c mx my
  | Just b <- W4.asConstantPred c = if b then mx else my
  | otherwise =
      do x <- mx
         y <- my
         f c x y

indexFront_int ::
  W4.IsExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  SeqMap (What4 sym) ->
  TValue ->
  SInteger (What4 sym) ->
  SEval (What4 sym) (Value sym)
indexFront_int sym@(What4 w4sym _) mblen _a xs ix idx
  | Just i <- W4.asInteger idx
  = lookupSeqMap xs i

  | (lo, Just hi) <- bounds
  = foldr f def [lo .. hi]

  | otherwise
  = liftIO (X.throw (UnsupportedSymbolicOp "unbounded integer indexing"))

 where
    def = raiseError sym (InvalidIndex Nothing)

    f n y =
       do p <- liftIO (W4.intEq w4sym idx =<< W4.intLit w4sym n)
          iteValue sym p (lookupSeqMap xs n) y

    bounds =
      (case W4.rangeLowBound (W4.integerBounds idx) of
        W4.Inclusive l -> max l 0
        _ -> 0
      , case (maxIdx, W4.rangeHiBound (W4.integerBounds idx)) of
          (Just n, W4.Inclusive h) -> Just (min n h)
          (Just n, _)              -> Just n
          _                        -> Nothing
      )

    -- Maximum possible in-bounds index given `Z m`
    -- type information and the length
    -- of the sequence. If the sequences is infinite and the
    -- integer is unbounded, there isn't much we can do.
    maxIdx =
      case (mblen, ix) of
        (Nat n, TVIntMod m)  -> Just (min (toInteger n) (toInteger m))
        (Nat n, _)           -> Just n
        (_    , TVIntMod m)  -> Just m
        _                    -> Nothing

indexBack_int ::
  W4.IsExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  SeqMap (What4 sym) ->
  TValue ->
  SInteger (What4 sym) ->
  SEval (What4 sym) (Value sym)
indexBack_int sym (Nat n) a xs ix idx = indexFront_int sym (Nat n) a (reverseSeqMap n xs) ix idx
indexBack_int _ Inf _ _ _ _ = evalPanic "Expected finite sequence" ["indexBack_int"]

indexFront_word ::
  W4.IsExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  SeqMap (What4 sym) ->
  TValue ->
  SWord (What4 sym) ->
  SEval (What4 sym) (Value sym)
indexFront_word sym@(What4 w4sym _) mblen _a xs _ix idx
  | Just i <- SW.bvAsUnsignedInteger idx
  = lookupSeqMap xs i

  | otherwise
  = foldr f def idxs

 where
    w = SW.bvWidth idx
    def = raiseError sym (InvalidIndex Nothing)

    f n y =
       do p <- liftIO (SW.bvEq w4sym idx =<< SW.bvLit w4sym w n)
          iteValue sym p (lookupSeqMap xs n) y

    -- maximum possible in-bounds index given the bitwidth
    -- of the index value and the length of the sequence
    maxIdx =
      case mblen of
        Nat n | n < 2^w -> n-1
        _ -> 2^w - 1

    -- concrete indices to consider, intersection of the
    -- range of values the index value might take with
    -- the legal values
    idxs =
      case SW.unsignedBVBounds idx of
        Just (lo, hi) -> [lo .. min hi maxIdx]
        _ -> [0 .. maxIdx]

indexBack_word ::
  W4.IsExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  SeqMap (What4 sym) ->
  TValue ->
  SWord (What4 sym) ->
  SEval (What4 sym) (Value sym)
indexBack_word sym (Nat n) a xs ix idx = indexFront_word sym (Nat n) a (reverseSeqMap n xs) ix idx
indexBack_word _ Inf _ _ _ _ = evalPanic "Expected finite sequence" ["indexBack_word"]

indexFront_bits :: forall sym.
  W4.IsExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  SeqMap (What4 sym) ->
  TValue ->
  [SBit (What4 sym)] ->
  SEval (What4 sym) (Value sym)
indexFront_bits sym mblen _a xs _ix bits0 = go 0 (length bits0) bits0
 where
  go :: Integer -> Int -> [W4.Pred sym] -> W4Eval sym (Value sym)
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
  W4.IsExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  SeqMap (What4 sym) ->
  TValue ->
  [SBit (What4 sym)] ->
  SEval (What4 sym) (Value sym)
indexBack_bits sym (Nat n) a xs ix idx = indexFront_bits sym (Nat n) a (reverseSeqMap n xs) ix idx
indexBack_bits _ Inf _ _ _ _ = evalPanic "Expected finite sequence" ["indexBack_bits"]


-- | Compare a symbolic word value with a concrete integer.
wordValueEqualsInteger :: forall sym.
  W4.IsExprBuilder sym =>
  What4 sym ->
  WordValue (What4 sym) ->
  Integer ->
  W4Eval sym (W4.Pred sym)
wordValueEqualsInteger sym@(What4 w4sym _) wv i
  | wordValueSize sym wv < widthInteger i = return (W4.falsePred w4sym)
  | otherwise =
    case wv of
      WordVal w -> liftIO (SW.bvEq w4sym w =<< SW.bvLit w4sym (SW.bvWidth w) i)
      _ -> liftIO . bitsAre i =<< enumerateWordValueRev sym wv -- little-endian
  where
    bitsAre :: Integer -> [W4.Pred sym] -> IO (W4.Pred sym)
    bitsAre n [] = pure (W4.backendPred w4sym (n == 0))
    bitsAre n (b : bs) =
      do pb  <- bitIs (testBit n 0) b
         pbs <- bitsAre (n `shiftR` 1) bs
         W4.andPred w4sym pb pbs

    bitIs :: Bool -> W4.Pred sym -> IO (W4.Pred sym)
    bitIs b x = if b then pure x else W4.notPred w4sym x

updateFrontSym ::
  W4.IsExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  SeqMap (What4 sym) ->
  Either (SInteger (What4 sym)) (WordValue (What4 sym)) ->
  SEval (What4 sym) (Value sym) ->
  SEval (What4 sym) (SeqMap (What4 sym))
updateFrontSym sym _len _eltTy vs (Left idx) val =
  case W4.asInteger idx of
    Just i -> return $ updateSeqMap vs i val
    Nothing -> return $ IndexSeqMap $ \i ->
      do b <- intEq sym idx =<< integerLit sym i
         iteValue sym b val (lookupSeqMap vs i)

updateFrontSym sym _len _eltTy vs (Right wv) val =
  case wv of
    WordVal w | Just j <- SW.bvAsUnsignedInteger w ->
      return $ updateSeqMap vs j val
    _ ->
      memoMap $ IndexSeqMap $ \i ->
      do b <- wordValueEqualsInteger sym wv i
         iteValue sym b val (lookupSeqMap vs i)

updateBackSym ::
  W4.IsExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  SeqMap (What4 sym) ->
  Either (SInteger (What4 sym)) (WordValue (What4 sym)) ->
  SEval (What4 sym) (Value sym) ->
  SEval (What4 sym) (SeqMap (What4 sym))
updateBackSym _ Inf _ _ _ _ = evalPanic "Expected finite sequence" ["updateBackSym"]

updateBackSym sym (Nat n) _eltTy vs (Left idx) val =
  case W4.asInteger idx of
    Just i -> return $ updateSeqMap vs (n - 1 - i) val
    Nothing -> return $ IndexSeqMap $ \i ->
      do b <- intEq sym idx =<< integerLit sym (n - 1 - i)
         iteValue sym b val (lookupSeqMap vs i)

updateBackSym sym (Nat n) _eltTy vs (Right wv) val =
  case wv of
    WordVal w | Just j <- SW.bvAsUnsignedInteger w ->
      return $ updateSeqMap vs (n - 1 - j) val
    _ ->
      memoMap $ IndexSeqMap $ \i ->
      do b <- wordValueEqualsInteger sym wv (n - 1 - i)
         iteValue sym b val (lookupSeqMap vs i)


updateFrontSym_word ::
  W4.IsExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  WordValue (What4 sym) ->
  Either (SInteger (What4 sym)) (WordValue (What4 sym)) ->
  SEval (What4 sym) (GenValue (What4 sym)) ->
  SEval (What4 sym) (WordValue (What4 sym))
updateFrontSym_word _ Inf _ _ _ _ = evalPanic "Expected finite sequence" ["updateFrontSym_word"]

updateFrontSym_word sym (Nat _) eltTy (LargeBitsVal n bv) idx val =
  LargeBitsVal n <$> updateFrontSym sym (Nat n) eltTy bv idx val

updateFrontSym_word sym (Nat n) eltTy (WordVal bv) (Left idx) val =
  do idx' <- wordFromInt sym n idx
     updateFrontSym_word sym (Nat n) eltTy (WordVal bv) (Right (WordVal idx')) val

updateFrontSym_word sym@(What4 w4sym _) (Nat n) eltTy bv (Right wv) val =
  case wv of
    WordVal idx
      | Just j <- SW.bvAsUnsignedInteger idx ->
          updateWordValue sym bv j (fromVBit <$> val)

      | WordVal bw <- bv ->
        WordVal <$>
          do b <- fromVBit <$> val
             let sz = SW.bvWidth bw
             highbit <- liftIO (SW.bvLit w4sym sz (bit (fromInteger (sz-1))))
             msk <- w4bvLshr w4sym highbit idx
             liftIO $
               case W4.asConstantPred b of
                 Just True  -> SW.bvOr  w4sym bw msk
                 Just False -> SW.bvAnd w4sym bw =<< SW.bvNot w4sym msk
                 Nothing ->
                   do q <- SW.bvFill w4sym sz b
                      bw' <- SW.bvAnd w4sym bw =<< SW.bvNot w4sym msk
                      SW.bvXor w4sym bw' =<< SW.bvAnd w4sym q msk

    _ -> LargeBitsVal (wordValueSize sym wv) <$>
           updateFrontSym sym (Nat n) eltTy (asBitsMap sym bv) (Right wv) val


updateBackSym_word ::
  W4.IsExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  WordValue (What4 sym) ->
  Either (SInteger (What4 sym)) (WordValue (What4 sym)) ->
  SEval (What4 sym) (GenValue (What4 sym)) ->
  SEval (What4 sym) (WordValue (What4 sym))
updateBackSym_word _ Inf _ _ _ _ = evalPanic "Expected finite sequence" ["updateBackSym_word"]

updateBackSym_word sym (Nat _) eltTy (LargeBitsVal n bv) idx val =
  LargeBitsVal n <$> updateBackSym sym (Nat n) eltTy bv idx val

updateBackSym_word sym (Nat n) eltTy (WordVal bv) (Left idx) val =
  do idx' <- wordFromInt sym n idx
     updateBackSym_word sym (Nat n) eltTy (WordVal bv) (Right (WordVal idx')) val

updateBackSym_word sym@(What4 w4sym _) (Nat n) eltTy bv (Right wv) val =
  case wv of
    WordVal idx
      | Just j <- SW.bvAsUnsignedInteger idx ->
          updateWordValue sym bv (n - 1 - j) (fromVBit <$> val)

      | WordVal bw <- bv ->
        WordVal <$>
          do b <- fromVBit <$> val
             let sz = SW.bvWidth bw
             lowbit <- liftIO (SW.bvLit w4sym sz 1)
             msk <- w4bvShl w4sym lowbit idx
             liftIO $
               case W4.asConstantPred b of
                 Just True  -> SW.bvOr  w4sym bw msk
                 Just False -> SW.bvAnd w4sym bw =<< SW.bvNot w4sym msk
                 Nothing ->
                   do q <- SW.bvFill w4sym sz b
                      bw' <- SW.bvAnd w4sym bw =<< SW.bvNot w4sym msk
                      SW.bvXor w4sym bw' =<< SW.bvAnd w4sym q msk

    _ -> LargeBitsVal (wordValueSize sym wv) <$>
           updateBackSym sym (Nat n) eltTy (asBitsMap sym bv) (Right wv) val


sshrV :: W4.IsExprBuilder sym => What4 sym -> Value sym
sshrV sym =
  nlam $ \(Nat n) ->
  tlam $ \ix ->
  wlam sym $ \x -> return $
  lam $ \y ->
    y >>= asIndex sym ">>$" ix >>= \case
       Left i ->
         do pneg <- intLessThan sym i =<< integerLit sym 0
            zneg <- do i' <- shiftShrink sym (Nat n) ix =<< intNegate sym i
                       amt <- wordFromInt sym n i'
                       w4bvShl (w4 sym) x amt
            zpos <- do i' <- shiftShrink sym (Nat n) ix i
                       amt <- wordFromInt sym n i'
                       w4bvAshr (w4 sym) x amt
            return (VWord (SW.bvWidth x) (WordVal <$> iteWord sym pneg zneg zpos))

       Right wv ->
         do amt <- asWordVal sym wv
            return (VWord (SW.bvWidth x) (WordVal <$> w4bvAshr (w4 sym) x amt))


w4bvShl  :: W4.IsExprBuilder sym => sym -> SW.SWord sym -> SW.SWord sym -> W4Eval sym (SW.SWord sym)
w4bvShl sym x y = liftIO $ SW.bvShl sym x y

w4bvLshr  :: W4.IsExprBuilder sym => sym -> SW.SWord sym -> SW.SWord sym -> W4Eval sym (SW.SWord sym)
w4bvLshr sym x y = liftIO $ SW.bvLshr sym x y

w4bvAshr :: W4.IsExprBuilder sym => sym -> SW.SWord sym -> SW.SWord sym -> W4Eval sym (SW.SWord sym)
w4bvAshr sym x y = liftIO $ SW.bvAshr sym x y

w4bvRol  :: W4.IsExprBuilder sym => sym -> SW.SWord sym -> SW.SWord sym -> W4Eval sym (SW.SWord sym)
w4bvRol sym x y = liftIO $ SW.bvRol sym x y

w4bvRor  :: W4.IsExprBuilder sym => sym -> SW.SWord sym -> SW.SWord sym -> W4Eval sym (SW.SWord sym)
w4bvRor sym x y = liftIO $ SW.bvRor sym x y



fpRoundingMode ::
  W4.IsExprBuilder sym =>
  What4 sym -> SWord (What4 sym) -> SEval (What4 sym) W4.RoundingMode
fpRoundingMode sym v =
  case wordAsLit sym v of
    Just (_w,i) ->
      case i of
        0 -> pure W4.RNE
        1 -> pure W4.RNA
        2 -> pure W4.RTP
        3 -> pure W4.RTN
        4 -> pure W4.RTZ
        x -> raiseError sym (BadRoundingMode x)
    _ -> liftIO $ X.throwIO $ UnsupportedSymbolicOp "rounding mode"

fpBinArith ::
  W4.IsExprBuilder sym =>
  FP.SFloatBinArith sym ->
  What4 sym ->
  SWord (What4 sym) ->
  SFloat (What4 sym) ->
  SFloat (What4 sym) ->
  SEval (What4 sym) (SFloat (What4 sym))
fpBinArith fun = \sym@(What4 s _) r x y ->
  do m <- fpRoundingMode sym r
     liftIO (fun s m x y)


fpCvtToInteger ::
  (W4.IsExprBuilder sy, sym ~ What4 sy) =>
  sym -> String -> SWord sym -> SFloat sym -> SEval sym (SInteger sym)
fpCvtToInteger sym@(What4 sy _) fun r x =
  do grd <- liftIO
              do bad1 <- FP.fpIsInf sy x
                 bad2 <- FP.fpIsNaN sy x
                 W4.notPred sy =<< W4.orPred sy bad1 bad2
     assertSideCondition sym grd (BadValue fun)
     rnd  <- fpRoundingMode sym r
     liftIO
       do y <- FP.fpToReal sy x
          case rnd of
            W4.RNE -> W4.realRoundEven sy y
            W4.RNA -> W4.realRound sy y
            W4.RTP -> W4.realCeil sy y
            W4.RTN -> W4.realFloor sy y
            W4.RTZ -> W4.realTrunc sy y


fpCvtToRational ::
  (W4.IsSymExprBuilder sy, sym ~ What4 sy) =>
  sym -> SFloat sym -> SEval sym (SRational sym)
fpCvtToRational sym@(What4 w4sym _) fp =
  do grd <- liftIO
            do bad1 <- FP.fpIsInf w4sym fp
               bad2 <- FP.fpIsNaN w4sym fp
               W4.notPred w4sym =<< W4.orPred w4sym bad1 bad2
     assertSideCondition sym grd (BadValue "fpToRational")
     (rel,x,y) <- liftIO (FP.fpToRational w4sym fp)
     addDefEqn sym =<< liftIO (W4.impliesPred w4sym grd rel)
     ratio sym x y

fpCvtFromRational ::
  (W4.IsExprBuilder sy, sym ~ What4 sy) =>
  sym -> Integer -> Integer -> SWord sym ->
  SRational sym -> SEval sym (SFloat sym)
fpCvtFromRational sym@(What4 w4sym _) e p r rat =
  do rnd <- fpRoundingMode sym r
     liftIO (FP.fpFromRational w4sym e p rnd (sNum rat) (sDenom rat))
