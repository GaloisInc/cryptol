-- |
-- Module      :  Cryptol.Backend.What4
-- Copyright   :  (c) 2020 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com

{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
module Cryptol.Backend.What4 where


import qualified Control.Exception as X
import           Control.Concurrent.MVar
import           Control.Monad (foldM,ap,liftM)
import           Control.Monad.IO.Class
import           Data.Bits (bit)
import qualified Data.BitVector.Sized as BV
import           Data.List
import           Data.Map (Map)
import           Data.Set (Set)
import           Data.Text (Text)
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some

import qualified GHC.Num.Compat as Integer

import qualified What4.Interface as W4
import qualified What4.SWord as SW
import qualified What4.SFloat as FP

import Cryptol.Backend
import Cryptol.Backend.FloatHelpers
import Cryptol.Backend.Monad
   ( Eval(..), EvalError(..), EvalErrorEx(..)
   , Unsupported(..), delayFill, blackhole, evalSpark
   , modifyCallStack, getCallStack, maybeReady
   )
import Cryptol.Utils.Panic


data What4 sym =
  What4
  { w4  :: sym
  , w4defs :: MVar (W4.Pred sym)
  , w4funs :: MVar (What4FunCache sym)
  , w4uninterpWarns :: MVar (Set Text)
  }

type What4FunCache sym = Map Text (SomeSymFn sym)

data SomeSymFn sym =
  forall args ret. SomeSymFn (W4.SymFn sym args ret)

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
  = W4Error !EvalErrorEx
    -- ^ A malformed value

  | W4Result !(W4.Pred sym) !a
    -- ^ safety predicate and result: the result only makes sense when
    -- the predicate holds.
 deriving Functor

--------------------------------------------------------------------------------
-- Moving between the layers

w4Eval :: W4Eval sym a -> sym -> Eval (W4Result sym a)
w4Eval (W4Eval (W4Conn m)) = m

w4Thunk :: Eval (W4Result sym a) -> W4Eval sym a
w4Thunk m = W4Eval (W4Conn \_ -> m)

-- | A value with no context.
doEval :: W4.IsSymExprBuilder sym => Eval a -> W4Conn sym a
doEval m = W4Conn \_sym -> m

-- | A total value.
total :: W4.IsSymExprBuilder sym => W4Conn sym a -> W4Eval sym a
total m = W4Eval
  do sym <- getSym
     W4Result (W4.backendPred sym True) <$> m

--------------------------------------------------------------------------------
-- Operations in WConn

instance W4.IsSymExprBuilder sym => Functor (W4Conn sym) where
  fmap = liftM

instance W4.IsSymExprBuilder sym => Applicative (W4Conn sym) where
  pure   = doEval . pure
  (<*>)  = ap

instance W4.IsSymExprBuilder sym => Monad (W4Conn sym) where
  m1 >>= f = W4Conn \sym ->
    do res1 <- evalConn m1 sym
       evalConn (f res1) sym

instance W4.IsSymExprBuilder sym => MonadIO (W4Conn sym) where
  liftIO = doEval . liftIO

-- | Access the symbolic back-end
getSym :: W4Conn sym sym
getSym = W4Conn \sym -> pure sym

-- | Record a definition.
--addDef :: W4.Pred sym -> W4Conn sym ()
--addDef p = W4Conn \_ -> pure W4Defs { w4Defs = p, w4Result = () }

-- | Compute conjunction.
w4And :: W4.IsSymExprBuilder sym =>
         W4.Pred sym -> W4.Pred sym -> W4Conn sym (W4.Pred sym)
w4And p q =
  do sym <- getSym
     liftIO (W4.andPred sym p q)

-- | Compute negation.
w4Not :: W4.IsSymExprBuilder sym => W4.Pred sym -> W4Conn sym (W4.Pred sym)
w4Not p =
  do sym <- getSym
     liftIO (W4.notPred sym p)

-- | Compute if-then-else.
w4ITE :: W4.IsSymExprBuilder sym =>
         W4.Pred sym -> W4.Pred sym -> W4.Pred sym -> W4Conn sym (W4.Pred sym)
w4ITE ifP ifThen ifElse =
  do sym <- getSym
     liftIO (W4.itePred sym ifP ifThen ifElse)



--------------------------------------------------------------------------------
-- Operations in W4Eval

instance W4.IsSymExprBuilder sym => Functor (W4Eval sym) where
  fmap = liftM

instance W4.IsSymExprBuilder sym => Applicative (W4Eval sym) where
  pure  = total . pure
  (<*>) = ap

instance W4.IsSymExprBuilder sym => Monad (W4Eval sym) where
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

instance W4.IsSymExprBuilder sym => MonadIO (W4Eval sym) where
  liftIO = total . liftIO


-- | Add a definitional equation.
-- This will always be asserted when we make queries to the solver.
addDefEqn :: W4.IsSymExprBuilder sym => What4 sym -> W4.Pred sym -> W4Eval sym ()
addDefEqn sym p =
  liftIO (modifyMVar_ (w4defs sym) (W4.andPred (w4 sym) p))

-- | Add s safety condition.
addSafety :: W4.IsSymExprBuilder sym => W4.Pred sym -> W4Eval sym ()
addSafety p = W4Eval (pure (W4Result p ()))

-- | A fully undefined symbolic value
evalError :: W4.IsSymExprBuilder sym => EvalError -> W4Eval sym a
evalError err = W4Eval $ W4Conn $ \_sym ->
  do stk <- getCallStack
     pure (W4Error (EvalErrorEx stk err))

--------------------------------------------------------------------------------


assertBVDivisor :: W4.IsSymExprBuilder sym => What4 sym -> SW.SWord sym -> W4Eval sym ()
assertBVDivisor sym x =
  do p <- liftIO (SW.bvIsNonzero (w4 sym) x)
     assertSideCondition sym p DivideByZero

assertIntDivisor ::
  W4.IsSymExprBuilder sym => What4 sym -> W4.SymInteger sym -> W4Eval sym ()
assertIntDivisor sym x =
  do p <- liftIO (W4.notPred (w4 sym) =<< W4.intEq (w4 sym) x =<< W4.intLit (w4 sym) 0)
     assertSideCondition sym p DivideByZero

instance W4.IsSymExprBuilder sym => Backend (What4 sym) where
  type SBit (What4 sym)     = W4.Pred sym
  type SWord (What4 sym)    = SW.SWord sym
  type SInteger (What4 sym) = W4.SymInteger sym
  type SFloat (What4 sym)   = FP.SFloat sym
  type SEval (What4 sym)    = W4Eval sym

  raiseError _ = evalError

  assertSideCondition _ cond err
    | Just False <- W4.asConstantPred cond = evalError err
    | otherwise = addSafety cond

  isReady sym m = W4Eval $ W4Conn $ \_ ->
    maybeReady (w4Eval m (w4 sym)) >>= \case
      Just x  -> pure (Just <$> x)
      Nothing -> pure (W4Result (W4.backendPred (w4 sym) True) Nothing)

  sDelayFill _ m retry msg =
    total
    do sym <- getSym
       doEval (w4Thunk <$> delayFill (w4Eval m sym) (w4Eval <$> retry <*> pure sym) msg)

  sSpark _ m =
    total
    do sym   <- getSym
       doEval (w4Thunk <$> evalSpark (w4Eval m sym))

  sModifyCallStack _ f (W4Eval (W4Conn m)) =
    W4Eval (W4Conn \sym -> modifyCallStack f (m sym))

  sGetCallStack _ = total (doEval getCallStack)

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

  wordLen' _ bv = SW.bvWidth bv
  {-# INLINE wordLen' #-}

  bitLit sym b = W4.backendPred (w4 sym) b
  bitAsLit _ v = W4.asConstantPred v

  wordLit sym intw i
    | Just (Some w) <- someNat intw
    = case isPosNat w of
        Nothing -> pure $ SW.ZBV
        Just LeqProof -> SW.DBV <$> liftIO (W4.bvLit (w4 sym) w (BV.mkBV w i))
    | otherwise = panic "what4: wordLit" ["invalid bit width:", show intw ]

  wordAsLit _ v
    | Just x <- SW.bvAsUnsignedInteger v = Just (SW.bvWidth v, x)
    | otherwise = Nothing

  integerLit sym i = liftIO (W4.intLit (w4 sym) i)

  integerAsLit _ v = W4.asInteger v

  iteBit sym c x y = liftIO (W4.itePred (w4 sym) c x y)
  iteWord sym c x y = liftIO (SW.bvIte (w4 sym) c x y)
  iteInteger sym c x y = liftIO (W4.intIte (w4 sym) c x y)
  iteFloat sym p x y = liftIO (FP.fpIte (w4 sym) p x y)

  bitEq  sym x y = liftIO (W4.eqPred (w4 sym) x y)
  bitAnd sym x y = liftIO (W4.andPred (w4 sym) x y)
  bitOr  sym x y = liftIO (W4.orPred (w4 sym) x y)
  bitXor sym x y = liftIO (W4.xorPred (w4 sym) x y)
  bitComplement sym x = liftIO (W4.notPred (w4 sym) x)

  wordBit sym bv idx = liftIO (SW.bvAtBE (w4 sym) bv idx)
  wordUpdate sym bv idx b = liftIO (SW.bvSetBE (w4 sym) bv idx b)

  packWord sym bs =
    do z <- wordLit sym (genericLength bs) 0
       let f w (idx,b) = wordUpdate sym w idx b
       foldM f z (zip [0..] bs)

  unpackWord sym bv = liftIO $
    mapM (SW.bvAtBE (w4 sym) bv) [0 .. SW.bvWidth bv-1]

  joinWord sym x y = liftIO $ SW.bvJoin (w4 sym) x y

  splitWord _sym 0 _ bv = pure (SW.ZBV, bv)
  splitWord _sym _ 0 bv = pure (bv, SW.ZBV)
  splitWord sym lw rw bv = liftIO $
    do l <- SW.bvSliceBE (w4 sym) 0 lw bv
       r <- SW.bvSliceBE (w4 sym) lw rw bv
       return (l, r)

  extractWord sym bits idx bv =
    liftIO $ SW.bvSliceLE (w4 sym) idx bits bv

  wordEq                sym x y = liftIO (SW.bvEq  (w4 sym) x y)
  wordLessThan          sym x y = liftIO (SW.bvult (w4 sym) x y)
  wordGreaterThan       sym x y = liftIO (SW.bvugt (w4 sym) x y)
  wordSignedLessThan    sym x y = liftIO (SW.bvslt (w4 sym) x y)

  wordOr  sym x y = liftIO (SW.bvOr  (w4 sym) x y)
  wordAnd sym x y = liftIO (SW.bvAnd (w4 sym) x y)
  wordXor sym x y = liftIO (SW.bvXor (w4 sym) x y)
  wordComplement sym x = liftIO (SW.bvNot (w4 sym) x)

  wordPlus   sym x y = liftIO (SW.bvAdd (w4 sym) x y)
  wordMinus  sym x y = liftIO (SW.bvSub (w4 sym) x y)
  wordMult   sym x y = liftIO (SW.bvMul (w4 sym) x y)
  wordNegate sym x   = liftIO (SW.bvNeg (w4 sym) x)
  wordLg2    sym x   = sLg2 (w4 sym) x

  wordShiftLeft   sym x y = w4bvShl (w4 sym) x y
  wordShiftRight  sym x y = w4bvLshr (w4 sym) x y
  wordRotateLeft  sym x y = w4bvRol (w4 sym) x y
  wordRotateRight sym x y = w4bvRor (w4 sym) x y
  wordSignedShiftRight sym x y = w4bvAshr (w4 sym) x y

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

  wordToInt sym x = liftIO (SW.bvToInteger (w4 sym) x)
  wordToSignedInt sym x = liftIO (SW.sbvToInteger (w4 sym) x)
  wordFromInt sym width i = liftIO (SW.integerToBV (w4 sym) i width)

  intPlus   sym x y  = liftIO $ W4.intAdd (w4 sym) x y
  intMinus  sym x y  = liftIO $ W4.intSub (w4 sym) x y
  intMult   sym x y  = liftIO $ W4.intMul (w4 sym) x y
  intNegate sym x    = liftIO $ W4.intNeg (w4 sym) x

  -- NB: What4's division operation provides SMTLib's euclidean division,
  -- which doesn't match the round-to-neg-infinity semantics of Cryptol,
  -- so we have to do some work to get the desired semantics.
  intDiv sym x y =
    do assertIntDivisor sym y
       liftIO $ do
         neg <- liftIO (W4.intLt (w4 sym) y =<< W4.intLit (w4 sym) 0)
         case W4.asConstantPred neg of
           Just False -> W4.intDiv (w4 sym) x y
           Just True  ->
              do xneg <- W4.intNeg (w4 sym) x
                 yneg <- W4.intNeg (w4 sym) y
                 W4.intDiv (w4 sym) xneg yneg
           Nothing ->
              do xneg <- W4.intNeg (w4 sym) x
                 yneg <- W4.intNeg (w4 sym) y
                 zneg <- W4.intDiv (w4 sym) xneg yneg
                 z    <- W4.intDiv (w4 sym) x y
                 W4.intIte (w4 sym) neg zneg z

  -- NB: What4's division operation provides SMTLib's euclidean division,
  -- which doesn't match the round-to-neg-infinity semantics of Cryptol,
  -- so we have to do some work to get the desired semantics.
  intMod sym x y =
    do assertIntDivisor sym y
       liftIO $ do
         neg <- liftIO (W4.intLt (w4 sym) y =<< W4.intLit (w4 sym) 0)
         case W4.asConstantPred neg of
           Just False -> W4.intMod (w4 sym) x y
           Just True  ->
              do xneg <- W4.intNeg (w4 sym) x
                 yneg <- W4.intNeg (w4 sym) y
                 W4.intNeg (w4 sym) =<< W4.intMod (w4 sym) xneg yneg
           Nothing ->
              do xneg <- W4.intNeg (w4 sym) x
                 yneg <- W4.intNeg (w4 sym) y
                 z    <- W4.intMod (w4 sym) x y
                 zneg <- W4.intNeg (w4 sym) =<< W4.intMod (w4 sym) xneg yneg
                 W4.intIte (w4 sym) neg zneg z

  intEq sym x y = liftIO $ W4.intEq (w4 sym) x y
  intLessThan sym x y = liftIO $ W4.intLt (w4 sym) x y
  intGreaterThan sym x y = liftIO $ W4.intLt (w4 sym) y x

  -- NB, we don't do reduction here on symbolic values
  intToZn sym m x
    | Just xi <- W4.asInteger x
    = liftIO $ W4.intLit (w4 sym) (xi `mod` m)

    | otherwise
    = pure x

  znToInt _ 0 _ = evalPanic "znToInt" ["0 modulus not allowed"]
  znToInt sym m x = liftIO (W4.intMod (w4 sym) x =<< W4.intLit (w4 sym) m)

  znEq _ 0 _ _ = evalPanic "znEq" ["0 modulus not allowed"]
  znEq sym m x y = liftIO $
     do diff <- W4.intSub (w4 sym) x y
        W4.intDivisible (w4 sym) diff (fromInteger m)

  znPlus   sym m x y = liftIO $ sModAdd (w4 sym) m x y
  znMinus  sym m x y = liftIO $ sModSub (w4 sym) m x y
  znMult   sym m x y = liftIO $ sModMult (w4 sym) m x y
  znNegate sym m x   = liftIO $ sModNegate (w4 sym) m x
  znRecip = sModRecip

  --------------------------------------------------------------

  fpLit sym e p r = liftIO $ FP.fpFromRationalLit (w4 sym) e p r
  fpAsLit _ f = BF e p <$> FP.fpAsLit f
    where (e,p) = FP.fpSize f

  fpExactLit sym BF{ bfExpWidth = e, bfPrecWidth = p, bfValue = bf } =
    liftIO (FP.fpFromBinary (w4 sym) e p =<< SW.bvLit (w4 sym) (e+p) (floatToBits e p bf))

  fpNaN sym e p = liftIO (FP.fpNaN (w4 sym) e p)
  fpPosInf sym e p = liftIO (FP.fpPosInf (w4 sym) e p)

  fpToBits sym f = liftIO (FP.fpToBinary (w4 sym) f)
  fpFromBits sym e p w = liftIO (FP.fpFromBinary (w4 sym) e p w)

  fpEq          sym x y = liftIO $ FP.fpEqIEEE (w4 sym) x y
  fpLessThan    sym x y = liftIO $ FP.fpLtIEEE (w4 sym) x y
  fpGreaterThan sym x y = liftIO $ FP.fpGtIEEE (w4 sym) x y
  fpLogicalEq   sym x y = liftIO $ FP.fpEq (w4 sym) x y

  fpPlus  = fpBinArith FP.fpAdd
  fpMinus = fpBinArith FP.fpSub
  fpMult  = fpBinArith FP.fpMul
  fpDiv   = fpBinArith FP.fpDiv

  fpNeg sym x = liftIO $ FP.fpNeg (w4 sym) x
  fpAbs sym x = liftIO $ FP.fpAbs (w4 sym) x
  fpSqrt sym r x =
    do rm <- fpRoundingMode sym r
       liftIO $ FP.fpSqrt (w4 sym) rm x

  fpFMA sym r x y z =
    do rm <- fpRoundingMode sym r
       liftIO $ FP.fpFMA (w4 sym) rm x y z

  fpIsZero sym x = liftIO $ FP.fpIsZero (w4 sym) x
  fpIsNeg sym x = liftIO $ FP.fpIsNeg (w4 sym) x
  fpIsNaN sym x = liftIO $ FP.fpIsNaN (w4 sym) x
  fpIsInf sym x = liftIO $ FP.fpIsInf (w4 sym) x
  fpIsNorm sym x = liftIO $ FP.fpIsNorm (w4 sym) x
  fpIsSubnorm sym x = liftIO $ FP.fpIsSubnorm (w4 sym) x

  fpFromInteger sym e p r x =
    do rm <- fpRoundingMode sym r
       liftIO $ FP.fpFromInteger (w4 sym) e p rm x

  fpToInteger = fpCvtToInteger

  fpFromRational = fpCvtFromRational
  fpToRational = fpCvtToRational

sModAdd :: W4.IsSymExprBuilder sym =>
  sym -> Integer -> W4.SymInteger sym -> W4.SymInteger sym -> IO (W4.SymInteger sym)
sModAdd _sym 0 _ _ = evalPanic "sModAdd" ["0 modulus not allowed"]
sModAdd sym m x y
  | Just xi <- W4.asInteger x
  , Just yi <- W4.asInteger y
  = W4.intLit sym ((xi+yi) `mod` m)

  | otherwise
  = W4.intAdd sym x y

sModSub :: W4.IsSymExprBuilder sym =>
  sym -> Integer -> W4.SymInteger sym -> W4.SymInteger sym -> IO (W4.SymInteger sym)
sModSub _sym 0 _ _ = evalPanic "sModSub" ["0 modulus not allowed"]
sModSub sym m x y
  | Just xi <- W4.asInteger x
  , Just yi <- W4.asInteger y
  = W4.intLit sym ((xi-yi) `mod` m)

  | otherwise
  = W4.intSub sym x y


sModMult :: W4.IsSymExprBuilder sym =>
  sym -> Integer -> W4.SymInteger sym -> W4.SymInteger sym -> IO (W4.SymInteger sym)
sModMult _sym 0 _ _ = evalPanic "sModMult" ["0 modulus not allowed"]
sModMult sym m x y
  | Just xi <- W4.asInteger x
  , Just yi <- W4.asInteger y
  = W4.intLit sym ((xi*yi) `mod` m)

  | otherwise
  = W4.intMul sym x y

sModNegate :: W4.IsSymExprBuilder sym =>
  sym -> Integer -> W4.SymInteger sym -> IO (W4.SymInteger sym)
sModNegate _sym 0 _ = evalPanic "sModMult" ["0 modulus not allowed"]
sModNegate sym m x
  | Just xi <- W4.asInteger x
  = W4.intLit sym ((negate xi) `mod` m)

  | otherwise
  = W4.intNeg sym x


-- | Try successive powers of 2 to find the first that dominates the input.
--   We could perhaps reduce to using CLZ instead...
sLg2 :: W4.IsSymExprBuilder sym => sym -> SW.SWord sym -> SEval (What4 sym) (SW.SWord sym)
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
evalPanic cxt = panic ("[What4] " ++ cxt)

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

w4bvShl  :: W4.IsSymExprBuilder sym => sym -> SW.SWord sym -> SW.SWord sym -> W4Eval sym (SW.SWord sym)
w4bvShl sym x y = liftIO $ SW.bvShl sym x y

w4bvLshr  :: W4.IsSymExprBuilder sym => sym -> SW.SWord sym -> SW.SWord sym -> W4Eval sym (SW.SWord sym)
w4bvLshr sym x y = liftIO $ SW.bvLshr sym x y

w4bvAshr :: W4.IsSymExprBuilder sym => sym -> SW.SWord sym -> SW.SWord sym -> W4Eval sym (SW.SWord sym)
w4bvAshr sym x y = liftIO $ SW.bvAshr sym x y

w4bvRol  :: W4.IsSymExprBuilder sym => sym -> SW.SWord sym -> SW.SWord sym -> W4Eval sym (SW.SWord sym)
w4bvRol sym x y = liftIO $ SW.bvRol sym x y

w4bvRor  :: W4.IsSymExprBuilder sym => sym -> SW.SWord sym -> SW.SWord sym -> W4Eval sym (SW.SWord sym)
w4bvRor sym x y = liftIO $ SW.bvRor sym x y



fpRoundingMode ::
  W4.IsSymExprBuilder sym =>
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
  W4.IsSymExprBuilder sym =>
  FP.SFloatBinArith sym ->
  What4 sym ->
  SWord (What4 sym) ->
  SFloat (What4 sym) ->
  SFloat (What4 sym) ->
  SEval (What4 sym) (SFloat (What4 sym))
fpBinArith fun = \sym r x y ->
  do m <- fpRoundingMode sym r
     liftIO (fun (w4 sym) m x y)


fpCvtToInteger ::
  (W4.IsSymExprBuilder sy, sym ~ What4 sy) =>
  sym -> String -> SWord sym -> SFloat sym -> SEval sym (SInteger sym)
fpCvtToInteger sym fun r x =
  do grd <- liftIO
              do bad1 <- FP.fpIsInf (w4 sym) x
                 bad2 <- FP.fpIsNaN (w4 sym) x
                 W4.notPred (w4 sym) =<< W4.orPred (w4 sym) bad1 bad2
     assertSideCondition sym grd (BadValue fun)
     rnd  <- fpRoundingMode sym r
     liftIO
       do y <- FP.fpToReal (w4 sym) x
          case rnd of
            W4.RNE -> W4.realRoundEven (w4 sym) y
            W4.RNA -> W4.realRound (w4 sym) y
            W4.RTP -> W4.realCeil (w4 sym) y
            W4.RTN -> W4.realFloor (w4 sym) y
            W4.RTZ -> W4.realTrunc (w4 sym) y


fpCvtToRational ::
  (W4.IsSymExprBuilder sy, sym ~ What4 sy) =>
  sym -> SFloat sym -> SEval sym (SRational sym)
fpCvtToRational sym fp =
  do grd <- liftIO
            do bad1 <- FP.fpIsInf (w4 sym) fp
               bad2 <- FP.fpIsNaN (w4 sym) fp
               W4.notPred (w4 sym) =<< W4.orPred (w4 sym) bad1 bad2
     assertSideCondition sym grd (BadValue "fpToRational")
     (rel,x,y) <- liftIO (FP.fpToRational (w4 sym) fp)
     addDefEqn sym =<< liftIO (W4.impliesPred (w4 sym) grd rel)
     ratio sym x y

fpCvtFromRational ::
  (W4.IsSymExprBuilder sy, sym ~ What4 sy) =>
  sym -> Integer -> Integer -> SWord sym ->
  SRational sym -> SEval sym (SFloat sym)
fpCvtFromRational sym e p r rat =
  do rnd <- fpRoundingMode sym r
     liftIO (FP.fpFromRational (w4 sym) e p rnd (sNum rat) (sDenom rat))

-- Create a fresh constant and assert that it is the
-- multiplicitive inverse of x; return the constant.
-- Such an inverse must exist under the precondition
-- that the modulus is prime and the input is nonzero.
sModRecip ::
  W4.IsSymExprBuilder sym =>
  What4 sym ->
  Integer ->
  W4.SymInteger sym ->
  W4Eval sym (W4.SymInteger sym)
sModRecip _sym 0 _ = panic "sModRecip" ["0 modulus not allowed"]
sModRecip sym m x
  -- If the input is concrete, evaluate the answer
  | Just xi <- W4.asInteger x
  = case Integer.integerRecipMod xi m of
      Just r  -> integerLit sym r
      Nothing -> raiseError sym DivideByZero

  -- If the input is symbolic, create a new symbolic constant
  -- and assert that it is the desired multiplicitive inverse.
  -- Such an inverse will exist under the precondition that
  -- the modulus is prime, and as long as the input is nonzero.
  | otherwise
  = do divZero <- liftIO (W4.intDivisible (w4 sym) x (fromInteger m))
       ok <- liftIO (W4.notPred (w4 sym) divZero)
       assertSideCondition sym ok DivideByZero

       z <- liftIO (W4.freshBoundedInt (w4 sym) W4.emptySymbol (Just 1) (Just (m-1)))
       xz <- liftIO (W4.intMul (w4 sym) x z)
       rel <- znEq sym m xz =<< liftIO (W4.intLit (w4 sym) 1)
       addDefEqn sym =<< liftIO (W4.orPred (w4 sym) divZero rel)

       return z
