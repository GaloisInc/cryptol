-- |
-- Module      :  Cryptol.Eval.What4
-- Copyright   :  (c) 2020 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
module Cryptol.Eval.What4
  ( What4(..)
  , W4Result(..)
  , W4Eval(..)
  , Value
  , evalPrim
  ) where


import qualified Control.Exception as X
import           Control.Monad (foldM, join)
import           Control.Monad.IO.Class
import           Data.Bits (bit, shiftR, shiftL, testBit)
import           Data.List
import qualified Data.Map as Map
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
import qualified Data.Text as T

import qualified What4.Interface as W4
import qualified What4.SWord as SW

import Cryptol.Eval.Backend
import Cryptol.Eval.Concrete.Value( BV(..), ppBV, lg2 )
import Cryptol.Eval.Generic
import Cryptol.Eval.Monad (Eval(..), EvalError(..), io, delayFill, blackhole)
import Cryptol.Eval.Type (TValue(..), finNat')
import Cryptol.Eval.Value
import Cryptol.Testing.Random( randomV )
import Cryptol.TypeCheck.Solver.InfNat (Nat'(..), widthInteger)
import Cryptol.Utils.Ident
import Cryptol.Utils.Panic
import Cryptol.Utils.PP


data What4 sym = What4 sym

type Value sym = GenValue (What4 sym)

data W4Result sym a
  = W4Error !EvalError
  | W4Result !(W4.Pred sym) !a -- safety predicate and result

instance Functor (W4Result sym) where
  fmap _ (W4Error err) = W4Error err
  fmap f (W4Result p x) = W4Result p (f x)

total :: W4.IsExprBuilder sym => sym -> a -> W4Result sym a
total sym = W4Result (W4.backendPred sym True)

-- TODO? Reorganize this to use PartialT ?
newtype W4Eval sym a = W4Eval{ w4Eval :: sym -> Eval (W4Result sym a) }
  deriving (Functor)

instance W4.IsExprBuilder sym => Applicative (W4Eval sym) where
  pure x = W4Eval $ \sym -> pure (total sym x)
  mf <*> mx = mf >>= \f -> mx >>= \x -> pure (f x)

instance W4.IsExprBuilder sym => Monad (W4Eval sym) where
  return = pure
  x >>= f = W4Eval $ \sym ->
    w4Eval x sym >>= \case
      W4Error err -> pure (W4Error err)
      W4Result px x' ->
        w4Eval (f x') sym >>= \case
          W4Error err -> pure (W4Error err)
          W4Result pz z ->
            do p <- io (W4.andPred sym px pz)
               pure (W4Result p z)

instance W4.IsExprBuilder sym => MonadIO (W4Eval sym) where
  liftIO m = W4Eval $ \sym -> fmap (total sym) (liftIO m)

assertBVDivisor :: W4.IsExprBuilder sym => sym -> SW.SWord sym -> W4Eval sym ()
assertBVDivisor sym x =
  do p <- liftIO (SW.bvIsNonzero sym x)
     assertSideCondition (What4 sym) p DivideByZero

assertIntDivisor :: W4.IsExprBuilder sym => sym -> W4.SymInteger sym -> W4Eval sym ()
assertIntDivisor sym x =
  do p <- liftIO (W4.notPred sym =<< W4.intEq sym x =<< W4.intLit sym 0)
     assertSideCondition (What4 sym) p DivideByZero

instance W4.IsExprBuilder sym => Backend (What4 sym) where
  type SBit (What4 sym)     = W4.Pred sym
  type SWord (What4 sym)    = SW.SWord sym
  type SInteger (What4 sym) = W4.SymInteger sym
  type SEval (What4 sym)    = W4Eval sym

  raiseError _ err = W4Eval (\_ -> pure (W4Error err))

  assertSideCondition _ cond err
    | Just False <- W4.asConstantPred cond = W4Eval (\_ -> pure (W4Error err))
    | otherwise = W4Eval (\_ -> pure (W4Result cond ()))

  isReady (What4 sym) m =
    case w4Eval m sym of
      Ready _ -> True
      _ -> False

  sDelayFill _ m retry = W4Eval $ \sym ->
    do m' <- delayFill (w4Eval m sym) (w4Eval retry sym)
       pure (total sym (W4Eval (const m')))

  sDeclareHole _ msg = W4Eval $ \sym ->
    do (hole, fill) <- blackhole msg
       pure (total sym ( W4Eval (const hole), \m -> W4Eval (\sym' -> fmap (total sym') (fill (w4Eval m sym'))) ))

  mergeEval _sym f c mx my = W4Eval $ \sym ->
    do rx <- w4Eval mx sym
       ry <- w4Eval my sym
       case (rx, ry) of
         (W4Error err, W4Error _) ->
           pure $ W4Error err -- arbitrarily choose left error to report
         (W4Error _, W4Result p y) ->
           do p' <- io (W4.andPred sym p =<< W4.notPred sym c)
              pure $ W4Result p' y
         (W4Result p x, W4Error _) ->
           do p' <- io (W4.andPred sym p c)
              pure $ W4Result p' x
         (W4Result px x, W4Result py y) ->
           do zr <- w4Eval (f c x y) sym
              case zr of
                W4Error err -> pure $ W4Error err
                W4Result pz z ->
                  do p'  <- io (W4.andPred sym pz =<< W4.itePred sym c px py)
                     pure $ W4Result p' z

  wordAsChar _ bv
    | SW.bvWidth bv == 8 = toEnum . fromInteger <$> SW.bvAsUnsignedInteger bv
    | otherwise = Nothing

  wordLen _ bv = SW.bvWidth bv

  bitLit (What4 sym) b = W4.backendPred sym b
  bitAsLit _ v = W4.asConstantPred v

  wordLit (What4 sym) intw i
    | Just (Some w) <- someNat intw
    = case isPosNat w of
        Nothing -> pure $ SW.ZBV
        Just LeqProof -> SW.DBV <$> liftIO (W4.bvLit sym w i)
    | otherwise = panic "what4: wordLit" ["invalid bit width:", show intw ]

  wordAsLit _ v
    | Just x <- SW.bvAsUnsignedInteger v = Just (SW.bvWidth v, x)
    | otherwise = Nothing

  integerLit (What4 sym) i = liftIO (W4.intLit sym i)

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


  iteBit (What4 sym) c x y = liftIO (W4.itePred sym c x y)
  iteWord (What4 sym) c x y = liftIO (SW.bvIte sym c x y)
  iteInteger (What4 sym) c x y = liftIO (W4.intIte sym c x y)

  bitEq  (What4 sym) x y = liftIO (W4.eqPred sym x y)
  bitAnd (What4 sym) x y = liftIO (W4.andPred sym x y)
  bitOr  (What4 sym) x y = liftIO (W4.orPred sym x y)
  bitXor (What4 sym) x y = liftIO (W4.xorPred sym x y)
  bitComplement (What4 sym) x = liftIO (W4.notPred sym x)

  wordBit (What4 sym) bv idx = liftIO (SW.bvAt sym bv idx)
  wordUpdate (What4 sym) bv idx b = liftIO (SW.bvSet sym bv idx b)

  packWord sym bs =
    do z <- wordLit sym (genericLength bs) 0
       let f w (idx,b) = wordUpdate sym w idx b
       foldM f z (zip [0..] bs)

  unpackWord (What4 sym) bv = liftIO $
    mapM (SW.bvAt sym bv) [0 .. SW.bvWidth bv-1]

  joinWord (What4 sym) x y = liftIO $ SW.bvJoin sym x y

  splitWord _sym 0 _ bv = pure (SW.ZBV, bv)
  splitWord _sym _ 0 bv = pure (bv, SW.ZBV)
  splitWord (What4 sym) lw rw bv = liftIO $
    do l <- SW.bvSlice sym 0 lw bv
       r <- SW.bvSlice sym lw rw bv
       return (l, r)

  extractWord (What4 sym) bits idx bv =
    liftIO $ SW.bvSlice sym idx bits bv

  wordEq                (What4 sym) x y = liftIO (SW.bvEq sym x y)
  wordLessThan          (What4 sym) x y = liftIO (SW.bvult sym x y)
  wordGreaterThan       (What4 sym) x y = liftIO (SW.bvugt sym x y)
  wordSignedLessThan    (What4 sym) x y = liftIO (SW.bvslt sym x y)

  wordOr  (What4 sym) x y = liftIO (SW.bvOr sym x y)
  wordAnd (What4 sym) x y = liftIO (SW.bvAnd sym x y)
  wordXor (What4 sym) x y = liftIO (SW.bvXor sym x y)
  wordComplement (What4 sym) x = liftIO (SW.bvNot sym x)

  wordPlus  (What4 sym) x y = liftIO (SW.bvAdd sym x y)
  wordMinus (What4 sym) x y = liftIO (SW.bvSub sym x y)
  wordMult  (What4 sym) x y = liftIO (SW.bvMul sym x y)
  wordNegate (What4 sym) x  = liftIO (SW.bvNeg sym x)
  wordExp (What4 sym) x y   = sExp sym x y
  wordLg2 (What4 sym) x     = sLg2 sym x

  wordDiv (What4 sym) x y =
     do assertBVDivisor sym y
        liftIO (SW.bvUDiv sym x y)
  wordMod (What4 sym) x y =
     do assertBVDivisor sym y
        liftIO (SW.bvURem sym x y)
  wordSignedDiv (What4 sym) x y =
     do assertBVDivisor sym y
        liftIO (SW.bvSDiv sym x y)
  wordSignedMod (What4 sym) x y =
     do assertBVDivisor sym y
        liftIO (SW.bvSRem sym x y)

  wordToInt (What4 sym) x = liftIO (SW.bvToInteger sym x)
  wordFromInt (What4 sym) width i = liftIO (SW.integerToBV sym i width)

  intPlus (What4 sym) x y  = liftIO $ W4.intAdd sym x y
  intMinus (What4 sym) x y = liftIO $ W4.intSub sym x y
  intMult (What4 sym) x y  = liftIO $ W4.intMul sym x y
  intNegate (What4 sym) x  = liftIO $ W4.intNeg sym x

  -- NB: What4's division operation provides SMTLib's euclidean division,
  -- which doesn't match the round-to-neg-infinity semantics of Cryptol,
  -- so we have to do some work to get the desired semantics.
  intDiv (What4 sym) x y =
    do assertIntDivisor sym y
       liftIO $ do
         neg <- liftIO (W4.intLt sym y =<< W4.intLit sym 0)
         case W4.asConstantPred neg of
           Just False -> W4.intDiv sym x y
           Just True  ->
              do xneg <- W4.intNeg sym x
                 yneg <- W4.intNeg sym y
                 W4.intDiv sym xneg yneg
           Nothing ->
              do xneg <- W4.intNeg sym x
                 yneg <- W4.intNeg sym y
                 zneg <- W4.intDiv sym xneg yneg
                 z    <- W4.intDiv sym x y
                 W4.intIte sym neg zneg z

  -- NB: What4's division operation provides SMTLib's euclidean division,
  -- which doesn't match the round-to-neg-infinity semantics of Cryptol,
  -- so we have to do some work to get the desired semantics.
  intMod (What4 sym) x y =
    do assertIntDivisor sym y
       liftIO $ do
         neg <- liftIO (W4.intLt sym y =<< W4.intLit sym 0)
         case W4.asConstantPred neg of
           Just False -> W4.intMod sym x y
           Just True  ->
              do xneg <- W4.intNeg sym x
                 yneg <- W4.intNeg sym y
                 W4.intNeg sym =<< W4.intMod sym xneg yneg
           Nothing ->
              do xneg <- W4.intNeg sym x
                 yneg <- W4.intNeg sym y
                 z    <- W4.intMod sym x y
                 zneg <- W4.intNeg sym =<< W4.intMod sym xneg yneg
                 W4.intIte sym neg zneg z

  intEq (What4 sym) x y = liftIO $ W4.intEq sym x y
  intLessThan (What4 sym) x y = liftIO $ W4.intLt sym x y
  intGreaterThan (What4 sym) x y = liftIO $ W4.intLt sym y x

  intExp (What4 sym) x y
    | Just i <- W4.asInteger y = intExpConcrete sym x i
    | otherwise = liftIO (X.throw (UnsupportedSymbolicOp "integer exponentation"))

  intLg2 (What4 sym) x
    | Just i <- W4.asInteger x = liftIO $ W4.intLit sym (lg2 i)
    | otherwise = liftIO (X.throw (UnsupportedSymbolicOp "integer lg2"))

  -- NB, we don't do reduction here on symbolic values
  intToZn (What4 sym) m x
    | Just xi <- W4.asInteger x
    = liftIO $ W4.intLit sym (xi `mod` m)

    | otherwise
    = pure x

  znToInt _ 0 _ = evalPanic "znToInt" ["0 modulus not allowed"]
  znToInt (What4 sym) m x = liftIO (W4.intMod sym x =<< W4.intLit sym m)

  znEq _ 0 _ _ = evalPanic "znEq" ["0 modulus not allowed"]
  znEq (What4 sym) m x y = liftIO $
     do diff <- W4.intSub sym x y
        W4.intDivisible sym diff (fromInteger m)

  znPlus   (What4 sym) m x y = liftIO $ sModAdd sym m x y
  znMinus  (What4 sym) m x y = liftIO $ sModSub sym m x y
  znMult   (What4 sym) m x y = liftIO $ sModMult sym m x y
  znNegate (What4 sym) m x   = liftIO $ sModNegate sym m x


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


-- | Square-and-multiply according to the concrete integer
intExpConcrete :: W4.IsExprBuilder sym =>
  sym -> W4.SymInteger sym -> Integer -> SEval (What4 sym) (W4.SymInteger sym)
intExpConcrete sym x = liftIO . go
  where
  go 0 = W4.intLit sym 1
  go i =
    do a  <- go (i `shiftR` 1)
       a2 <- W4.intMul sym a a
       if testBit i 0 then
         W4.intMul sym x a2
       else
         return a2

-- | Bit-blast the exponent and square-and-multiply
sExp :: W4.IsExprBuilder sym => sym -> SW.SWord sym -> SW.SWord sym -> SEval (What4 sym) (SW.SWord sym)
sExp sym x y = liftIO . go =<< (reverse <$> unpackWord (What4 sym) y) -- bits in little-endian order
  where

  go []
    -- Base case, return 1
    = SW.bvLit sym (SW.bvWidth x) 1

  go (b:bs)
    = do a <- go bs
         a2 <- SW.bvMul sym a a
         lazyIte (SW.bvIte sym) b (SW.bvMul sym x a2) (pure a2)

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

-- Primitives ------------------------------------------------------------------

evalPrim :: W4.IsExprBuilder sym => sym -> Ident -> Maybe (Value sym)
evalPrim sym prim = Map.lookup prim (primTable sym)

-- See also Cryptol.Prims.Eval.primTable
primTable :: W4.IsExprBuilder sym => sym -> Map.Map Ident (Value sym)
primTable w4sym = let sym = What4 w4sym in
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
  , ("/$"          , binary (sdivV sym))
  , ("%$"          , binary (smodV sym))
  , ("^^"          , binary (expV sym))
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
  , ("<<"          , logicShift sym "<<"  (w4bvShl w4sym) shiftLeftReindex)
  , (">>"          , logicShift sym ">>"  (w4bvLshr w4sym) shiftRightReindex)
  , ("<<<"         , logicShift sym "<<<" (w4bvRol w4sym) rotateLeftReindex)
  , (">>>"         , logicShift sym ">>>" (w4bvRor w4sym) rotateRightReindex)
  , (">>$"         , sshrV w4sym)

    -- Indexing and updates
  , ("@"           , indexPrim sym (indexFront_bits w4sym) (indexFront w4sym))
  , ("!"           , indexPrim sym (indexBack_bits w4sym) (indexBack w4sym))

  , ("update"      , updatePrim sym (updateFrontSym_word w4sym) (updateFrontSym w4sym))
  , ("updateEnd"   , updatePrim sym (updateBackSym_word w4sym)  (updateBackSym w4sym))

    -- Misc

    -- {at,len} (fin len) => [len][8] -> at
  , ("error"       ,
      tlam $ \a ->
      nlam $ \_ ->
      VFun $ \s -> errorV sym a =<< (valueToString sym =<< s))

  , ("random"      ,
      tlam $ \a ->
      wlam sym $ \x ->
         case wordAsLit sym x of
           Just (_,i)  -> randomV sym a i
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

indexFront ::
  W4.IsExprBuilder sym =>
  sym ->
  Nat' ->
  TValue ->
  SeqMap (What4 sym) ->
  SWord (What4 sym) ->
  SEval (What4 sym) (Value sym)
indexFront sym mblen _a xs idx
  | Just i <- SW.bvAsUnsignedInteger idx
  = lookupSeqMap xs i

  | otherwise
  = foldr f def idxs

 where
    w = SW.bvWidth idx
    def = raiseError (What4 sym) (InvalidIndex Nothing)

    f n y =
       do p <- liftIO (SW.bvEq sym idx =<< SW.bvLit sym w n)
          iteValue (What4 sym) p (lookupSeqMap xs n) y

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

indexBack ::
  W4.IsExprBuilder sym =>
  sym ->
  Nat' ->
  TValue ->
  SeqMap (What4 sym) ->
  SWord (What4 sym) ->
  SEval (What4 sym) (Value sym)
indexBack sym (Nat n) a xs idx = indexFront sym (Nat n) a (reverseSeqMap n xs) idx
indexBack _ Inf _ _ _ = evalPanic "Expected finite sequence" ["indexBack"]

indexFront_bits :: forall sym.
  W4.IsExprBuilder sym =>
  sym ->
  Nat' ->
  TValue ->
  SeqMap (What4 sym) ->
  [SBit (What4 sym)] ->
  SEval (What4 sym) (Value sym)
indexFront_bits sym mblen _a xs bits0 = go 0 (length bits0) bits0
 where
  go :: Integer -> Int -> [W4.Pred sym] -> W4Eval sym (Value sym)
  go i _k []
    -- For indices out of range, fail
    | Nat n <- mblen
    , i >= n
    = raiseError (What4 sym) (InvalidIndex (Just i))

    | otherwise
    = lookupSeqMap xs i

  go i k (b:bs)
    -- Fail early when all possible indices we could compute from here
    -- are out of bounds
    | Nat n <- mblen
    , (i `shiftL` k) >= n
    = raiseError (What4 sym) (InvalidIndex Nothing)

    | otherwise
    = iteValue (What4 sym) b
         (go ((i `shiftL` 1) + 1) (k-1) bs)
         (go  (i `shiftL` 1)      (k-1) bs)

indexBack_bits ::
  W4.IsExprBuilder sym =>
  sym ->
  Nat' ->
  TValue ->
  SeqMap (What4 sym) ->
  [SBit (What4 sym)] ->
  SEval (What4 sym) (Value sym)
indexBack_bits sym (Nat n) a xs idx = indexFront_bits sym (Nat n) a (reverseSeqMap n xs) idx
indexBack_bits _ Inf _ _ _ = evalPanic "Expected finite sequence" ["indexBack_bits"]


-- | Compare a symbolic word value with a concrete integer.
wordValueEqualsInteger :: forall sym.
  W4.IsExprBuilder sym =>
  sym ->
  WordValue (What4 sym) ->
  Integer ->
  W4Eval sym (W4.Pred sym)
wordValueEqualsInteger sym wv i
  | wordValueSize (What4 sym) wv < widthInteger i = return (W4.falsePred sym)
  | otherwise =
    case wv of
      WordVal w -> liftIO (SW.bvEq sym w =<< SW.bvLit sym (SW.bvWidth w) i)
      _ -> liftIO . bitsAre i =<< enumerateWordValueRev (What4 sym) wv -- little-endian
  where
    bitsAre :: Integer -> [W4.Pred sym] -> IO (W4.Pred sym)
    bitsAre n [] = pure (W4.backendPred sym (n == 0))
    bitsAre n (b : bs) =
      do pb  <- bitIs (testBit n 0) b
         pbs <- bitsAre (n `shiftR` 1) bs
         W4.andPred sym pb pbs

    bitIs :: Bool -> W4.Pred sym -> IO (W4.Pred sym)
    bitIs b x = if b then pure x else W4.notPred sym x

updateFrontSym ::
  W4.IsExprBuilder sym =>
  sym ->
  Nat' ->
  TValue ->
  SeqMap (What4 sym) ->
  WordValue (What4 sym) ->
  SEval (What4 sym) (Value sym) ->
  SEval (What4 sym) (SeqMap (What4 sym))
updateFrontSym sym _len _eltTy vs wv val =
  case wv of
    WordVal w | Just j <- SW.bvAsUnsignedInteger w ->
      return $ updateSeqMap vs j val
    _ ->
      memoMap $ IndexSeqMap $ \i ->
      do b <- wordValueEqualsInteger sym wv i
         iteValue (What4 sym) b val (lookupSeqMap vs i)

updateBackSym ::
  W4.IsExprBuilder sym =>
  sym ->
  Nat' ->
  TValue ->
  SeqMap (What4 sym) ->
  WordValue (What4 sym) ->
  SEval (What4 sym) (Value sym) ->
  SEval (What4 sym) (SeqMap (What4 sym))
updateBackSym _ Inf _ _ _ _ = evalPanic "Expected finite sequence" ["updateBackSym"]
updateBackSym sym (Nat n) _eltTy vs wv val =
  case wv of
    WordVal w | Just j <- SW.bvAsUnsignedInteger w ->
      return $ updateSeqMap vs (n - 1 - j) val
    _ ->
      memoMap $ IndexSeqMap $ \i ->
      do b <- wordValueEqualsInteger sym wv (n - 1 - i)
         iteValue (What4 sym) b val (lookupSeqMap vs i)


updateFrontSym_word ::
  W4.IsExprBuilder sym =>
  sym ->
  Nat' ->
  TValue ->
  WordValue (What4 sym) ->
  WordValue (What4 sym) ->
  SEval (What4 sym) (GenValue (What4 sym)) ->
  SEval (What4 sym) (WordValue (What4 sym))
updateFrontSym_word _ Inf _ _ _ _ = evalPanic "Expected finite sequence" ["updateFrontSym_word"]
updateFrontSym_word sym (Nat n) eltTy bv wv val =
  case wv of
    WordVal idx
      | Just j <- SW.bvAsUnsignedInteger idx ->
          updateWordValue (What4 sym) bv j (fromVBit <$> val)

      | WordVal bw <- bv ->
        WordVal <$>
          do b <- fromVBit <$> val
             let sz = SW.bvWidth bw
             highbit <- liftIO (SW.bvLit sym sz (bit (fromInteger (sz-1))))
             msk <- w4bvLshr sym highbit idx
             liftIO $
               case W4.asConstantPred b of
                 Just True  -> SW.bvOr  sym bw msk
                 Just False -> SW.bvAnd sym bw =<< SW.bvNot sym msk
                 Nothing ->
                   do q <- SW.bvFill sym sz b
                      bw' <- SW.bvAnd sym bw =<< SW.bvNot sym msk
                      SW.bvXor sym bw' =<< SW.bvAnd sym q msk

    _ -> LargeBitsVal (wordValueSize (What4 sym) wv) <$>
           updateFrontSym sym (Nat n) eltTy (asBitsMap (What4 sym) bv) wv val


updateBackSym_word ::
  W4.IsExprBuilder sym =>
  sym ->
  Nat' ->
  TValue ->
  WordValue (What4 sym) ->
  WordValue (What4 sym) ->
  SEval (What4 sym) (GenValue (What4 sym)) ->
  SEval (What4 sym) (WordValue (What4 sym))
updateBackSym_word _ Inf _ _ _ _ = evalPanic "Expected finite sequence" ["updateBackSym_word"]
updateBackSym_word sym (Nat n) eltTy bv wv val =
  case wv of
    WordVal idx
      | Just j <- SW.bvAsUnsignedInteger idx ->
          updateWordValue (What4 sym) bv (n - 1 - j) (fromVBit <$> val)

      | WordVal bw <- bv ->
        WordVal <$>
          do b <- fromVBit <$> val
             let sz = SW.bvWidth bw
             lowbit <- liftIO (SW.bvLit sym sz 1)
             msk <- w4bvShl sym lowbit idx
             liftIO $
               case W4.asConstantPred b of
                 Just True  -> SW.bvOr  sym bw msk
                 Just False -> SW.bvAnd sym bw =<< SW.bvNot sym msk
                 Nothing ->
                   do q <- SW.bvFill sym sz b
                      bw' <- SW.bvAnd sym bw =<< SW.bvNot sym msk
                      SW.bvXor sym bw' =<< SW.bvAnd sym q msk

    _ -> LargeBitsVal (wordValueSize (What4 sym) wv) <$>
           updateBackSym sym (Nat n) eltTy (asBitsMap (What4 sym) bv) wv val


sshrV :: W4.IsExprBuilder sym => sym -> Value sym
sshrV sym =
  nlam $ \_n ->
  nlam $ \_k ->
  wlam (What4 sym) $ \x -> return $
  wlam (What4 sym) $ \y ->
    return (VWord (SW.bvWidth x) (WordVal <$> w4bvAshr sym x y))


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
