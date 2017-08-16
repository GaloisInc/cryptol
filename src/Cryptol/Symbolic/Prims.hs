-- |
-- Module      :  $Header$
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
import Data.List (genericTake)
import qualified Data.Sequence as Seq

import Cryptol.Eval.Monad (Eval(..), ready, invalidIndex, cryUserError)
import Cryptol.Eval.Type  (finNat', TValue(..))
import Cryptol.Eval.Value (BitWord(..), EvalPrims(..), enumerateSeqMap, SeqMap(..),
                          reverseSeqMap, wlam, nlam, WordValue(..),
                          asWordVal, fromWordVal, enumerateWordValue,
                          enumerateWordValueRev, updateWordValue,
                          updateSeqMap, lookupSeqMap, memoMap )
import Cryptol.Prims.Eval (binary, unary, arithUnary,
                           arithBinary, Binary, BinArith,
                           logicBinary, logicUnary, zeroV,
                           ccatV, splitAtV, joinV, ecSplitV,
                           reverseV, infFromV, infFromThenV,
                           fromThenV, fromToV, fromThenToV,
                           transposeV, indexPrimOne, indexPrimMany,
                           ecDemoteV, updatePrim, randomV, liftWord,
                           cmpValue)
import Cryptol.Symbolic.Value
import Cryptol.TypeCheck.AST (Decl(..))
import Cryptol.TypeCheck.Solver.InfNat(Nat'(..))
import Cryptol.Utils.Panic
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

instance EvalPrims SBool SWord where
  evalPrim Decl { dName = n, .. }
    | Just prim <- asPrim n, Just val <- Map.lookup prim primTable = val

  evalPrim Decl { .. } =
      panic "Eval" [ "Unimplemented primitive", show dName ]

  iteValue b x y
    | Just b' <- SBV.svAsBool b = if b' then x else y
    | otherwise = iteSValue b <$> x <*> y

-- See also Cryptol.Prims.Eval.primTable
primTable :: Map.Map Ident Value
primTable  = Map.fromList $ map (\(n, v) -> (mkIdent (T.pack n), v))
  [ ("True"        , VBit SBV.svTrue)
  , ("False"       , VBit SBV.svFalse)
  , ("demote"      , ecDemoteV) -- Converts a numeric type into its corresponding value.
                                -- { val, bits } (fin val, fin bits, bits >= width val) => [bits]
  , ("+"           , binary (arithBinary (liftBinArith SBV.svPlus))) -- {a} (Arith a) => a -> a -> a
  , ("-"           , binary (arithBinary (liftBinArith SBV.svMinus))) -- {a} (Arith a) => a -> a -> a
  , ("*"           , binary (arithBinary (liftBinArith SBV.svTimes))) -- {a} (Arith a) => a -> a -> a
  , ("/"           , binary (arithBinary (liftBinArith SBV.svQuot))) -- {a} (Arith a) => a -> a -> a
  , ("%"           , binary (arithBinary (liftBinArith SBV.svRem))) -- {a} (Arith a) => a -> a -> a
  , ("^^"          , binary (arithBinary sExp)) -- {a} (Arith a) => a -> a -> a
  , ("lg2"         , unary (arithUnary sLg2)) -- {a} (Arith a) => a -> a
  , ("negate"      , unary (arithUnary (\_ -> ready . SBV.svUNeg)))
  , ("<"           , binary (cmpBinary cmpLt cmpLt SBV.svFalse))
  , (">"           , binary (cmpBinary cmpGt cmpGt SBV.svFalse))
  , ("<="          , binary (cmpBinary cmpLtEq cmpLtEq SBV.svTrue))
  , (">="          , binary (cmpBinary cmpGtEq cmpGtEq SBV.svTrue))
  , ("=="          , binary (cmpBinary cmpEq cmpEq SBV.svTrue))
  , ("!="          , binary (cmpBinary cmpNotEq cmpNotEq SBV.svFalse))
  , ("<$"          , let boolFail = evalPanic "<$" ["Attempted signed comparison on bare Bit values"]
                      in binary (cmpBinary boolFail cmpSignedLt SBV.svFalse))
  , ("/$"          , liftWord swordSdiv)
  , ("%$"          , liftWord swordSrem)
  , (">>$"         , sshrV)
  , ("&&"          , binary (logicBinary SBV.svAnd SBV.svAnd))
  , ("||"          , binary (logicBinary SBV.svOr SBV.svOr))
  , ("^"           , binary (logicBinary SBV.svXOr SBV.svXOr))
  , ("complement"  , unary (logicUnary SBV.svNot SBV.svNot))
  , ("zero"        , tlam zeroV)
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

  , ("fromThen"    , fromThenV)
  , ("fromTo"      , fromToV)
  , ("fromThenTo"  , fromThenToV)
  , ("infFrom"     , infFromV)
  , ("infFromThen" , infFromThenV)

  , ("@"           , indexPrimOne  indexFront_bits indexFront)
  , ("@@"          , indexPrimMany indexFront_bits indexFront)
  , ("!"           , indexPrimOne  indexBack_bits indexBack)
  , ("!!"          , indexPrimMany indexBack_bits indexBack)

  , ("update"      , updatePrim updateFrontSym_word updateFrontSym)
  , ("updateEnd"   , updatePrim updateBackSym_word updateBackSym)


  , ("pmult"       , -- {a,b} (fin a, fin b) => [1 + a] -> [1 + b] -> [1 + a + b]
      nlam $ \(finNat' -> i) ->
      nlam $ \(finNat' -> j) ->
      VFun $ \v1 -> return $
      VFun $ \v2 -> do
        let k = 1 + i + j
            mul _  []     ps = ps
            mul as (b:bs) ps = mul (SBV.svFalse : as) bs (ites b (as `addPoly` ps) ps)
        xs <- enumerateWordValue =<< fromWordVal "pmult 1" =<< v1
        ys <- enumerateWordValue =<< fromWordVal "pmult 2" =<< v2
        let zs = Seq.fromList $ genericTake k (mul xs ys [] ++ repeat SBV.svFalse)
        return $ VWord k $ return $ BitsVal k $ IndexSeqMap (return . VBit . Seq.index zs . fromInteger))

  , ("pdiv"        , -- {a,b} (fin a, fin b) => [a] -> [b] -> [a]
      nlam $ \(finNat' -> i) ->
      nlam $ \(finNat' -> _j) ->
      VFun $ \v1 -> return $
      VFun $ \v2 -> do
        xs <- enumerateWordValueRev =<< fromWordVal "pdiv 1" =<< v1
        ys <- enumerateWordValueRev =<< fromWordVal "pdiv 2" =<< v2
        let zs = Seq.reverse $ Seq.fromList $ genericTake i (fst (mdp xs ys) ++ repeat SBV.svFalse)
        return $ VWord i $ return $ BitsVal i $ IndexSeqMap (return . VBit . Seq.index zs . fromInteger))

  , ("pmod"        , -- {a,b} (fin a, fin b) => [a] -> [b+1] -> [b]
      nlam $ \(finNat' -> _i) ->
      nlam $ \(finNat' -> j) ->
      VFun $ \v1 -> return $
      VFun $ \v2 -> do
        xs <- enumerateWordValueRev =<< fromWordVal "pmod 1" =<< v1
        ys <- enumerateWordValueRev =<< fromWordVal "pmod 2" =<< v2
        let zs = Seq.reverse $ Seq.fromList $ genericTake j (snd (mdp xs ys) ++ repeat SBV.svFalse)
        return $ VWord j $ return $ BitsVal j $ IndexSeqMap (return . VBit . Seq.index zs . fromInteger))

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
                 BitsVal n bs0 ->
                   do idx_bits <- enumerateWordValue idx
                      let op bs shft = memoMap $ IndexSeqMap $ \i ->
                                         case reindex (Nat w) i shft of
                                           Nothing -> return $ VBit $ bitLit False
                                           Just i' -> lookupSeqMap bs i'
                      BitsVal n <$> shifter (mergeSeqMap True) op bs0 idx_bits

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


selectV :: forall a
         . (SBool -> Eval a -> Eval a -> Eval a) -- ^ Mux function on @a@s
        -> WordValue SBool SWord                 -- ^ Symbolic index value
        -> (Integer -> Eval a)                   -- ^ Function from concrete indices to answers
        -> Eval a                                -- ^ overall answer
selectV mux val f =
   case val of
     WordVal x | Just idx <- SBV.svAsInteger x -> f idx
               | otherwise -> sel 0 (unpackWord x)
     BitsVal n xs -> sel 0 . map fromVBit =<< sequence (enumerateSeqMap n xs)

 where
    sel offset []       = f offset
    sel offset (b : bs) = mux b m1 m2
      where m1 = sel (offset + (2 ^ length bs)) bs
            m2 = sel offset bs


indexFront :: Maybe Integer
           -> TValue
           -> SeqMap SBool SWord
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
           return $ VWord n $ ready $ WordVal $ SBV.svSelect ws (wordLit wlen 0) idx
         Nothing -> foldr f def [0 .. 2^w  - 1]

  | otherwise
  = foldr f def [0 .. 2^w  - 1]

 where
    k = SBV.kindOf idx
    w = SBV.intSizeOf idx
    def = ready $ zeroV a
    f n y = iteValue (SBV.svEqual idx (SBV.svInteger k n)) (lookupSeqMap xs n) y


indexBack :: Maybe Integer
          -> TValue
          -> SeqMap SBool SWord
          -> SWord
          -> Eval Value
indexBack (Just n) a xs idx = indexFront (Just n) a (reverseSeqMap n xs) idx
indexBack Nothing _ _ _ = evalPanic "Expected finite sequence" ["indexBack"]

indexFront_bits :: Maybe Integer
                -> TValue
                -> SeqMap SBool SWord
                -> [SBool]
                -> Eval Value
indexFront_bits mblen a xs bits0 = go 0 (length bits0) bits0
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
               -> SeqMap SBool SWord
               -> [SBool]
               -> Eval Value
indexBack_bits (Just n) a xs idx = indexFront_bits (Just n) a (reverseSeqMap n xs) idx
indexBack_bits Nothing _ _ _ = evalPanic "Expected finite sequence" ["indexBack_bits"]


updateFrontSym
  :: Nat'
  -> TValue
  -> SeqMap SBool SWord
  -> WordValue SBool SWord
  -> Eval (GenValue SBool SWord)
  -> Eval (SeqMap SBool SWord)
updateFrontSym len _eltTy vs w val = do
  -- TODO? alternate handling if w is a list of bits...
  case w of
    WordVal wv | Just j <- SBV.svAsInteger wv -> do
        case len of
          Inf -> return ()
          Nat n -> unless (j < n) (invalidIndex j)
        return $ updateSeqMap vs j val
    _ ->
        return $ IndexSeqMap $ \i ->
          selectV iteValue w $ \j ->
            if i == j then val else lookupSeqMap vs i

updateFrontSym_word
  :: Nat'
  -> TValue
  -> WordValue SBool SWord
  -> WordValue SBool SWord
  -> Eval (GenValue SBool SWord)
  -> Eval (WordValue SBool SWord)
updateFrontSym_word Inf _ _ _ _ = evalPanic "Expected finite sequence" ["updateFrontSym_bits"]
updateFrontSym_word (Nat _) _eltTy bs w val =
  selectV (mergeWord' True) w $ \j -> updateWordValue bs j (fromVBit <$> val)

updateBackSym
  :: Nat'
  -> TValue
  -> SeqMap SBool SWord
  -> WordValue SBool SWord
  -> Eval (GenValue SBool SWord)
  -> Eval (SeqMap SBool SWord)
updateBackSym Inf _ _ _ _ = evalPanic "Expected finite sequence" ["updateBackSym"]
updateBackSym (Nat n) _eltTy vs w val = do
  -- TODO? alternate handling if w is a list of bits...
  case w of
    WordVal wv | Just j <- SBV.svAsInteger wv -> do
        unless (j < n) (invalidIndex j)
        return $ updateSeqMap vs (n - j - 1) val
    _ ->
        return $ IndexSeqMap $ \i ->
          selectV iteValue w $ \j ->
            if i == (n - j - 1) then val else lookupSeqMap vs i

updateBackSym_word
  :: Nat'
  -> TValue
  -> WordValue SBool SWord
  -> WordValue SBool SWord
  -> Eval (GenValue SBool SWord)
  -> Eval (WordValue SBool SWord)
updateBackSym_word Inf _ _ _ _ = evalPanic "Expected finite sequence" ["updateBackSym_bits"]
updateBackSym_word (Nat n) _eltTy bs w val = do
  selectV (mergeWord' True) w $ \j -> updateWordValue bs (n - j - 1) (fromVBit <$> val)

asBitList :: [Eval SBool] -> Maybe [SBool]
asBitList = go id
 where go :: ([SBool] -> [SBool]) -> [Eval SBool] -> Maybe [SBool]
       go f [] = Just (f [])
       go f (Ready b:vs) = go (f . (b:)) vs
       go _ _ = Nothing


asWordList :: [WordValue SBool SWord] -> Maybe [SWord]
asWordList = go id
 where go :: ([SWord] -> [SWord]) -> [WordValue SBool SWord] -> Maybe [SWord]
       go f [] = Just (f [])
       go f (WordVal x :vs) = go (f . (x:)) vs
       go _f (BitsVal _ _ : _) = Nothing

liftBinArith :: (SWord -> SWord -> SWord) -> BinArith SWord
liftBinArith op _ x y = ready $ op x y

sExp :: Integer -> SWord -> SWord -> Eval SWord
sExp _w x y = ready $ go (reverse (unpackWord y)) -- bits in little-endian order
  where go []       = literalSWord (SBV.intSizeOf x) 1
        go (b : bs) = SBV.svIte b (SBV.svTimes x s) s
            where a = go bs
                  s = SBV.svTimes a a

-- | Ceiling (log_2 x)
sLg2 :: Integer -> SWord -> Eval SWord
sLg2 _w x = ready $ go 0
  where
    lit n = literalSWord (SBV.intSizeOf x) n
    go i | i < SBV.intSizeOf x = SBV.svIte (SBV.svLessEq x (lit (2^i))) (lit (toInteger i)) (go (i + 1))
         | otherwise           = lit (toInteger i)

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

cmpBinary :: (SBool -> SBool -> Eval SBool -> Eval SBool)
          -> (SWord -> SWord -> Eval SBool -> Eval SBool)
          -> SBool -> Binary SBool SWord
cmpBinary fb fw b _ty v1 v2 = VBit <$> cmpValue fb fw v1 v2 (return b)

-- Signed arithmetic -----------------------------------------------------------

swordSlt :: SWord -> SWord -> Eval Value
swordSlt x y = return $ VBit lt
  where lt = SBV.svLessThan (SBV.svSign x) (SBV.svSign y)

swordSdiv :: SWord -> SWord -> Eval Value
swordSdiv x y = return . VWord (toInteger (SBV.intSizeOf x)) . ready . WordVal $ z
  where z = SBV.svQuot (SBV.svSign x) (SBV.svSign y)

swordSrem :: SWord -> SWord -> Eval Value
swordSrem x y = return . VWord (toInteger (SBV.intSizeOf x)) . ready . WordVal $ z
  where z = SBV.svRem (SBV.svSign x) (SBV.svSign y)

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

-- Polynomials -----------------------------------------------------------------

-- TODO: Data.SBV.BitVectors.Polynomials should export ites, addPoly,
-- and mdp (the following definitions are copied from that module)

-- | Add two polynomials
addPoly :: [SBool] -> [SBool] -> [SBool]
addPoly xs    []      = xs
addPoly []    ys      = ys
addPoly (x:xs) (y:ys) = SBV.svXOr x y : addPoly xs ys

ites :: SBool -> [SBool] -> [SBool] -> [SBool]
ites s xs ys
 | Just t <- SBV.svAsBool s
 = if t then xs else ys
 | True
 = go xs ys
 where go [] []         = []
       go []     (b:bs) = SBV.svIte s SBV.svFalse b : go [] bs
       go (a:as) []     = SBV.svIte s a SBV.svFalse : go as []
       go (a:as) (b:bs) = SBV.svIte s a b : go as bs

-- conservative over-approximation of the degree
degree :: [SBool] -> Int
degree xs = walk (length xs - 1) $ reverse xs
  where walk n []     = n
        walk n (b:bs)
         | Just t <- SBV.svAsBool b
         = if t then n else walk (n-1) bs
         | True
         = n -- over-estimate

mdp :: [SBool] -> [SBool] -> ([SBool], [SBool])
mdp xs ys = go (length ys - 1) (reverse ys)
  where degTop  = degree xs
        go _ []     = error "SBV.Polynomial.mdp: Impossible happened; exhausted ys before hitting 0"
        go n (b:bs)
         | n == 0   = (reverse qs, rs)
         | True     = let (rqs, rrs) = go (n-1) bs
                      in (ites b (reverse qs) rqs, ites b rs rrs)
         where degQuot = degTop - n
               ys' = replicate degQuot SBV.svFalse ++ ys
               (qs, rs) = divx (degQuot+1) degTop xs ys'

-- return the element at index i; if not enough elements, return false
-- N.B. equivalent to '(xs ++ repeat false) !! i', but more efficient
nth :: [SBool] -> Int -> SBool
nth []     _ = SBV.svFalse
nth (x:_)  0 = x
nth (_:xs) i = nth xs (i-1)

divx :: Int -> Int -> [SBool] -> [SBool] -> ([SBool], [SBool])
divx n _ xs _ | n <= 0 = ([], xs)
divx n i xs ys'        = (q:qs, rs)
  where q        = xs `nth` i
        xs'      = ites q (xs `addPoly` ys') xs
        (qs, rs) = divx (n-1) (i-1) xs' (tail ys')
