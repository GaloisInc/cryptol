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
import Data.List (genericTake, sortBy)
import Data.Ord (comparing)
import qualified Data.Sequence as Seq
import qualified Data.Foldable as Fold

import Cryptol.Eval.Monad (Eval(..), ready, invalidIndex)
import Cryptol.Eval.Type  (finNat', TValue(..))
import Cryptol.Eval.Value (BitWord(..), EvalPrims(..), enumerateSeqMap, SeqMap(..),
                          reverseSeqMap, wlam, nlam, WordValue(..),
                          asWordVal, asBitsVal, fromWordVal, updateSeqMap, lookupSeqMap )
import Cryptol.Prims.Eval (binary, unary, arithUnary,
                           arithBinary, Binary, BinArith,
                           logicBinary, logicUnary, zeroV,
                           ccatV, splitAtV, joinV, ecSplitV,
                           reverseV, infFromV, infFromThenV,
                           fromThenV, fromToV, fromThenToV,
                           transposeV, indexPrimOne, indexPrimMany,
                           ecIntegerV, ecToIntegerV, ecFromIntegerV,
                           ecDemoteV, updatePrim, lg2)
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

instance EvalPrims SBool SWord SInteger where
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
  , ("integer"     , ecIntegerV) -- Converts a numeric type into its corresponding value.
                                 -- { val } (fin val) => Integer
  , ("+"           , binary (arithBinary (liftBinArith SBV.svPlus) SBV.svPlus)) -- {a} (Arith a) => a -> a -> a
  , ("-"           , binary (arithBinary (liftBinArith SBV.svMinus) SBV.svMinus)) -- {a} (Arith a) => a -> a -> a
  , ("*"           , binary (arithBinary (liftBinArith SBV.svTimes) SBV.svTimes)) -- {a} (Arith a) => a -> a -> a
  , ("/"           , binary (arithBinary (liftBinArith SBV.svQuot) SBV.svQuot)) -- {a} (Arith a) => a -> a -> a
  , ("%"           , binary (arithBinary (liftBinArith SBV.svRem) SBV.svRem)) -- {a} (Arith a) => a -> a -> a
  , ("^^"          , binary (arithBinary sExp SBV.svExp)) -- {a} (Arith a) => a -> a -> a
  , ("lg2"         , unary (arithUnary sLg2 svLg2)) -- {a} (Arith a) => a -> a
  , ("negate"      , unary (arithUnary (\_ -> SBV.svUNeg) SBV.svUNeg))
  , ("<"           , binary (cmpBinary cmpLt cmpLt cmpLt SBV.svFalse))
  , (">"           , binary (cmpBinary cmpGt cmpGt cmpGt SBV.svFalse))
  , ("<="          , binary (cmpBinary cmpLtEq cmpLtEq cmpLtEq SBV.svTrue))
  , (">="          , binary (cmpBinary cmpGtEq cmpGtEq cmpGtEq SBV.svTrue))
  , ("=="          , binary (cmpBinary cmpEq cmpEq cmpEq SBV.svTrue))
  , ("!="          , binary (cmpBinary cmpNotEq cmpNotEq cmpNotEq SBV.svFalse))
  , ("&&"          , binary (logicBinary SBV.svAnd SBV.svAnd SBV.svAnd))
  , ("||"          , binary (logicBinary SBV.svOr SBV.svOr SBV.svOr))
  , ("^"           , binary (logicBinary SBV.svXOr SBV.svXOr SBV.svXOr))
  , ("complement"  , unary (logicUnary SBV.svNot SBV.svNot SBV.svNot))
  , ("zero"        , tlam zeroV)
  , ("toInteger"   , ecToIntegerV)
  , ("fromInteger" , ecFromIntegerV)
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

  , ("update"      , updatePrim updateFrontSym_bits updateFrontSym)
  , ("updateEnd"   , updatePrim updateBackSym_bits updateBackSym)

  , ("pmult"       , -- {a,b} (fin a, fin b) => [a] -> [b] -> [max 1 (a + b) - 1]
      nlam $ \(finNat' -> i) ->
      nlam $ \(finNat' -> j) ->
      VFun $ \v1 -> return $
      VFun $ \v2 -> do
        let k = max 1 (i + j) - 1
            mul _  []     ps = ps
            mul as (b:bs) ps = mul (SBV.svFalse : as) bs (ites b (as `addPoly` ps) ps)
        xs <- sequence . Fold.toList . asBitsVal =<< fromWordVal "pmult 1" =<< v1
        ys <- sequence . Fold.toList . asBitsVal =<< fromWordVal "pmult 2" =<< v2
        let zs = genericTake k (mul xs ys [] ++ repeat SBV.svFalse)
        return $ VWord k $ return $ BitsVal $ Seq.fromList $ map ready zs)

  , ("pdiv"        , -- {a,b} (fin a, fin b) => [a] -> [b] -> [a]
      nlam $ \(finNat' -> i) ->
      nlam $ \(finNat' -> _j) ->
      VFun $ \v1 -> return $
      VFun $ \v2 -> do
        xs <- sequence . Fold.toList . Seq.reverse . asBitsVal =<< fromWordVal "pdiv 1" =<< v1
        ys <- sequence . Fold.toList . Seq.reverse . asBitsVal =<< fromWordVal "pdiv 2" =<< v2
        let zs = genericTake i (fst (mdp xs ys) ++ repeat SBV.svFalse)
        return $ VWord i $ return $ BitsVal $ Seq.reverse $ Seq.fromList $ map ready zs)

  , ("pmod"        , -- {a,b} (fin a, fin b) => [a] -> [b+1] -> [b]
      nlam $ \(finNat' -> _i) ->
      nlam $ \(finNat' -> j) ->
      VFun $ \v1 -> return $
      VFun $ \v2 -> do
        xs <- sequence . Fold.toList . Seq.reverse . asBitsVal =<< fromWordVal "pmod 1" =<< v1
        ys <- sequence . Fold.toList . Seq.reverse . asBitsVal =<< fromWordVal "pmod 2" =<< v2
        let zs = genericTake j (snd (mdp xs ys) ++ repeat SBV.svFalse)
        return $ VWord j $ return $ BitsVal $ Seq.reverse $ Seq.fromList $ map ready zs)

    -- {at,len} (fin len) => [len][8] -> at
  , ("error"       ,
      tlam $ \at ->
      nlam $ \(finNat' -> _len) ->
      VFun $ \_msg ->
        return $ zeroV at) -- error/undefined, is arbitrarily translated to 0

  , ("random"      ,
      tlam $ \_a ->
      wlam $ \_x ->
         Thunk $ return $ panic
            "Cryptol.Symbolic.Prims.evalECon"
            [ "can't symbolically evaluate ECRandom" ])

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


iteWord :: SBool
        -> Eval (WordValue SBool SWord)
        -> Eval (WordValue SBool SWord)
        -> Eval (WordValue SBool SWord)
iteWord c x y = mergeWord True c <$> x <*> y

logicShift :: String
           -> (SWord -> SWord -> SWord)
           -> (Nat' -> Integer -> Integer -> Maybe Integer)
           -> Value
logicShift nm wop reindex =
      nlam $ \_m ->
      nlam $ \n ->
      tlam $ \a ->
      VFun $ \xs -> return $
      VFun $ \y -> do
        let Nat _len = n
        idx <- fromWordVal "<<" =<< y

        xs >>= \case
          VWord w x -> return $ VWord w $ do
                         x >>= \case
                           WordVal x' -> WordVal . wop x' <$> asWordVal idx
                           BitsVal bs -> selectV iteWord idx $ \shft -> return $
                                           BitsVal $ Seq.fromFunction (Seq.length bs) $ \i ->
                                             case reindex (Nat w) (toInteger i) shft of
                                               Nothing -> return $ bitLit False
                                               Just _  -> Seq.index bs i

          VSeq w vs  -> selectV iteValue idx $ \shft -> return $
                          VSeq w $ IndexSeqMap $ \i ->
                            case reindex (Nat w) i shft of
                              Nothing -> return $ zeroV a
                              Just i' -> lookupSeqMap vs i'

          VStream vs -> selectV iteValue idx $ \shft -> return $
                          VStream $ IndexSeqMap $ \i ->
                            case reindex Inf i shft of
                              Nothing -> return $ zeroV a
                              Just i' -> lookupSeqMap vs i'

          _ -> evalPanic "expected sequence value in shift operation" [nm]


selectV :: forall a
         . (SBool -> Eval a -> Eval a -> Eval a)
        -> WordValue SBool SWord
        -> (Integer -> Eval a)
        -> Eval a
selectV mux val f =
   case val of
     WordVal x | Just idx <- SBV.svAsInteger x -> f idx
               | otherwise -> sel 0 (unpackWord x)
     BitsVal bs -> sel 0 =<< sequence (Fold.toList bs)

 where
    sel offset []       = f offset
    sel offset (b : bs) = mux b m1 m2
      where m1 = sel (offset + 2 ^ length bs) bs
            m2 = sel offset bs


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
           return $ VWord n $ ready $ WordVal $ SBV.svSelect ws (wordLit wlen 0) idx
         Nothing -> foldr f def [0 .. 2^w  - 1]

  | otherwise
  = foldr f def [0 .. 2^w  - 1]

 where
    k = SBV.kindOf idx
    w = SBV.intSizeOf idx
    def = ready $ VWord (toInteger w) $ ready $ WordVal $ SBV.svInteger k 0
    f n y = iteValue (SBV.svEqual idx (SBV.svInteger k n)) (lookupSeqMap xs n) y


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


updateFrontSym
  :: Nat'
  -> TValue
  -> SeqMap SBool SWord SInteger
  -> WordValue SBool SWord
  -> Eval (GenValue SBool SWord SInteger)
  -> Eval (SeqMap SBool SWord SInteger)
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

updateFrontSym_bits
  :: Nat'
  -> TValue
  -> Seq.Seq (Eval SBool)
  -> WordValue SBool SWord
  -> Eval (GenValue SBool SWord SInteger)
  -> Eval (Seq.Seq (Eval SBool))
updateFrontSym_bits Inf _ _ _ _ = evalPanic "Expected finite sequence" ["updateFrontSym_bits"]
updateFrontSym_bits (Nat n) _eltTy bs w val = do
  -- TODO? alternate handling if w is a list of bits...
  case w of
    WordVal wv | Just j <- SBV.svAsInteger wv -> do
      unless (j < n) (invalidIndex j)
      return $! Seq.update (fromInteger j) (fromVBit <$> val) bs
    _ -> do
      let mergeBit' c x y = mergeBit True c <$> x <*> y
      return $ Seq.fromFunction (fromInteger n) $ \i ->
        selectV mergeBit' w $ \j ->
          if toInteger i == j then (fromVBit <$> val) else Seq.index bs i

updateBackSym
  :: Nat'
  -> TValue
  -> SeqMap SBool SWord SInteger
  -> WordValue SBool SWord
  -> Eval (GenValue SBool SWord SInteger)
  -> Eval (SeqMap SBool SWord SInteger)
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

updateBackSym_bits
  :: Nat'
  -> TValue
  -> Seq.Seq (Eval SBool)
  -> WordValue SBool SWord
  -> Eval (GenValue SBool SWord SInteger)
  -> Eval (Seq.Seq (Eval SBool))
updateBackSym_bits Inf _ _ _ _ = evalPanic "Expected finite sequence" ["updateBackSym_bits"]
updateBackSym_bits (Nat n) _eltTy bs w val = do
  -- TODO? alternate handling if w is a list of bits...
  case w of
    WordVal wv | Just j <- SBV.svAsInteger wv -> do
      unless (j < n) (invalidIndex j)
      return $! Seq.update (fromInteger (n - j - 1)) (fromVBit <$> val) bs
    _ -> do
      let mergeBit' c x y = mergeBit True c <$> x <*> y
      return $ Seq.fromFunction (fromInteger n) $ \i ->
        selectV mergeBit' w $ \j ->
          if toInteger i == (n - j - 1) then (fromVBit <$> val) else Seq.index bs i


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
       go f (BitsVal bs:vs) =
              case asBitList (Fold.toList bs) of
                  Just xs -> go (f . (packWord xs:)) vs
                  Nothing -> Nothing



liftBinArith :: (SWord -> SWord -> SWord) -> BinArith SWord
liftBinArith op _ = op

sExp :: Integer -> SWord -> SWord -> SWord
sExp _w x y = go (reverse (unpackWord y)) -- bits in little-endian order
  where go []       = literalSWord (SBV.intSizeOf x) 1
        go (b : bs) = SBV.svIte b (SBV.svTimes x s) s
            where a = go bs
                  s = SBV.svTimes a a

-- | Ceiling (log_2 x)
sLg2 :: Integer -> SWord -> SWord
sLg2 _w x = go 0
  where
    lit n = literalSWord (SBV.intSizeOf x) n
    go i | i < SBV.intSizeOf x = SBV.svIte (SBV.svLessEq x (lit (2^i))) (lit (toInteger i)) (go (i + 1))
         | otherwise           = lit (toInteger i)

-- | Ceiling (log_2 x)
svLg2 :: SInteger -> SInteger
svLg2 x =
  case SBV.svAsInteger x of
    Just n -> SBV.svInteger SBV.KUnbounded (lg2 n)
    Nothing -> evalPanic "cannot compute lg2 of symbolic unbounded integer" []

-- Cmp -------------------------------------------------------------------------

cmpValue :: (SBool -> SBool -> Eval a -> Eval a)
         -> (SWord -> SWord -> Eval a -> Eval a)
         -> (SInteger -> SInteger -> Eval a -> Eval a)
         -> (Value -> Value -> Eval a -> Eval a)
cmpValue fb fw fi = cmp
  where
    cmp v1 v2 k =
      case (v1, v2) of
        (VRecord fs1, VRecord fs2) -> let vals = map snd . sortBy (comparing fst)
                                      in  cmpValues (vals fs1) (vals fs2) k
        (VTuple vs1 , VTuple vs2 ) -> cmpValues vs1 vs2 k
        (VBit b1    , VBit b2    ) -> fb b1 b2 k
        (VInteger i1, VInteger i2) -> fi i1 i2 k
        (VWord _ w1 , VWord _ w2 ) -> join (fw <$> (asWordVal =<< w1)
                                               <*> (asWordVal =<< w2)
                                               <*> return k)
        (VSeq n vs1 , VSeq _ vs2 ) -> cmpValues (enumerateSeqMap n vs1)
                                                (enumerateSeqMap n vs2) k
        (VStream {} , VStream {} ) -> panic "Cryptol.Symbolic.Prims.cmpValue"
                                        [ "Infinite streams are not comparable" ]
        (VFun {}    , VFun {}    ) -> panic "Cryptol.Symbolic.Prims.cmpValue"
                                        [ "Functions are not comparable" ]
        (VPoly {}   , VPoly {}   ) -> panic "Cryptol.Symbolic.Prims.cmpValue"
                                        [ "Polymorphic values are not comparable" ]
        (_          , _          ) -> panic "Cryptol.Symbolic.Prims.cmpValue"
                                        [ "type mismatch" ]

    cmpValues (x1 : xs1) (x2 : xs2) k = do
          x1' <- x1
          x2' <- x2
          cmp x1' x2' (cmpValues xs1 xs2 k)
    cmpValues _ _ k = k

cmpEq :: SWord -> SWord -> Eval SBool -> Eval SBool
cmpEq x y k = SBV.svAnd (SBV.svEqual x y) <$> k

cmpNotEq :: SWord -> SWord -> Eval SBool -> Eval SBool
cmpNotEq x y k = SBV.svOr (SBV.svNotEqual x y) <$> k

cmpLt, cmpGt :: SWord -> SWord -> Eval SBool -> Eval SBool
cmpLt x y k = SBV.svOr (SBV.svLessThan x y) <$> (cmpEq x y k)
cmpGt x y k = SBV.svOr (SBV.svGreaterThan x y) <$> (cmpEq x y k)

cmpLtEq, cmpGtEq :: SWord -> SWord -> Eval SBool -> Eval SBool
cmpLtEq x y k = SBV.svAnd (SBV.svLessEq x y) <$> (cmpNotEq x y k)
cmpGtEq x y k = SBV.svAnd (SBV.svGreaterEq x y) <$> (cmpNotEq x y k)

cmpBinary :: (SBool -> SBool -> Eval SBool -> Eval SBool)
          -> (SWord -> SWord -> Eval SBool -> Eval SBool)
          -> (SInteger -> SInteger -> Eval SBool -> Eval SBool)
          -> SBool -> Binary SBool SWord SInteger
cmpBinary fb fw fi b _ty v1 v2 = VBit <$> cmpValue fb fw fi v1 v2 (return b)

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
