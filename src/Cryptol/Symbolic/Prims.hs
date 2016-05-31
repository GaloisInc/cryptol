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
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Cryptol.Symbolic.Prims where

import Data.Bits
import Data.List (genericDrop, genericReplicate, genericSplitAt, genericTake, sortBy, transpose)
import Data.Ord (comparing)

import Cryptol.Eval.Monad (Eval(..), ready)
import Cryptol.Eval.Value (BitWord(..), EvalPrims(..), enumerateSeqMap, SeqMap(..),
                          finiteSeqMap, reverseSeqMap)
import Cryptol.Prims.Eval (binary, unary, tlamN, arithUnary,
                           arithBinary, Binary, BinArith,
                           logicBinary, logicUnary, zeroV,
                           ccatV, splitAtV, joinV, ecSplitV,
                           reverseV, infFromV, infFromThenV,
                           fromThenV, fromToV, fromThenToV,
                           transposeV, indexPrimOne, indexPrimMany)
import Cryptol.Symbolic.Value
import Cryptol.TypeCheck.AST (Decl(..))
import Cryptol.TypeCheck.Solver.InfNat(Nat'(..), nMul)
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
  , ("-"           , binary (arithBinary (liftBinArith  SBV.svMinus))) -- {a} (Arith a) => a -> a -> a
  , ("*"           , binary (arithBinary (liftBinArith SBV.svTimes))) -- {a} (Arith a) => a -> a -> a
  , ("/"           , binary (arithBinary (liftBinArith SBV.svQuot))) -- {a} (Arith a) => a -> a -> a
  , ("%"           , binary (arithBinary (liftBinArith SBV.svRem))) -- {a} (Arith a) => a -> a -> a
  , ("^^"          , binary (arithBinary sExp)) -- {a} (Arith a) => a -> a -> a
  , ("lg2"         , unary (arithUnary sLg2)) -- {a} (Arith a) => a -> a
  , ("negate"      , unary (arithUnary (\_ -> SBV.svUNeg)))
  , ("<"           , binary (cmpBinary cmpLt cmpLt SBV.svFalse))
  , (">"           , binary (cmpBinary cmpGt cmpGt SBV.svFalse))
  , ("<="          , binary (cmpBinary cmpLtEq cmpLtEq SBV.svTrue))
  , (">="          , binary (cmpBinary cmpGtEq cmpGtEq SBV.svTrue))
  , ("=="          , binary (cmpBinary cmpEq cmpEq SBV.svTrue))
  , ("!="          , binary (cmpBinary cmpNotEq cmpNotEq SBV.svFalse))
  , ("&&"          , binary (logicBinary SBV.svAnd SBV.svAnd))
  , ("||"          , binary (logicBinary SBV.svOr SBV.svOr))
  , ("^"           , binary (logicBinary SBV.svXOr SBV.svXOr))
  , ("complement"  , unary (logicUnary SBV.svNot SBV.svNot))
  , ("zero"        , tlam zeroV)

  , ("<<"          ,  -- {m,n,a} (fin n) => [m] a -> [n] -> [m] a
      tlam $ \m ->
      tlam $ \n ->
      tlam $ \a ->
      VFun $ \xs -> return $
      VFun $ \y ->
        xs >>= \case
          VWord x -> VWord . SBV.svShiftLeft x <$> (fromVWord "<<" =<< y)
          x -> do
            x' <- fromSeq x
            let Nat len = numTValue n
            let shl :: Integer -> Value
                shl =
                  case numTValue m of
                    Inf   -> \i -> VStream $ SeqMap $ \idx -> lookupSeqMap x' (i+idx)
                    Nat j -> \i -> VSeq j (isTBit a) $ SeqMap $ \idx ->
                                       if i+idx >= j then
                                         return $ zeroV a
                                       else
                                         lookupSeqMap x' (i+idx)
             in selectV len shl =<< y)

  , (">>"          , -- {m,n,a} (fin n) => [m] a -> [n] -> [m] a
      tlam $ \m ->
      tlam $ \n ->
      tlam $ \a ->
      VFun $ \xs -> return $
      VFun $ \y ->
        xs >>= \case
          VWord x -> VWord . SBV.svShiftRight x <$> (fromVWord ">>" =<< y)
          x -> do
            x' <- fromSeq x
            let Nat len = numTValue n
            let shr :: Integer -> Value
                shr =
                  case numTValue m of
                    Inf   -> \i -> VStream $ SeqMap $ \idx ->
                                       if idx-i < 0 then
                                         return $ zeroV a
                                       else
                                         lookupSeqMap x' (idx-i)
                    Nat j -> \i -> VSeq j (isTBit a) $ SeqMap $ \idx ->
                                       if idx-i < 0 then
                                         return $ zeroV a
                                       else
                                         lookupSeqMap x' (idx-i)
            selectV len shr =<< y)

  , ("<<<"         , -- {m,n,a} (fin m, fin n) => [m] a -> [n] -> [m] a
      tlam $ \m ->
      tlam $ \n ->
      tlam $ \a ->
      VFun $ \xs -> return $
      VFun $ \y ->
        xs >>= \case
          VWord x -> VWord . SBV.svRotateLeft x <$> (fromVWord "<<<" =<< y)
          x -> do
            x' <- fromSeq x
            let len = finTValue n
            let m'  = finTValue m
            let rol :: Integer -> Value
                rol i = VSeq m' (isTBit a) $ SeqMap $ \idx ->
                          lookupSeqMap x' ((i+idx) `mod` m')
            selectV len rol =<< y)

  , (">>>"         , -- {m,n,a} (fin m, fin n) => [m] a -> [n] -> [m] a
      tlam $ \m ->
      tlam $ \n ->
      tlam $ \a ->
      VFun $ \xs -> return $
      VFun $ \y ->
        xs >>= \case
          VWord x -> VWord . SBV.svRotateRight x <$> (fromVWord ">>>" =<< y)
          x -> do
            x' <- fromSeq x
            let len = finTValue n
            let m'  = finTValue m
            let rol :: Integer -> Value
                rol i = VSeq m' (isTBit a) $ SeqMap $ \idx ->
                          lookupSeqMap x' ((idx+m'-i) `mod` m')
            selectV len rol =<< y)

  , ("#"          , -- {a,b,d} (fin a) => [a] d -> [b] d -> [a + b] d
     tlam $ \ front ->
     tlam $ \ back  ->
     tlam $ \ elty  ->
     lam  $ \ l     -> return $
     lam  $ \ r     -> ccatV front back elty l r)

  , ("splitAt"    ,
     tlam $ \ front ->
     tlam $ \ back  ->
     tlam $ \ a     ->
     lam  $ \ x     ->
       splitAtV front back a =<< x)

  , ("join"       ,
     tlam $ \ parts ->
     tlam $ \ each  ->
     tlam $ \ a     ->
     lam  $ \ x     ->
       joinV parts each a =<< x)

  , ("split"       , ecSplitV)

  , ("reverse"    , tlam $ \a ->
                    tlam $ \b ->
                     lam $ \xs -> reverseV =<< xs)

  , ("transpose"  , tlam $ \a ->
                    tlam $ \b ->
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


  , ("pmult"       , -- {a,b} (fin a, fin b) => [a] -> [b] -> [max 1 (a + b) - 1]
      tlam $ \(finTValue -> i) ->
      tlam $ \(finTValue -> j) ->
      VFun $ \v1 -> return $
      VFun $ \v2 -> do
        let k = max 1 (i + j) - 1
            mul _  []     ps = ps
            mul as (b:bs) ps = mul (SBV.svFalse : as) bs (ites b (as `addPoly` ps) ps)
        xs <- traverse (fromVBit<$>) . enumerateSeqMap i =<< fromSeq =<< v1
        ys <- traverse (fromVBit<$>) . enumerateSeqMap j =<< fromSeq =<< v2
        let zs = genericTake k (mul xs ys [] ++ repeat SBV.svFalse)
        VSeq k True <$> finiteSeqMap (map (ready . VBit) zs))


  , ("pdiv"        , -- {a,b} (fin a, fin b) => [a] -> [b] -> [a]
      tlam $ \(finTValue -> i) ->
      tlam $ \(finTValue -> j) ->
      VFun $ \v1 -> return $
      VFun $ \v2 -> do
        xs <- traverse (fromVBit<$>) . enumerateSeqMap i =<< fromSeq =<< v1
        ys <- traverse (fromVBit<$>) . enumerateSeqMap j =<< fromSeq =<< v2
        let zs = take (fromInteger i) (fst (mdp (reverse xs) (reverse ys)) ++ repeat SBV.svFalse)
        VSeq i True <$> finiteSeqMap (map (ready . VBit) (reverse zs)))

  , ("pmod"        , -- {a,b} (fin a, fin b) => [a] -> [b+1] -> [b]
      tlam $ \(finTValue -> i) ->
      tlam $ \(finTValue -> j) ->
      VFun $ \v1 -> return $
      VFun $ \v2 -> do
        xs <- traverse (fromVBit<$>) . enumerateSeqMap i =<< fromSeq =<< v1
        ys <- traverse (fromVBit<$>) . enumerateSeqMap (j+1) =<< fromSeq =<< v2
        let zs = take (fromInteger j) (snd (mdp (reverse xs) (reverse ys)) ++ repeat SBV.svFalse)
        VSeq j True <$> finiteSeqMap (map (ready . VBit) (reverse zs)))

    -- {at,len} (fin len) => [len][8] -> at
  , ("error"       ,
      tlam $ \at ->
      tlam $ \(finTValue -> _len) ->
      VFun $ \_msg ->
        return $ zeroV at) -- error/undefined, is arbitrarily translated to 0

  , ("random"      ,
      tlam $ \_a ->
       lam $ \_x -> return $
         panic "Cryptol.Symbolic.Prims.evalECon"
               [ "can't symbolically evaluae ECRandom" ])

     -- The trace function simply forces its first two
     -- values before returing the third in the symbolic
     -- evaluator.
  , ("trace",
      tlam $ \_a ->
      tlam $ \_b ->
       lam $ \s -> return $
       lam $ \x -> return $
       lam $ \y -> do
         _ <- s
         _ <- x
         y)
  ]


selectV :: Integer -> (Integer -> Value) -> Value -> Eval Value
selectV _len f (VWord v) | Just idx <- SBV.svAsInteger v = return $ f idx

selectV len f v = sel 0 =<< bits
  where
    bits = enumerateSeqMap len <$> fromSeq v -- index bits in big-endian order

    sel :: Integer -> [Eval Value] -> Eval Value
    sel offset []       = return $ f offset
    sel offset (b : bs) = do b' <- fromVBit <$> b
                             iteValue b' m1 m2
      where m1 = sel (offset + 2 ^ length bs) bs
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
  , Just (finTValue -> wlen, a') <- isTSeq a
  , isTBit a'
  , Just ws <- asWordList (enumerateSeqMap n xs)
  = return $ VWord $ SBV.svSelect ws (wordLit wlen 0) idx

  | otherwise
  = foldr f def [0 .. 2 ^ SBV.intSizeOf idx - 1]
      where
        k = SBV.kindOf idx
        def = ready $ VWord $ SBV.svInteger k 0
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


asBitList :: [Eval Value] -> Maybe [SBool]
asBitList = go id
 where go :: ([SBool] -> [SBool]) -> [Eval Value] -> Maybe [SBool]
       go f [] = Just (f [])
       go f (Ready (VBit b):vs) = go (f . (b:)) vs
       go _ _ = Nothing

asWordList :: [Eval Value] -> Maybe [SWord]
asWordList = go id
 where go :: ([SWord] -> [SWord]) -> [Eval Value] -> Maybe [SWord]
       go f [] = Just (f [])
       go f (Ready (VWord x):vs) = go (f . (x:)) vs
       go f (Ready (VSeq i True bs):vs) =
              case asBitList (enumerateSeqMap i bs) of
                  Just xs -> go (f . (packWord xs:)) vs
                  Nothing -> Nothing
       go _ _ = Nothing


-- | Make a numeric constant.
-- { val, bits } (fin val, fin bits, bits >= width val) => [bits]
ecDemoteV :: Value
ecDemoteV = tlam $ \valT ->
            tlam $ \bitT ->
            case (numTValue valT, numTValue bitT) of
              (Nat v, Nat bs) -> VWord (literalSWord (fromInteger bs) v)
              _ -> evalPanic "Cryptol.Prove.evalECon"
                       ["Unexpected Inf in constant."
                       , show valT
                       , show bitT
                       ]

{-
-- Type Values -----------------------------------------------------------------

-- | An easy-to-use alternative representation for type `TValue`.
data TypeVal
  = TVBit
  | TVSeq Int TypeVal
  | TVStream TypeVal
  | TVTuple [TypeVal]
  | TVRecord [(Ident, TypeVal)]
  | TVFun TypeVal TypeVal

toTypeVal :: TValue -> TypeVal
toTypeVal ty
  | isTBit ty                    = TVBit
  | Just (n, ety) <- isTSeq ty   = case numTValue n of
                                     Nat w -> TVSeq (fromInteger w) (toTypeVal ety)
                                     Inf   -> TVStream (toTypeVal ety)
  | Just (aty, bty) <- isTFun ty = TVFun (toTypeVal aty) (toTypeVal bty)
  | Just (_, tys) <- isTTuple ty = TVTuple (map toTypeVal tys)
  | Just fields <- isTRec ty     = TVRecord [ (n, toTypeVal aty) | (n, aty) <- fields ]
  | otherwise                    = panic "Cryptol.Symbolic.Prims.toTypeVal" [ "bad TValue" ]

-}

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

-- Cmp -------------------------------------------------------------------------

cmpValue :: (SBool -> SBool -> Eval a -> Eval a)
         -> (SWord -> SWord -> Eval a -> Eval a)
         -> (Value -> Value -> Eval a -> Eval a)
cmpValue fb fw = cmp
  where
    cmp v1 v2 k =
      case (v1, v2) of
        (VRecord fs1, VRecord fs2) -> let vals = map snd . sortBy (comparing fst)
                                      in  cmpValues (vals fs1) (vals fs2) k
        (VTuple vs1 , VTuple vs2 ) -> cmpValues vs1 vs2 k
        (VBit b1    , VBit b2    ) -> fb b1 b2 k
        (VWord w1   , VWord w2   ) -> fw w1 w2 k
        (VSeq n _ vs1 , VSeq _ _ vs2 ) -> cmpValues (enumerateSeqMap n vs1)
                                                    (enumerateSeqMap n vs2) k
        (VStream {} , VStream {} ) -> panic "Cryptol.Symbolic.Prims.cmpValue"
                                        [ "Infinite streams are not comparable" ]
        (VFun {}    , VFun {}    ) -> panic "Cryptol.Symbolic.Prims.cmpValue"
                                        [ "Functions are not comparable" ]
        (VPoly {}   , VPoly {}   ) -> panic "Cryptol.Symbolic.Prims.cmpValue"
                                        [ "Polymorphic values are not comparable" ]
        (VWord w1   , _          ) -> do w2 <- fromVWord "cmpValue right" v2
                                         fw w1 w2 k
        (_          , VWord w2   ) -> do w1 <- fromVWord "cmpValue left" v1
                                         fw w1 w2 k
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
          -> SBool -> Binary SBool SWord
cmpBinary fb fw b _ty v1 v2 = VBit <$> cmpValue fb fw v1 v2 (return b)

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
idx :: [SBool] -> Int -> SBool
idx []     _ = SBV.svFalse
idx (x:_)  0 = x
idx (_:xs) i = idx xs (i-1)

divx :: Int -> Int -> [SBool] -> [SBool] -> ([SBool], [SBool])
divx n _ xs _ | n <= 0 = ([], xs)
divx n i xs ys'        = (q:qs, rs)
  where q        = xs `idx` i
        xs'      = ites q (xs `addPoly` ys') xs
        (qs, rs) = divx (n-1) (i-1) xs' (tail ys')
