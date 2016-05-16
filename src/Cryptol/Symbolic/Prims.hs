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

import Data.List (genericDrop, genericReplicate, genericSplitAt, genericTake, sortBy, transpose)
import Data.Ord (comparing)

import Cryptol.Eval.Monad (Eval)
import Cryptol.Eval.Value (BitWord(..), EvalPrims(..), enumerateSeqMap, SeqMap(..))
import Cryptol.Prims.Eval (binary, unary, tlamN, arithUnary,
                           arithBinary, Binary, BinArith,
                           logicBinary, logicUnary, zeroV)
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
          VWord x -> VWord . SBV.svShiftLeft x <$> (fromVWord "<<" =<< y)
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
             in selectV len shr =<< y)
  ]
{-
  , ("<<<"         , -- {m,n,a} (fin m, fin n) => [m] a -> [n] -> [m] a
      tlam $ \m ->
      tlam $ \_ ->
      tlam $ \_ ->
      VFun $ \xs ->
      VFun $ \y ->
        case xs of
          VWord x -> VWord (SBV.svRotateLeft x (fromVWord y))
          _ -> let rol :: Integer -> Value
                   rol i = catV (dropV k xs) (takeV k xs)
                     where k = i `mod` finTValue m
                in selectV rol y)

  , (">>>"         , -- {m,n,a} (fin m, fin n) => [m] a -> [n] -> [m] a
      tlam $ \m ->
      tlam $ \_ ->
      tlam $ \_ ->
      VFun $ \xs ->
      VFun $ \y ->
        case xs of
          VWord x -> VWord (SBV.svRotateRight x (fromVWord y))
          _ ->
            let ror :: Integer -> Value
                ror i = catV (dropV k xs) (takeV k xs)
                  where k = (- i) `mod` finTValue m
             in selectV ror y)

  , ("#"           , -- {a,b,d} (fin a) => [a] d -> [b] d -> [a + b] d
      tlam $ \_ ->
      tlam $ \_ ->
      tlam $ \_ ->
      VFun $ \v1 ->
      VFun $ \v2 -> catV v1 v2)

  , ("splitAt"     , -- {a,b,c} (fin a) => [a+b] c -> ([a]c,[b]c)
      tlam $ \(finTValue -> a) ->
      tlam $ \_ ->
      tlam $ \_ ->
      VFun $ \v -> VTuple [takeV a v, dropV a v])

  , ("join"        , tlam $ \ parts ->
                     tlam $ \ each  ->
                     tlam $ \ a     -> lam (joinV parts each a))

  , ("split"       , ecSplitV)

  , ("reverse"     ,
      tlam $ \a ->
      tlam $ \b ->
       lam $ \(fromSeq -> xs) -> toSeq a b (reverse xs))

  , ("transpose"    ,
      tlam $ \a ->
      tlam $ \b ->
      tlam $ \c ->
       lam $ \((map fromSeq . fromSeq) -> xs) ->
          case numTValue a of
             Nat 0 ->
               let v = toSeq a c []
               in case numTValue b of
                    Nat n -> toSeq b (tvSeq a c) $ genericReplicate n v
                    Inf   -> VStream $ repeat v
             _ -> toSeq b (tvSeq a c) $ map (toSeq a c) $ transpose xs)

  , ("@"           , -- {n,a,i} (fin i) => [n]a -> [i] -> a
      tlam $ \_ ->
      tlam $ \a ->
      tlam $ \_ ->
      VFun $ \xs ->
      VFun $ \y ->
        let isInf = case xs of VStream _ -> True; _ -> False
            err = zeroV a -- default for out-of-bounds accesses
        in atV isInf err (fromSeq xs) y)

  , ("@@"          , -- {n,a,m,i} (fin i) => [n]a -> [m][i] -> [m]a
      tlam $ \_ ->
      tlam $ \a ->
      tlam $ \_ ->
      tlam $ \_ ->
      VFun $ \xs ->
      VFun $ \ys ->
        let isInf = case xs of VStream _ -> True; _ -> False
            err = zeroV a -- default for out-of-bounds accesses
        in atV_list (isTBit a) isInf err (fromSeq xs) ys)

  , ("!"           , -- {n,a,i} (fin n, fin i) => [n]a -> [i] -> a
      tlam $ \_ ->
      tlam $ \a ->
      tlam $ \_ ->
      VFun $ \xs ->
      VFun $ \y ->
        let err = zeroV a -- default for out-of-bounds accesses
            isInf = False -- type of (!) guarantess finite sequences
        in atV isInf err (reverse $ fromSeq xs) y)

  , ("!!"          , -- {n,a,m,i} (fin n, fin i) => [n]a -> [m][i] -> [m]a
      tlam $ \_ ->
      tlam $ \a ->
      tlam $ \_ ->
      tlam $ \_ ->
      VFun $ \xs ->
      VFun $ \ys ->
        let err = zeroV a -- default for out-of-bounds accesses
            isInf = False -- type of (!!) guarantess finite sequences
        in atV_list (isTBit a) isInf err (reverse $ fromSeq xs) ys)

  , ("fromThen"    , fromThenV)
  , ("fromTo"      , fromToV)
  , ("fromThenTo"  , fromThenToV)

  , ("infFrom"     ,
      tlam $ \(finTValue -> bits)  ->
       lam $ \(fromVWord  -> first) ->
      toStream [ VWord (SBV.svPlus first (literalSWord (fromInteger bits) i)) | i <- [0 ..] ])

  , ("infFromThen" , -- {a} (fin a) => [a] -> [a] -> [inf][a]
      tlam $ \_ ->
       lam $ \(fromVWord -> first) ->
       lam $ \(fromVWord -> next) ->
      toStream (map VWord (iterate (SBV.svPlus (SBV.svMinus next first)) first)))

    -- {at,len} (fin len) => [len][8] -> at
  , ("error"       ,
      tlam $ \at ->
      tlam $ \(finTValue -> _len) ->
      VFun $ \_msg -> zeroV at) -- error/undefined, is arbitrarily translated to 0

  , ("pmult"       , -- {a,b} (fin a, fin b) => [a] -> [b] -> [max 1 (a + b) - 1]
      tlam $ \(finTValue -> i) ->
      tlam $ \(finTValue -> j) ->
      VFun $ \v1 ->
      VFun $ \v2 ->
        let k = max 1 (i + j) - 1
            mul _  []     ps = ps
            mul as (b:bs) ps = mul (SBV.svFalse : as) bs (ites b (as `addPoly` ps) ps)
            xs = map fromVBit (fromSeq v1)
            ys = map fromVBit (fromSeq v2)
            zs = take (fromInteger k) (mul xs ys [] ++ repeat SBV.svFalse)
        in VSeq True (map VBit zs))

  , ("pdiv"        , -- {a,b} (fin a, fin b) => [a] -> [b] -> [a]
      tlam $ \(finTValue -> i) ->
      tlam $ \_ ->
      VFun $ \v1 ->
      VFun $ \v2 ->
        let xs = map fromVBit (fromSeq v1)
            ys = map fromVBit (fromSeq v2)
            zs = take (fromInteger i) (fst (mdp (reverse xs) (reverse ys)) ++ repeat SBV.svFalse)
        in VSeq True (map VBit (reverse zs)))

  , ("pmod"        , -- {a,b} (fin a, fin b) => [a] -> [b+1] -> [b]
      tlam $ \_ ->
      tlam $ \(finTValue -> j) ->
      VFun $ \v1 ->
      VFun $ \v2 ->
        let xs = map fromVBit (fromSeq v1)
            ys = map fromVBit (fromSeq v2)
            zs = take (fromInteger j) (snd (mdp (reverse xs) (reverse ys)) ++ repeat SBV.svFalse)
        in VSeq True (map VBit (reverse zs)))

  , ("random"      , panic "Cryptol.Symbolic.Prims.evalECon"
                       [ "can't symbolically evaluae ECRandom" ])
  ]
-}

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

{-
asWordList :: [Value] -> Maybe [SWord]
asWordList = go id
 where go :: ([SWord] -> [SWord]) -> [Value] -> Maybe [SWord]
       go f [] = Just (f [])
       go f (VWord x:vs)      = go (f . (x:)) vs
       go f (VSeq True bs:vs) = go (f . (x:)) vs
              where x = packWord $ map fromVBit bs
       go _ _ = Nothing

atV_list :: Bool -- Are the elements of the resulting sequence bits?
         -> Bool -- Is this an infinite sequence?
         -> Value -- default value
         -> [Value] -- values to select
         -> Value   -- index
         -> Value

-- Use SBV selection primitives if possible
-- NB: only examine the list if it is finite
atV_list isBit False def (asWordList -> Just ws) v =
  case v of
    VSeq _ ys ->
      VSeq isBit $ map (VWord . SBV.svSelect ws (fromVWord def) . fromVWord) ys
    VStream ys ->
      VStream $ map (VWord . SBV.svSelect ws (fromVWord def) . fromVWord) ys
    _ -> panic "Cryptol.Symbolic.Prims.atV_list" [ "non-mappable value" ]

atV_list isBit _ def xs v =
  case v of
    VSeq _  ys ->
      VSeq isBit $ map (iteAtV def xs) ys
    VStream ys ->
      VStream $ map (iteAtV def xs) ys
    _ -> panic "Cryptol.Symbolic.Prims.atV_list" [ "non-mappable value" ]


atV :: Bool -- Is this an infinite sequence?
    -> Value -- default value
    -> [Value] -- values to select
    -> Value   -- index
    -> Value

-- When applicable, use the SBV selection operation
-- NB: only examine the list if it is finite
atV False def (asWordList -> Just ws) i =
  VWord $ SBV.svSelect ws (fromVWord def) (fromVWord i)

-- Otherwise, decompose into a sequence of if/then/else operations
atV _ def vs i = iteAtV def vs i

-- Select a value at an index by building a sequence of if/then/else operations
iteAtV :: Value -> [Value] -> Value -> Value
iteAtV def vs i =
  case i of
    VSeq True (map fromVBit -> bits) -> -- index bits in big-endian order
      case foldr weave vs bits of
        [] -> def
        y : _ -> y
    VWord x -> foldr f def (zip [0 .. 2 ^ SBV.intSizeOf x - 1] vs)
      where
        k = SBV.kindOf x
        f (n, v) y = iteValue (SBV.svEqual x (SBV.svInteger k n)) v y
    _ -> evalPanic "Cryptol.Symbolic.Prims.selectV" ["Invalid index argument"]
  where
    weave :: SBool -> [Value] -> [Value]
    weave _ [] = []
    weave b [x1] = [iteValue b def x1]
    weave b (x1 : x2 : xs) = iteValue b x2 x1 : weave b xs



replicateV :: Integer -- ^ number of elements
           -> TValue  -- ^ type of element
           -> Value   -- ^ element
           -> Value
replicateV n (toTypeVal -> TVBit) x = VSeq True  (genericReplicate n x)
replicateV n _                    x = VSeq False (genericReplicate n x)

nth :: a -> [a] -> Int -> a
nth def [] _ = def
nth def (x : xs) n
  | n == 0    = x
  | otherwise = nth def xs (n - 1)

nthV :: Value -> Value -> Integer -> Value
nthV err v n =
  case v of
    VStream xs -> nth err xs (fromInteger n)
    VSeq _ xs  -> nth err xs (fromInteger n)
    VWord x                 -> let i = SBV.intSizeOf x - 1 - fromInteger n
                               in if i < 0 then err else
                                    VBit (SBV.svTestBit x i)
    _                       -> err

mapV :: Bool -> (Value -> Value) -> Value -> Value
mapV isBit f v =
  case v of
    VSeq _ xs  -> VSeq isBit (map f xs)
    VStream xs -> VStream (map f xs)
    _          -> panic "Cryptol.Symbolic.Prims.mapV" [ "non-mappable value" ]

catV :: Value -> Value -> Value
catV xs          (VStream ys) = VStream (fromSeq xs ++ ys)
catV (VWord x)   ys           = VWord (SBV.svJoin x (fromVWord ys))
catV xs          (VWord y)    = VWord (SBV.svJoin (fromVWord xs) y)
catV (VSeq b xs) (VSeq _ ys)  = VSeq b (xs ++ ys)
catV _ _ = panic "Cryptol.Symbolic.Prims.catV" [ "non-concatenable value" ]

dropV :: Integer -> Value -> Value
dropV 0 xs = xs
dropV n xs =
  case xs of
    VSeq b xs'  -> VSeq b (genericDrop n xs')
    VStream xs' -> VStream (genericDrop n xs')
    VWord w     -> VWord $ SBV.svExtract (SBV.intSizeOf w - 1 - fromInteger n) 0 w
    _           -> panic "Cryptol.Symbolic.Prims.dropV" [ "non-droppable value" ]

takeV :: Integer -> Value -> Value
takeV n xs =
  case xs of
    VWord w     -> VWord $ SBV.svExtract (SBV.intSizeOf w - 1) (SBV.intSizeOf w - fromInteger n) w
    VSeq b xs'  -> VSeq b (genericTake n xs')
    VStream xs' -> VSeq b (genericTake n xs')
                     where b = case xs' of VBit _ : _ -> True
                                           _          -> False
    _           -> panic "Cryptol.Symbolic.Prims.takeV" [ "non-takeable value" ]
-}

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

-- Arith -----------------------------------------------------------------------

type Binary = TValue -> Value -> Value -> Eval Value
type Unary = TValue -> Value -> Eval Value

-- | Models functions of type `{a} (Arith a) => a -> a -> a`
arithBinary :: (SWord -> SWord -> SWord) -> Binary
arithBinary op = loop . toTypeVal
  where
    loop ty l r =
      case ty of
        TVBit         -> evalPanic "arithBinop" ["Invalid arguments"]
        TVSeq _ TVBit -> VWord (op (fromVWord l) (fromVWord r))
        TVSeq _ t     -> VSeq False (zipWith (loop t) (fromSeq l) (fromSeq r))
        TVStream t    -> VStream (zipWith (loop t) (fromSeq l) (fromSeq r))
        TVTuple ts    -> VTuple (zipWith3 loop ts (fromVTuple l) (fromVTuple r))
        TVRecord fs   -> VRecord [ (f, loop t (lookupRecord f l) (lookupRecord f r)) | (f, t) <- fs ]
        TVFun _ t     -> VFun (\x -> loop t (fromVFun l x) (fromVFun r x))

-- | Models functions of type `{a} (Arith a) => a -> a`
arithUnary :: (SWord -> SWord) -> Unary
arithUnary op = loop . toTypeVal
  where
    loop ty v =
      case ty of
        TVBit         -> evalPanic "arithUnary" ["Invalid arguments"]
        TVSeq _ TVBit -> VWord (op (fromVWord v))
        TVSeq _ t     -> VSeq False (map (loop t) (fromSeq v))
        TVStream t    -> VStream (map (loop t) (fromSeq v))
        TVTuple ts    -> VTuple (zipWith loop ts (fromVTuple v))
        TVRecord fs   -> VRecord [ (f, loop t (lookupRecord f v)) | (f, t) <- fs ]
        TVFun _ t     -> VFun (\x -> loop t (fromVFun v x))
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

{-
-- Logic -----------------------------------------------------------------------

errorV :: String -> TValue -> Value
errorV msg = go . toTypeVal
  where
    go ty =
      case ty of
        TVBit         -> VBit (error msg)
        TVSeq n t     -> VSeq False (replicate n (go t))
        TVStream t    -> VStream (repeat (go t))
        TVTuple ts    -> VTuple [ go t | t <- ts ]
        TVRecord fs   -> VRecord [ (n, go t) | (n, t) <- fs ]
        TVFun _ t     -> VFun (const (go t))

zeroV :: TValue -> Value
zeroV = go . toTypeVal
  where
    go ty =
      case ty of
        TVBit         -> VBit SBV.svFalse
        TVSeq n TVBit -> VWord (literalSWord n 0)
        TVSeq n t     -> VSeq False (replicate n (go t))
        TVStream t    -> VStream (repeat (go t))
        TVTuple ts    -> VTuple [ go t | t <- ts ]
        TVRecord fs   -> VRecord [ (n, go t) | (n, t) <- fs ]
        TVFun _ t     -> VFun (const (go t))

-- | Join a sequence of sequences into a single sequence.
joinV :: TValue -> TValue -> TValue -> Value -> Value
joinV parts each a v =
  let len = toNumTValue (numTValue parts `nMul` numTValue each)
  in toSeq len a (concatMap fromSeq (fromSeq v))

-- | Split implementation.
ecSplitV :: Value
ecSplitV =
  tlam $ \ parts ->
  tlam $ \ each  ->
  tlam $ \ a     ->
  lam  $ \ v     ->
  let mkChunks f = map (toFinSeq a) $ f $ fromSeq v
  in case (numTValue parts, numTValue each) of
       (Nat p, Nat e) -> VSeq False $ mkChunks (finChunksOf p e)
       (Inf  , Nat e) -> toStream   $ mkChunks (infChunksOf e)
       _              -> evalPanic "splitV" ["invalid type arguments to split"]

-- | Split into infinitely many chunks
infChunksOf :: Integer -> [a] -> [[a]]
infChunksOf each xs = let (as,bs) = genericSplitAt each xs
                      in as : infChunksOf each bs

-- | Split into finitely many chunks
finChunksOf :: Integer -> Integer -> [a] -> [[a]]
finChunksOf 0 _ _ = []
finChunksOf parts each xs = let (as,bs) = genericSplitAt each xs
                            in as : finChunksOf (parts - 1) each bs

-- | Merge two values given a binop.  This is used for and, or and xor.
logicBinary :: (SBool -> SBool -> SBool) -> (SWord -> SWord -> SWord) -> Binary
logicBinary bop op = loop . toTypeVal
  where
    loop ty l r =
      case ty of
        TVBit         -> VBit (bop (fromVBit l) (fromVBit r))
        TVSeq _ TVBit -> VWord (op (fromVWord l) (fromVWord r))
        TVSeq _ t     -> VSeq False (zipWith (loop t) (fromSeq l) (fromSeq r))
        TVStream t    -> VStream (zipWith (loop t) (fromSeq l) (fromSeq r))
        TVTuple ts    -> VTuple (zipWith3 loop ts (fromVTuple l) (fromVTuple r))
        TVRecord fs   -> VRecord [ (f, loop t (lookupRecord f l) (lookupRecord f r)) | (f, t) <- fs ]
        TVFun _ t     -> VFun (\x -> loop t (fromVFun l x) (fromVFun r x))

logicUnary :: (SBool -> SBool) -> (SWord -> SWord) -> Unary
logicUnary bop op = loop . toTypeVal
  where
    loop ty v =
      case ty of
        TVBit         -> VBit (bop (fromVBit v))
        TVSeq _ TVBit -> VWord (op (fromVWord v))
        TVSeq _ t     -> VSeq False (map (loop t) (fromSeq v))
        TVStream t    -> VStream (map (loop t) (fromSeq v))
        TVTuple ts    -> VTuple (zipWith loop ts (fromVTuple v))
        TVRecord fs   -> VRecord [ (f, loop t (lookupRecord f v)) | (f, t) <- fs ]
        TVFun _ t     -> VFun (\x -> loop t (fromVFun v x))

-- @[ 0, 1 .. ]@
fromThenV :: Value
fromThenV  =
  tlamN $ \ first ->
  tlamN $ \ next  ->
  tlamN $ \ bits  ->
  tlamN $ \ len   ->
    case (first, next, len, bits) of
      (Nat first', Nat next', Nat len', Nat bits') ->
        let nums = enumFromThen first' next'
            lit i = VWord (literalSWord (fromInteger bits') i)
         in VSeq False (genericTake len' (map lit nums))
      _ -> evalPanic "fromThenV" ["invalid arguments"]

-- @[ 0 .. 10 ]@
fromToV :: Value
fromToV  =
  tlamN $ \ first ->
  tlamN $ \ lst   ->
  tlamN $ \ bits  ->
    case (first, lst, bits) of

      (Nat first', Nat lst', Nat bits') ->
        let nums = enumFromThenTo first' (first' + 1) lst'
            len  = 1 + (lst' - first')
            lit i = VWord (literalSWord (fromInteger bits') i)
         in VSeq False (genericTake len (map lit nums))

      _ -> evalPanic "fromThenV" ["invalid arguments"]

-- @[ 0, 1 .. 10 ]@
fromThenToV :: Value
fromThenToV  =
  tlamN $ \ first ->
  tlamN $ \ next  ->
  tlamN $ \ lst   ->
  tlamN $ \ bits  ->
  tlamN $ \ len   ->
    case (first, next, lst, len, bits) of

      (Nat first', Nat next', Nat lst', Nat len', Nat bits') ->
        let nums = enumFromThenTo first' next' lst'
            lit i = VWord (literalSWord (fromInteger bits') i)
         in VSeq False (genericTake len' (map lit nums))

      _ -> evalPanic "fromThenV" ["invalid arguments"]

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
-}
