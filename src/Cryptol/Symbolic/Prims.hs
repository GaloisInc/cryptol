-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
module Cryptol.Symbolic.Prims where

import Control.Applicative
import Data.Bits
import Data.List (genericDrop, genericReplicate, genericSplitAt, genericTake, transpose)

import Cryptol.Prims.Eval (binary, unary, tlamN)
import Cryptol.Prims.Syntax (ECon(..))
import Cryptol.Symbolic.BitVector
import Cryptol.Symbolic.Value
import Cryptol.TypeCheck.AST (Name)
import Cryptol.TypeCheck.Solver.InfNat(Nat'(..), nMul)
import Cryptol.Utils.Panic

import qualified Data.SBV as SBV
import Data.SBV (SBool)
import qualified Data.SBV.Tools.Polynomial as Poly

traverseSnd :: Functor f => (a -> f b) -> (t, a) -> f (t, b)
traverseSnd f (x, y) = (,) x <$> f y

-- Primitives ------------------------------------------------------------------

-- See also Cryptol.Prims.Eval.evalECon
evalECon :: ECon -> Value
evalECon econ =
  case econ of
    ECTrue        -> VBit SBV.true
    ECFalse       -> VBit SBV.false
    ECDemote      -> ecDemoteV -- Converts a numeric type into its corresponding value.
                               -- { val, bits } (fin val, fin bits, bits >= width val) => [bits]
    ECPlus        -> binary (arithBinary (+)) -- {a} (Arith a) => a -> a -> a
    ECMinus       -> binary (arithBinary (-)) -- {a} (Arith a) => a -> a -> a
    ECMul         -> binary (arithBinary (*)) -- {a} (Arith a) => a -> a -> a
    ECDiv         -> binary (arithBinary (SBV.sQuot)) -- {a} (Arith a) => a -> a -> a
    ECMod         -> binary (arithBinary (SBV.sRem)) -- {a} (Arith a) => a -> a -> a
    ECExp         -> binary (arithBinary sExp) -- {a} (Arith a) => a -> a -> a
    ECLg2         -> unary (arithUnary sLg2) -- {a} (Arith a) => a -> a
    ECNeg         -> unary (arithUnary negate)

    ECLt          -> binary (cmpBinary cmpLt cmpLt SBV.false)
    ECGt          -> binary (cmpBinary cmpGt cmpGt SBV.false)
    ECLtEq        -> binary (cmpBinary cmpLtEq cmpLtEq SBV.true)
    ECGtEq        -> binary (cmpBinary cmpGtEq cmpGtEq SBV.true)
    ECEq          -> binary (cmpBinary cmpEq cmpEq SBV.true)
    ECNotEq       -> binary (cmpBinary cmpNotEq cmpNotEq SBV.false)

    -- FIXME: the next 4 "primitives" should be defined in the Cryptol prelude.
    ECFunEq       -> -- {a b} (Cmp b) => (a -> b) -> (a -> b) -> a -> Bit
      -- (f === g) x = (f x == g x)
      tlam $ \_ ->
      tlam $ \b ->
      VFun $ \f ->
      VFun $ \g ->
      VFun $ \x -> cmpBinary cmpEq cmpEq SBV.true b (fromVFun f x) (fromVFun g x)

    ECFunNotEq    -> -- {a b} (Cmp b) => (a -> b) -> (a -> b) -> a -> Bit
      -- (f !== g) x = (f x != g x)
      tlam $ \_ ->
      tlam $ \b ->
      VFun $ \f ->
      VFun $ \g ->
      VFun $ \x -> cmpBinary cmpNotEq cmpNotEq SBV.false b (fromVFun f x) (fromVFun g x)

    ECMin         -> -- {a} (Cmp a) => a -> a -> a
      -- min x y = if x <= y then x else y
      binary $ \a x y ->
        let c = cmpBinary cmpLtEq cmpLtEq SBV.false a x y
        in SBV.ite (fromVBit c) x y

    ECMax         -> -- {a} (Cmp a) => a -> a -> a
      -- max x y = if y <= x then x else y
      binary $ \a x y ->
        let c = cmpBinary cmpLtEq cmpLtEq SBV.false a y x
        in SBV.ite (fromVBit c) x y

    ECAnd         -> binary (logicBinary (SBV.&&&) (.&.))
    ECOr          -> binary (logicBinary (SBV.|||) (.|.))
    ECXor         -> binary (logicBinary (SBV.<+>) xor)
    ECCompl       -> unary (logicUnary (SBV.bnot) complement)
    ECZero        -> VPoly zeroV

    ECShiftL      -> -- {m,n,a} (fin n) => [m] a -> [n] -> [m] a
      tlam $ \m ->
      tlam $ \_ ->
      tlam $ \a ->
      VFun $ \xs ->
      VFun $ \y ->
        case xs of
          VWord x -> VWord (SBV.sbvShiftLeft x (fromWord y))
          _ -> selectV shl y
            where
              shl :: Integer -> Value
              shl i =
                case numTValue m of
                  Inf               -> dropV i xs
                  Nat j | i >= j    -> replicateV j (zeroV a)
                        | otherwise -> catV (dropV i xs) (replicateV i (zeroV a))

    ECShiftR      -> -- {m,n,a} (fin n) => [m] a -> [n] -> [m] a
      tlam $ \m ->
      tlam $ \_ ->
      tlam $ \a ->
      VFun $ \xs ->
      VFun $ \y ->
        case xs of
          VWord x -> VWord (SBV.sbvShiftRight x (fromWord y))
          _ -> selectV shr y
            where
              shr :: Integer -> Value
              shr i =
                case numTValue m of
                  Inf               -> catV (replicateV i (zeroV a)) xs
                  Nat j | i >= j    -> replicateV j (zeroV a)
                        | otherwise -> catV (replicateV i (zeroV a)) (takeV (j - i) xs)

    ECRotL        -> -- {m,n,a} (fin m, fin n) => [m] a -> [n] -> [m] a
      tlam $ \m ->
      tlam $ \_ ->
      tlam $ \_ ->
      VFun $ \xs ->
      VFun $ \y ->
        case xs of
          VWord x -> VWord (SBV.sbvRotateLeft x (fromWord y))
          _ -> selectV rol y
            where
              rol :: Integer -> Value
              rol i = catV (dropV k xs) (takeV k xs)
                where k = i `mod` finTValue m

    ECRotR        -> -- {m,n,a} (fin m, fin n) => [m] a -> [n] -> [m] a
      tlam $ \m ->
      tlam $ \_ ->
      tlam $ \_ ->
      VFun $ \xs ->
      VFun $ \y ->
        case xs of
          VWord x -> VWord (SBV.sbvRotateRight x (fromWord y))
          _ -> selectV ror y
            where
              ror :: Integer -> Value
              ror i = catV (dropV k xs) (takeV k xs)
                where k = (- i) `mod` finTValue m

    ECCat         -> -- {a,b,d} (fin a) => [a] d -> [b] d -> [a + b] d
      tlam $ \_ ->
      tlam $ \_ ->
      tlam $ \_ ->
      VFun $ \v1 ->
      VFun $ \v2 -> catV v1 v2

    ECSplitAt     -> -- {a,b,c} (fin a) => [a+b] c -> ([a]c,[b]c)
      tlam $ \(finTValue -> a) ->
      tlam $ \_ ->
      tlam $ \_ ->
      VFun $ \v -> VTuple [takeV a v, dropV a v]

    ECJoin -> tlam $ \ parts ->
              tlam $ \ each  ->
              tlam $ \ a     -> lam (joinV parts each a)

    ECSplit -> ecSplitV

    ECReverse ->
      tlam $ \a ->
      tlam $ \b ->
       lam $ \(fromSeq -> xs) -> toSeq a b (reverse xs)

    ECTranspose ->
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
             _ -> toSeq b (tvSeq a c) $ map (toSeq a c) $ transpose xs

    ECAt          -> -- {n,a,i} (fin i) => [n]a -> [i] -> a
      tlam $ \_ ->
      tlam $ \a ->
      tlam $ \_ ->
      VFun $ \xs ->
      VFun $ \y ->
        let err = zeroV a -- default for out-of-bounds accesses
        in selectV (\i -> nthV err xs i) y

    ECAtRange     -> -- {n,a,m,i} (fin i) => [n]a -> [m][i] -> [m]a
      tlam $ \_ ->
      tlam $ \a ->
      tlam $ \_ ->
      tlam $ \_ ->
      VFun $ \xs ->
      VFun $ \ys ->
        let err = zeroV a -- default for out-of-bounds accesses
        in mapV (selectV (\i -> nthV err xs i)) ys

    ECAtBack      -> -- {n,a,i} (fin n, fin i) => [n]a -> [i] -> a
      tlam $ \(finTValue -> n) ->
      tlam $ \a ->
      tlam $ \_ ->
      VFun $ \xs ->
      VFun $ \y ->
        let err = zeroV a -- default for out-of-bounds accesses
        in selectV (\i -> nthV err xs (n - 1 - i)) y

    ECAtRangeBack -> -- {n,a,m,i} (fin n, fin i) => [n]a -> [m][i] -> [m]a
      tlam $ \(finTValue -> n) ->
      tlam $ \a ->
      tlam $ \_ ->
      tlam $ \_ ->
      VFun $ \xs ->
      VFun $ \ys ->
        let err = zeroV a -- default for out-of-bounds accesses
        in mapV (selectV (\i -> nthV err xs (n - 1 - i))) ys

    ECFromThen   -> fromThenV
    ECFromTo     -> fromToV
    ECFromThenTo -> fromThenToV

    ECInfFrom    ->
      tlam $ \(finTValue -> bits)  ->
       lam $ \(fromWord  -> first) ->
      toStream [ VWord (first + SBV.literal (bv (fromInteger bits) i)) | i <- [0 ..] ]

    ECInfFromThen -> -- {a} (fin a) => [a] -> [a] -> [inf][a]
      tlam $ \_ ->
       lam $ \(fromWord -> first) ->
       lam $ \(fromWord -> next) ->
      toStream (map VWord (iterate (+ (next - first)) first))

    -- {at,len} (fin len) => [len][8] -> at
    ECError ->
      tlam $ \at ->
      tlam $ \(finTValue -> _len) ->
      VFun $ \_msg -> zeroV at -- error/undefined, is arbitrarily translated to 0

    ECPMul        -> -- {a,b} (fin a, fin b) => [a] -> [b] -> [max 1 (a + b) - 1]
      tlam $ \(finTValue -> i) ->
      tlam $ \(finTValue -> j) ->
      VFun $ \v1 ->
      VFun $ \v2 ->
        let k = max 1 (i + j) - 1
            mul _  []     ps = ps
            mul as (b:bs) ps = mul (SBV.false : as) bs (Poly.ites b (as `Poly.addPoly` ps) ps)
            xs = map fromVBit (fromSeq v1)
            ys = map fromVBit (fromSeq v2)
            zs = take (fromInteger k) (mul xs ys [] ++ repeat SBV.false)
        in VSeq True (map VBit zs)

    ECPDiv        -> -- {a,b} (fin a, fin b) => [a] -> [b] -> [a]
      tlam $ \(finTValue -> i) ->
      tlam $ \_ ->
      VFun $ \v1 ->
      VFun $ \v2 ->
        let xs = map fromVBit (fromSeq v1)
            ys = map fromVBit (fromSeq v2)
            zs = take (fromInteger i) (fst (Poly.mdp (reverse xs) (reverse ys)) ++ repeat SBV.false)
        in VSeq True (map VBit (reverse zs))

    ECPMod        -> -- {a,b} (fin a, fin b) => [a] -> [b+1] -> [b]
      tlam $ \_ ->
      tlam $ \(finTValue -> j) ->
      VFun $ \v1 ->
      VFun $ \v2 ->
        let xs = map fromVBit (fromSeq v1)
            ys = map fromVBit (fromSeq v2)
            zs = take (fromInteger j) (snd (Poly.mdp (reverse xs) (reverse ys)) ++ repeat SBV.false)
        in VSeq True (map VBit (reverse zs))

    ECRandom      -> panic "Cryptol.Symbolic.Prims.evalECon"
                       [ "can't symbolically evaluae ECRandom" ]


selectV :: (Integer -> Value) -> Value -> Value
selectV f v = sel 0 bits
  where
    bits = map fromVBit (fromSeq v) -- index bits in big-endian order

    sel :: Integer -> [SBool] -> Value
    sel offset []       = f offset
    sel offset (b : bs) = SBV.ite b m1 m2
      where m1 = sel (offset + 2 ^ length bs) bs
            m2 = sel offset bs

replicateV :: Integer -> Value -> Value
replicateV n x = VSeq False (genericReplicate n x)

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
    VWord x                 -> let i = bitSize x - 1 - fromInteger n
                               in if i < 0 then err else
                                    VBit (SBV.sbvTestBit x i)
    _                       -> err

mapV :: (Value -> Value) -> Value -> Value
mapV f v =
  case v of
    VSeq b xs  -> VSeq b (map f xs)
    VStream xs -> VStream (map f xs)
    _          -> panic "Cryptol.Symbolic.Prims.mapV" [ "non-mappable value" ]

catV :: Value -> Value -> Value
catV xs          (VStream ys) = VStream (fromSeq xs ++ ys)
catV (VWord x)   ys           = VWord (cat x (fromWord ys))
catV xs          (VWord y)    = VWord (cat (fromWord xs) y)
catV (VSeq b xs) (VSeq _ ys)  = VSeq b (xs ++ ys)
catV _ _ = panic "Cryptol.Symbolic.Prims.catV" [ "non-concatenable value" ]

dropV :: Integer -> Value -> Value
dropV 0 xs = xs
dropV n xs =
  case xs of
    VSeq b xs'  -> VSeq b (genericDrop n xs')
    VStream xs' -> VStream (genericDrop n xs')
    VWord w     -> VWord $ extract (bitSize w - 1 - fromInteger n) 0 w
    _           -> panic "Cryptol.Symbolic.Prims.dropV" [ "non-droppable value" ]

takeV :: Integer -> Value -> Value
takeV n xs =
  case xs of
    VWord w     -> VWord $ extract (bitSize w - 1) (bitSize w - fromInteger n) w
    VSeq b xs'  -> VSeq b (genericTake n xs')
    VStream xs' -> VSeq b (genericTake n xs')
                     where b = case xs' of VBit _ : _ -> True
                                           _          -> False
    _           -> panic "Cryptol.Symbolic.Prims.takeV" [ "non-takeable value" ]

-- | Make a numeric constant.
-- { val, bits } (fin val, fin bits, bits >= width val) => [bits]
ecDemoteV :: Value
ecDemoteV = tlam $ \valT ->
            tlam $ \bitT ->
            case (numTValue valT, numTValue bitT) of
              (Nat v, Nat bs) -> VWord (SBV.literal (bv (fromInteger bs) v))
              _ -> evalPanic "Cryptol.Prove.evalECon"
                       ["Unexpected Inf in constant."
                       , show valT
                       , show bitT
                       ]

-- Type Values -----------------------------------------------------------------

-- | An easy-to-use alternative representation for type `TValue`.
data TypeVal
  = TVBit
  | TVSeq Int TypeVal
  | TVStream TypeVal
  | TVTuple [TypeVal]
  | TVRecord [(Name, TypeVal)]
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

type Binary = TValue -> Value -> Value -> Value
type Unary = TValue -> Value -> Value

-- | Models functions of type `{a} (Arith a) => a -> a -> a`
arithBinary :: (SWord -> SWord -> SWord) -> Binary
arithBinary op = loop . toTypeVal
  where
    loop ty l r =
      case ty of
        TVBit         -> evalPanic "arithBinop" ["Invalid arguments"]
        TVSeq _ TVBit -> VWord (op (fromWord l) (fromWord r))
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
        TVSeq _ TVBit -> VWord (op (fromWord v))
        TVSeq _ t     -> VSeq False (map (loop t) (fromSeq v))
        TVStream t    -> VStream (map (loop t) (fromSeq v))
        TVTuple ts    -> VTuple (zipWith loop ts (fromVTuple v))
        TVRecord fs   -> VRecord [ (f, loop t (lookupRecord f v)) | (f, t) <- fs ]
        TVFun _ t     -> VFun (\x -> loop t (fromVFun v x))

sExp :: SWord -> SWord -> SWord
sExp x y = go (SBV.blastLE y)
  where go []       = SBV.literal (bv (bitSize x) 1)
        go (b : bs) = SBV.ite b (x * s) s
            where a = go bs
                  s = a * a

-- | Ceiling (log_2 x)
sLg2 :: SWord -> SWord
sLg2 x = go 0
  where
    lit n = SBV.literal (bv (bitSize x) n)
    go i | i < bitSize x = SBV.ite ((SBV..<=) x (lit (2^i))) (lit (toInteger i)) (go (i + 1))
         | otherwise     = lit (toInteger i)

-- Cmp -------------------------------------------------------------------------

cmpValue :: (SBool -> SBool -> a -> a)
         -> (SWord -> SWord -> a -> a)
         -> (Value -> Value -> a -> a)
cmpValue fb fw = cmp
  where
    cmp v1 v2 k =
      case (v1, v2) of
        (VRecord fs1, VRecord fs2) -> cmpValues (map snd fs1) (map snd fs2) k
        (VTuple vs1 , VTuple vs2 ) -> cmpValues vs1 vs2 k
        (VBit b1    , VBit b2    ) -> fb b1 b2 k
        (VWord w1   , VWord w2   ) -> fw w1 w2 k
        (VSeq _ vs1 , VSeq _ vs2 ) -> cmpValues vs1 vs2 k
        (VStream {} , VStream {} ) -> panic "Cryptol.Symbolic.Prims.cmpValue"
                                        [ "Infinite streams are not comparable" ]
        (VFun {}    , VFun {}    ) -> panic "Cryptol.Symbolic.Prims.cmpValue"
                                        [ "Functions are not comparable" ]
        (VPoly {}   , VPoly {}   ) -> panic "Cryptol.Symbolic.Prims.cmpValue"
                                        [ "Polymorphic values are not comparable" ]
        (VWord w1   , _          ) -> fw w1 (fromWord v2) k
        (_          , VWord w2   ) -> fw (fromWord v1) w2 k
        (_          , _          ) -> panic "Cryptol.Symbolic.Prims.cmpValue"
                                        [ "type mismatch" ]

    cmpValues (x1 : xs1) (x2 : xs2) k = cmp x1 x2 (cmpValues xs1 xs2 k)
    cmpValues _ _ k = k

cmpEq :: SBV.EqSymbolic a => a -> a -> SBool -> SBool
cmpEq x y k = (SBV.&&&) ((SBV..==) x y) k

cmpNotEq :: SBV.EqSymbolic a => a -> a -> SBool -> SBool
cmpNotEq x y k = (SBV.|||) ((SBV../=) x y) k

cmpLt, cmpGt :: SBV.OrdSymbolic a => a -> a -> SBool -> SBool
cmpLt x y k = (SBV.|||) ((SBV..<) x y) (cmpEq x y k)
cmpGt x y k = (SBV.|||) ((SBV..>) x y) (cmpEq x y k)

cmpLtEq, cmpGtEq :: SBV.OrdSymbolic a => a -> a -> SBool -> SBool
cmpLtEq x y k = (SBV.&&&) ((SBV..<=) x y) (cmpNotEq x y k)
cmpGtEq x y k = (SBV.&&&) ((SBV..>=) x y) (cmpNotEq x y k)

cmpBinary :: (SBool -> SBool -> SBool -> SBool)
          -> (SWord -> SWord -> SBool -> SBool)
          -> SBool -> Binary
cmpBinary fb fw b _ty v1 v2 = VBit (cmpValue fb fw v1 v2 b)


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
        TVBit         -> VBit SBV.false
        TVSeq n TVBit -> VWord (SBV.literal (bv n 0))
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
        TVSeq _ TVBit -> VWord (op (fromWord l) (fromWord r))
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
        TVSeq _ TVBit -> VWord (op (fromWord v))
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
            lit i = VWord (SBV.literal (bv (fromInteger bits') i))
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
            lit i = VWord (SBV.literal (bv (fromInteger bits') i))
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
            lit i = VWord (SBV.literal (bv (fromInteger bits') i))
         in VSeq False (genericTake len' (map lit nums))

      _ -> evalPanic "fromThenV" ["invalid arguments"]
