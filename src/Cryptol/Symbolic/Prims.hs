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

import Cryptol.Eval.Value (TValue, numTValue, finTValue, isTSeq, isTBit, isTFun, isTTuple, isTRec)
import Cryptol.Prims.Syntax (ECon(..))
import Cryptol.Symbolic.BitVector
import Cryptol.Symbolic.Value
import Cryptol.TypeCheck.AST (Name)
import Cryptol.TypeCheck.Solver.InfNat(Nat'(..))

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
      VFun $ \x -> cmpBinary cmpEq cmpEq SBV.true b (vApply f x) (vApply g x)

    ECFunNotEq    -> -- {a b} (Cmp b) => (a -> b) -> (a -> b) -> a -> Bit
      -- (f !== g) x = (f x != g x)
      tlam $ \_ ->
      tlam $ \b ->
      VFun $ \f ->
      VFun $ \g ->
      VFun $ \x -> cmpBinary cmpNotEq cmpNotEq SBV.false b (vApply f x) (vApply g x)

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

    ECJoin        -> -- {a,b,c} (fin b) => [a][b]c -> [a * b]c
      tlam $ \a ->
      tlam $ \_ ->
      tlam $ \c ->
      VFun $ \v ->
        if not (numTValue a == Inf && isTBit c) then go v else go (mapV (vSeq . fromSeq) v)
          -- avoid concatenating infinitely many VWords
        where
          go :: Value -> Value
          go xss = do
            case xss of
              VNil          -> VNil
              VCons xs xss' -> catV xs (go xss')
              _             -> error "join"

    ECSplit       -> -- {a,b,c} (fin b) => [a * b] c -> [a][b] c
      tlam $ \(numTValue -> a) ->
      tlam $ \(finTValue -> b) ->
      tlam $ \_ ->
      VFun $ \v ->
        let go :: Nat' -> Value -> Value
            go t xs =
              case dec t of
                Nothing -> VNil
                Just t' -> VCons (takeV b xs) (go t' (dropV b xs))
        in go a v

    ECReverse     -> -- {a,b} (fin a) => [a] b -> [a] b
      tlam $ \_ ->
      tlam $ \_ ->
      VFun $ \v -> vSeq (reverse (fromSeq v))

    ECTranspose   -> -- {a,b,c} [a][b]c -> [b][a]c
      tlam $ \_a ->
      tlam $ \b ->
      tlam $ \_c ->
      VFun $ \v -> transp (numTValue b) v
        where
          hd :: Value -> Value
          hd = fst . fromVCons
          tl :: Value -> Value
          tl = snd . fromVCons
          transp :: Nat' -> Value -> Value
          transp t xss =
            case dec t of
              Nothing -> VNil
              Just t' -> VCons (mapV hd xss) (transp t' (mapV tl xss))

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

    ECFromThen    -> -- {first, next, bits, len} (...) => [len][bits]
      tlam $ \first ->
      tlam $ \next ->
      tlam $ \bits ->
      VPoly $ \len ->
        let w = fromInteger (finTValue bits)
            delta = finTValue next - finTValue first
            lit i = VWord (SBV.literal (bv w i))
            go :: Integer -> Integer -> Value
            go 0 _ = VNil
            go n i = VCons (lit i) (go (n - 1) (i + delta))
        in go (finTValue len) (finTValue first)

    ECFromTo      -> -- {first, last, bits} (...) => [1 + (last - first)][bits]
      tlam $ \first ->
      tlam $ \lst ->
      VPoly $ \bits ->
        let w = fromInteger (finTValue bits)
            lit i = VWord (SBV.literal (bv w i))
            go :: Integer -> Integer -> Value
            go 0 _ = VNil
            go n i = VCons (lit i) (go (n - 1) (i + 1))
        in go (finTValue lst - finTValue first + 1) (finTValue first)

    ECFromThenTo  -> -- {first, next, last, bits, len} (...) => [len][bits]
      tlam $ \first ->
      tlam $ \next ->
      tlam $ \_lst ->
      tlam $ \bits ->
      VPoly $ \len ->
        let w = fromInteger (finTValue bits)
            delta = finTValue next - finTValue first
            lit i = VWord (SBV.literal (bv w i))
            go :: Integer -> Integer -> Value
            go 0 _ = VNil
            go n i = VCons (lit i) (go (n - 1) (i + delta))
        in go (finTValue len) (finTValue first)

    ECInfFrom     -> -- {a} (fin a) => [a] -> [inf][a]
      tlam $ \(finTValue -> a) ->
      VFun $ \(fromWord -> x0) ->
        let delta = SBV.literal (bv (fromInteger a) 1)
            from x = VCons (VWord x) (from (x + delta))
        in from x0

    ECInfFromThen -> -- {a} (fin a) => [a] -> [a] -> [inf][a]
      tlam $ \_ ->
      VFun $ \(fromWord -> x1) ->
      VFun $ \(fromWord -> x2) ->
        let delta = x2 - x1
            from x = VCons (VWord x) (from (x + delta))
        in from x1

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
        in vSeq (map VBit zs)

    ECPDiv        -> -- {a,b} (fin a, fin b) => [a] -> [b] -> [a]
      tlam $ \(finTValue -> i) ->
      tlam $ \_ ->
      VFun $ \v1 ->
      VFun $ \v2 ->
        let xs = map fromVBit (fromSeq v1)
            ys = map fromVBit (fromSeq v2)
            zs = take (fromInteger i) (fst (Poly.mdp (reverse xs) (reverse ys)) ++ repeat SBV.false)
        in vSeq (map VBit (reverse zs))

    ECPMod        -> -- {a,b} (fin a, fin b) => [a] -> [b+1] -> [b]
      tlam $ \_ ->
      tlam $ \(finTValue -> j) ->
      VFun $ \v1 ->
      VFun $ \v2 ->
        let xs = map fromVBit (fromSeq v1)
            ys = map fromVBit (fromSeq v2)
            zs = take (fromInteger j) (snd (Poly.mdp (reverse xs) (reverse ys)) ++ repeat SBV.false)
        in vSeq (map VBit (reverse zs))

    ECRandom      -> error "ECRandom"

dec :: Nat' -> Maybe Nat'
dec (Nat 0) = Nothing
dec (Nat n) = Just (Nat (n - 1))
dec Inf     = Just Inf

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
replicateV n x = go n
  where go 0 = VNil
        go i = VCons x (go (i - 1))

nthV :: Value -> Value -> Integer -> Value
nthV err xs n =
  case xs of
    VCons x xs' | n == 0    -> x
                | otherwise -> nthV err xs' (n - 1)
    VWord x                 -> let i = bitSize x - 1 - fromInteger n
                               in if i < 0 then err else
                                    VBit (SBV.sbvTestBit x i)
    _                       -> err

mapV :: (Value -> Value) -> Value -> Value
mapV f v = do
  case v of
    VNil       -> VNil
    VCons x xs -> VCons (f x) (mapV f xs)
    _          -> error "mapV"

catV :: Value -> Value -> Value
catV xs ys = do
  case xs of
    VCons x xs' -> VCons x (catV xs' ys)
    VNil        -> ys
    VWord x     -> VWord (cat x (fromWord ys))
    _           -> error "catV"

dropV :: Integer -> Value -> Value
dropV 0 xs = xs
dropV n xs =
  case xs of
    VCons _ xs' -> dropV (n - 1) xs'
    VNil        -> VNil
    VWord w     -> VWord $ extract (bitSize w - 1 - fromInteger n) 0 w
    _           -> error "dropV"

takeV :: Integer -> Value -> Value
takeV 0 _ = VNil
takeV n xs =
  case xs of
    VWord w     -> VWord $ extract (bitSize w - 1) (bitSize w - fromInteger n) w
    VCons x xs' -> VCons x (takeV (n - 1) xs')
    VNil        -> VNil
    _           -> error "takeV"

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


-- Operation Lifting -----------------------------------------------------------

type Binary = TValue -> Value -> Value -> Value

binary :: Binary -> Value
binary f = VPoly $ \ty ->
           VFun $ \v1 ->
           VFun $ \v2 -> f ty v1 v2

type Unary = TValue -> Value -> Value

unary :: Unary -> Value
unary f = VPoly $ \ty ->
          VFun $ \v -> f ty v

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
  | otherwise                    = error "internal error: bad TValue"

-- Arith -----------------------------------------------------------------------

-- | Models functions of type `{a} (Arith a) => a -> a -> a`
arithBinary :: (SWord -> SWord -> SWord) -> Binary
arithBinary op = loop . toTypeVal
  where
    loop ty l r =
      case ty of
        TVBit         -> evalPanic "arithBinop" ["Invalid arguments"]
        TVSeq _ TVBit -> VWord (op (fromWord l) (fromWord r))
        TVSeq 0 _     -> VNil
        TVSeq n t     -> VCons (loop t hl hr) (loop (TVSeq (n - 1) t) tl tr)
                           where (hl, tl) = fromVCons l
                                 (hr, tr) = fromVCons r
        TVStream t    -> VCons (loop t hl hr) (loop ty tl tr)
                           where (hl, tl) = fromVCons l
                                 (hr, tr) = fromVCons r
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
        TVSeq 0 _     -> VNil
        TVSeq n t     -> VCons (loop t vh) (loop (TVSeq (n - 1) t) vt)
                           where (vh, vt) = fromVCons v
        TVStream t    -> VCons (loop t vh) (loop ty vt)
                           where (vh, vt) = fromVCons v
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
        (VNil       , VNil       ) -> k
        (VCons h1 t1, VCons h2 t2) -> cmpValues [h1,t1] [h2,t2] k
        (VFun {}    , VFun {}    ) -> error "Functions are not comparable"
        (VPoly {}   , VPoly {}   ) -> error "Polymorphic values are not comparable"
        (VWord w1   , _          ) -> fw w1 (fromWord v2) k
        (_          , VWord w2   ) -> fw (fromWord v1) w2 k
        (_          , _          ) -> error "type mismatch"

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
        TVSeq n t     -> vSeq (replicate n (go t))
        TVStream t    -> let v = VCons (go t) v in v
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
        TVSeq n t     -> vSeq (replicate n (go t))
        TVStream t    -> let v = VCons (go t) v in v
        TVTuple ts    -> VTuple [ go t | t <- ts ]
        TVRecord fs   -> VRecord [ (n, go t) | (n, t) <- fs ]
        TVFun _ t     -> VFun (const (go t))

-- | Merge two values given a binop.  This is used for and, or and xor.
logicBinary :: (SBool -> SBool -> SBool) -> (SWord -> SWord -> SWord) -> Binary
logicBinary bop op = loop . toTypeVal
  where
    loop ty l r =
      case ty of
        TVBit         -> VBit (bop (fromVBit l) (fromVBit r))
        TVSeq _ TVBit -> VWord (op (fromWord l) (fromWord r))
        TVSeq 0 _     -> VNil
        TVSeq n t     -> VCons (loop t hl hr) (loop (TVSeq (n - 1) t) tl tr)
                           where (hl, tl) = fromVCons l
                                 (hr, tr) = fromVCons r
        TVStream t    -> VCons (loop t hl hr) (loop ty tl tr)
                           where (hl, tl) = fromVCons l
                                 (hr, tr) = fromVCons r
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
        TVSeq 0 _     -> VNil
        TVSeq n t     -> VCons (loop t vh) (loop (TVSeq (n - 1) t) vt)
                           where (vh, vt) = fromVCons v
        TVStream t    -> VCons (loop t vh) (loop ty vt)
                           where (vh, vt) = fromVCons v
        TVTuple ts    -> VTuple (zipWith loop ts (fromVTuple v))
        TVRecord fs   -> VRecord [ (f, loop t (lookupRecord f v)) | (f, t) <- fs ]
        TVFun _ t     -> VFun (\x -> loop t (fromVFun v x))
