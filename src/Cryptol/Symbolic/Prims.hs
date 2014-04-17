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
import Control.Monad (liftM, zipWithM)
import Data.Bits
import Data.Traversable

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

-- Symbolic if-then-else -------------------------------------------------------

ite :: SBool -> Value -> Value -> TheMonad Value
ite s v1 v2
  | Just b <- SBV.unliteral s = return $ if b then v1 else v2
  | otherwise                 = mergeValue s v1 v2

iteM :: SBool -> TheMonad Value -> TheMonad Value -> TheMonad Value
iteM s m1 m2
  | Just b <- SBV.unliteral s = if b then m1 else m2
  | otherwise                 = do v1 <- m1
                                   v2 <- m2
                                   mergeValue s v1 v2

iteThunk :: SBool -> Thunk -> Thunk -> TheMonad Thunk
iteThunk s th1 th2
  | Just b <- SBV.unliteral s = return $ if b then th1 else th2
  | otherwise                 = mergeThunk s th1 th2

mergeValue :: SBool -> Value -> Value -> TheMonad Value
mergeValue c v1 v2 =
  case (v1, v2) of
    (VRecord fs1, VRecord fs2) -> VRecord <$> zipWithM mergeField fs1 fs2
    (VTuple ts1 , VTuple ts2 ) -> VTuple <$> zipWithM (mergeThunk c) ts1 ts2
    (VBit b1    , VBit b2    ) -> return $ VBit $ SBV.symbolicMerge c b1 b2
    (VWord w1   , VWord w2   ) -> return $ VWord $ SBV.symbolicMerge c w1 w2
    (VNil       , VNil       ) -> return $ VNil
    (VCons h1 t1, VCons h2 t2) -> VCons <$> mergeThunk c h1 h2 <*> mergeThunk c t1 t2
    (VFun f1    , VFun f2    ) -> return $ VFun $ \th -> do
                                    y1 <- f1 th
                                    y2 <- f2 th
                                    mergeValue c y1 y2
    (VPoly f1   , VPoly f2   ) -> return $ VPoly $ \ty -> do
                                    y1 <- f1 ty
                                    y2 <- f2 ty
                                    mergeValue c y1 y2
    (VWord w1   , _          ) -> do w2 <- fromWord v2
                                     return $ VWord $ SBV.symbolicMerge c w1 w2
    (_          , VWord w2   ) -> do w1 <- fromWord v1
                                     return $ VWord $ SBV.symbolicMerge c w1 w2
    (_          , _          ) -> fail "merge: shape mismatch"
  where
    mergeField (n1, th1) (n2, th2)
      | n1 == n2  = (,) n1 <$> mergeThunk c th1 th2
      | otherwise = error "merge: shape mismatch"
-- ^ FIXME: allow merging of VWord/VSeq.

mergeThunk :: SBool -> Thunk -> Thunk -> TheMonad Thunk
mergeThunk c (Ready v1) (Ready v2) = Ready <$> mergeValue c v1 v2
mergeThunk c thunk1 thunk2 =
  delay $ do
    v1 <- force thunk1
    v2 <- force thunk2
    mergeValue c v1 v2

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
      VFun $ \th1 -> return $
      VFun $ \th2 -> return $
      VFun $ \th3 -> do
        VFun f <- force th1
        VFun g <- force th2
        x <- f th3
        y <- g th3
        cmpBinary cmpEq cmpEq SBV.true b x y

    ECFunNotEq    -> -- {a b} (Cmp b) => (a -> b) -> (a -> b) -> a -> Bit
      -- (f !=== g) x = (f x != g x)
      tlam $ \_ ->
      tlam $ \b ->
      VFun $ \th1 -> return $
      VFun $ \th2 -> return $
      VFun $ \th3 -> do
        VFun f <- force th1
        VFun g <- force th2
        x <- f th3
        y <- g th3
        cmpBinary cmpNotEq cmpNotEq SBV.false b x y

    ECMin         -> -- {a} (Cmp a) => a -> a -> a
      -- min x y = if x <= y then x else y
      binary $ \a x y -> do
        c <- cmpBinary cmpLtEq cmpLtEq SBV.false a x y
        ite (fromVBit c) x y

    ECMax         -> -- {a} (Cmp a) => a -> a -> a
      -- max x y = if y <= x then x else y
      binary $ \a x y -> do
        c <- cmpBinary cmpLtEq cmpLtEq SBV.false a y x
        ite (fromVBit c) x y

    ECAnd         -> binary (logicBinary (SBV.&&&) (.&.))
    ECOr          -> binary (logicBinary (SBV.|||) (.|.))
    ECXor         -> binary (logicBinary (SBV.<+>) xor)
    ECCompl       -> unary (logicUnary (SBV.bnot) complement)
    ECZero        -> VPoly zeroV

    ECShiftL      -> -- {m,n,a} (fin n) => [m] a -> [n] -> [m] a
      tlam $ \m ->
      tlam $ \_ ->
      tlam $ \a ->
      VFun $ \xs -> return $
      VFun $ \th -> do
        v <- force xs
        case v of
          VWord x -> do
            i <- fromWord =<< force th
            return $ VWord (SBV.sbvShiftLeft x i)
          _ -> do
            z <- Ready <$> zeroV a
            let shl :: Integer -> TheMonad Value
                shl i =
                  case numTValue m of
                    Inf               -> dropV i xs
                    Nat j | i >= j    -> replicateV j z
                          | otherwise -> do ys <- delay (dropV i xs)
                                            zs <- delay (replicateV i z)
                                            catV ys zs
            selectV shl th

    ECShiftR      -> -- {m,n,a} (fin n) => [m] a -> [n] -> [m] a
      tlam $ \m ->
      tlam $ \_ ->
      tlam $ \a ->
      VFun $ \xs -> return $
      VFun $ \th -> do
        v <- force xs
        case v of
          VWord x -> do
            i <- fromWord =<< force th
            return $ VWord (SBV.sbvShiftRight x i)
          _ -> do
            z <- Ready <$> zeroV a
            let shr :: Integer -> TheMonad Value
                shr i =
                  case numTValue m of
                    Inf               -> do zs <- delay (replicateV i z)
                                            catV zs xs
                    Nat j | i >= j    -> replicateV j z
                          | otherwise -> do zs <- delay (replicateV i z)
                                            ys <- delay (takeV (j - i) xs)
                                            catV zs ys
            selectV shr th

    ECRotL        -> -- {m,n,a} (fin m, fin n) => [m] a -> [n] -> [m] a
      tlam $ \m ->
      tlam $ \_ ->
      tlam $ \_ ->
      VFun $ \xs -> return $
      VFun $ \th -> do
        v <- force xs
        case v of
          VWord x -> do
            i <- fromWord =<< force th
            return $ VWord (SBV.sbvRotateLeft x i)
          _ -> do
            let rol :: Integer -> TheMonad Value
                rol i = do
                  let k = i `mod` finTValue m
                  ys <- delay (dropV k xs)
                  zs <- delay (takeV k xs)
                  catV ys zs
            selectV rol th

    ECRotR        -> -- {m,n,a} (fin m, fin n) => [m] a -> [n] -> [m] a
      tlam $ \m ->
      tlam $ \_ ->
      tlam $ \_ ->
      VFun $ \xs -> return $
      VFun $ \th -> do
        v <- force xs
        case v of
          VWord x -> do
            i <- fromWord =<< force th
            return $ VWord (SBV.sbvRotateRight x i)
          _ -> do
            let ror :: Integer -> TheMonad Value
                ror i = do
                  let k = (- i) `mod` finTValue m
                  ys <- delay (dropV k xs)
                  zs <- delay (takeV k xs)
                  catV ys zs
            selectV ror th

    ECCat         -> -- {a,b,d} (fin a) => [a] d -> [b] d -> [a + b] d
      tlam $ \_ ->
      tlam $ \_ ->
      tlam $ \_ ->
      VFun $ \th1 -> return $
      VFun $ \th2 -> catV th1 th2

    ECSplitAt     -> -- {a,b,c} (fin a) => [a+b] c -> ([a]c,[b]c)
      tlam $ \(finTValue -> a) ->
      tlam $ \_ ->
      tlam $ \_ ->
      VFun $ \th -> do
        xs <- delay (takeV a th)
        ys <- delay (dropV a th)
        return $ VTuple [xs, ys]

    ECJoin        -> -- {a,b,c} (fin b) => [a][b]c -> [a * b]c
      tlam $ \a ->
      tlam $ \_ ->
      tlam $ \c ->
      VFun $ \th -> do
        let go :: Thunk -> TheMonad Value
            go xss = do
              v <- force xss
              case v of
                VNil          -> return VNil
                VCons xs xss' -> catV xs =<< delay (go xss')
                _             -> error "join"
        if not (numTValue a == Inf && isTBit c) then go th else do
          -- avoid concatenating infinitely many VWords
          let blast x = do
                v <- force x
                bits <- fromSeq v
                return $ Ready (vSeq bits)
          go =<< delay (mapV blast th)

    ECSplit       -> -- {a,b,c} (fin b) => [a * b] c -> [a][b] c
      tlam $ \(numTValue -> a) ->
      tlam $ \(finTValue -> b) ->
      tlam $ \_ ->
      VFun $ \th -> do
        let dec (Nat 0) = Nothing
            dec (Nat n) = Just (Nat (n - 1))
            dec Inf     = Just Inf
        let go :: Nat' -> Thunk -> TheMonad Value
            go t xs =
              case dec t of
                Nothing -> return VNil
                Just t' -> do
                  ys <- delay (takeV b xs)
                  zs <- delay (dropV b xs)
                  VCons ys <$> delay (go t' zs)
        go a th

    ECReverse     -> -- {a,b} (fin a) => [a] b -> [a] b
      tlam $ \_ ->
      tlam $ \_ ->
      VFun $ \th -> do
        v <- force th
        ths <- fromSeq v
        return $ vSeq (reverse ths)

    ECTranspose   -> -- {a,b,c} [a][b]c -> [b][a]c
      tlam $ \_a ->
      tlam $ \b ->
      tlam $ \_c ->
      VFun $ \th -> do
        let hd :: Thunk -> TheMonad Thunk
            hd thunk = (fst . fromVCons) <$> force thunk
        let tl :: Thunk -> TheMonad Thunk
            tl thunk = (snd . fromVCons) <$> force thunk
        let dec (Nat 0) = Nothing
            dec (Nat n) = Just (Nat (n - 1))
            dec Inf     = Just Inf
        let transp :: Nat' -> Thunk -> TheMonad Value
            transp t xss =
              case dec t of
                Nothing -> return VNil
                Just t' -> do
                  ys <- delay (mapV hd xss)
                  yss <- delay (mapV tl xss)
                  VCons ys <$> delay (transp t' yss)
        transp (numTValue b) th

    ECAt          -> -- {n,a,m} [n]a -> [m] -> a
      tlam $ \_ ->
      tlam $ \a ->
      tlam $ \_ ->
      VFun $ \th1 -> return $
      VFun $ \th2 -> do
        err <- Ready <$> zeroV a -- default for out-of-bounds accesses
        selectV (\i -> nthV err th1 i) th2

    ECAtRange     -> -- {n,a,m,i} (fin i) => [n]a -> [m][i] -> [m]a
      tlam $ \_ ->
      tlam $ \a ->
      tlam $ \_ ->
      tlam $ \_ ->
      VFun $ \th1 -> return $
      VFun $ \th2 -> do
        err <- Ready <$> zeroV a -- default for out-of-bounds accesses
        let f :: Thunk -> TheMonad Thunk
            f th = delay (selectV (\i -> nthV err th1 i) th)
        mapV f th2

    ECAtBack      -> -- {n,a,m} (fin n) => [n]a -> [m] -> a
      tlam $ \(finTValue -> n) ->
      tlam $ \a ->
      tlam $ \_ ->
      VFun $ \th1 -> return $
      VFun $ \th2 -> do
        err <- Ready <$> zeroV a -- default for out-of-bounds accesses
        selectV (\i -> nthV err th1 (n - 1 - i)) th2

    ECAtRangeBack -> -- {n,a,m,i} (fin n, fin i) => [n]a -> [m][i] -> [m]a
      tlam $ \(finTValue -> n) ->
      tlam $ \a ->
      tlam $ \_ ->
      tlam $ \_ ->
      VFun $ \th1 -> return $
      VFun $ \th2 -> do
        err <- Ready <$> zeroV a -- default for out-of-bounds accesses
        let f :: Thunk -> TheMonad Thunk
            f th = delay (selectV (\i -> nthV err th1 (n - 1 - i)) th)
        mapV f th2

    ECFromThen    -> -- {first, next, bits, len} (...) => [len][bits]
      tlam $ \first ->
      tlam $ \next ->
      tlam $ \bits ->
      VPoly $ \len -> do
        let w = fromInteger (finTValue bits)
        let delta = finTValue next - finTValue first
        let lit i = Ready (VWord (SBV.literal (bv w i)))
        let go :: Integer -> Integer -> TheMonad Value
            go 0 _ = return VNil
            go n i = VCons (lit i) <$> delay (go (n - 1) (i + delta))
        go (finTValue len) (finTValue first)

    ECFromTo      -> -- {first, last, bits} (...) => [1 + (last - first)][bits]
      tlam $ \first ->
      tlam $ \lst ->
      VPoly $ \bits -> do
        let w = fromInteger (finTValue bits)
        let lit i = Ready (VWord (SBV.literal (bv w i)))
        let go :: Integer -> Integer -> TheMonad Value
            go 0 _ = return VNil
            go n i = VCons (lit i) <$> delay (go (n - 1) (i + 1))
        go (finTValue lst - finTValue first + 1) (finTValue first)

    ECFromThenTo  -> -- {first, next, last, bits, len} (...) => [len][bits]
      tlam $ \first ->
      tlam $ \next ->
      tlam $ \_lst ->
      tlam $ \bits ->
      VPoly $ \len -> do
        let w = fromInteger (finTValue bits)
        let delta = finTValue next - finTValue first
        let lit i = Ready (VWord (SBV.literal (bv w i)))
        let go :: Integer -> Integer -> TheMonad Value
            go 0 _ = return VNil
            go n i = VCons (lit i) <$> delay (go (n - 1) (i + delta))
        go (finTValue len) (finTValue first)

    ECInfFrom     -> -- {a} (fin a) => [a] -> [inf][a]
      tlam $ \a ->
      VFun $ \th -> do
        let delta = SBV.literal (bv (fromInteger (finTValue a)) 1)
        let from x = VCons (Ready (VWord x)) <$> delay (from (x + delta))
        x0 <- fromWord =<< force th
        from x0

    ECInfFromThen -> -- {a} (fin a) => [a] -> [a] -> [inf][a]
      tlam $ \_ ->
      VFun $ \th1 -> return $
      VFun $ \th2 -> do
        x1 <- fromWord =<< force th1
        x2 <- fromWord =<< force th2
        let delta = x2 - x1
        let from x = VCons (Ready (VWord x)) <$> delay (from (x + delta))
        from x1

    -- {at,len} (fin len) => [len][8] -> at
    ECError ->
      tlam $ \at ->
      tlam $ \(finTValue -> _len) ->
      VFun $ \_msg -> zeroV  at -- error/undefined, is arbitrarily translated to 0

    ECPMul        -> -- {a,b} (fin a, fin b) => [a] -> [b] -> [max 1 (a + b) - 1]
      tlam $ \(finTValue -> i) ->
      tlam $ \(finTValue -> j) ->
      VFun $ \th1 -> return $
      VFun $ \th2 -> do
        let k = max 1 (i + j) - 1
        let mul _  []     ps = ps
            mul as (b:bs) ps = mul (SBV.false : as) bs (Poly.ites b (as `Poly.addPoly` ps) ps)
        xs <- traverse (fmap fromVBit . force) =<< fromSeq =<< force th1
        ys <- traverse (fmap fromVBit . force) =<< fromSeq =<< force th2
        let zs = take (fromInteger k) (mul xs ys [] ++ repeat SBV.false)
        return $ vSeq (map (Ready . VBit) zs)

    ECPDiv        -> -- {a,b} (fin a, fin b) => [a] -> [b] -> [a]
      tlam $ \(finTValue -> i) ->
      tlam $ \_ ->
      VFun $ \th1 -> return $
      VFun $ \th2 -> do
        xs <- traverse (fmap fromVBit . force) =<< fromSeq =<< force th1
        ys <- traverse (fmap fromVBit . force) =<< fromSeq =<< force th2
        let zs = take (fromInteger i) (fst (Poly.mdp (reverse xs) (reverse ys)) ++ repeat SBV.false)
        return $ vSeq (map (Ready . VBit) (reverse zs))

    ECPMod        -> -- {a,b} (fin a, fin b) => [a] -> [b+1] -> [b]
      tlam $ \_ ->
      tlam $ \(finTValue -> j) ->
      VFun $ \th1 -> return $
      VFun $ \th2 -> do
        xs <- traverse (fmap fromVBit . force) =<< fromSeq =<< force th1
        ys <- traverse (fmap fromVBit . force) =<< fromSeq =<< force th2
        let zs = take (fromInteger j) (snd (Poly.mdp (reverse xs) (reverse ys)) ++ repeat SBV.false)
        return $ vSeq (map (Ready . VBit) (reverse zs))

    ECRandom      -> error "ECRandom"

selectV :: (Integer -> TheMonad Value) -> Thunk -> TheMonad Value
selectV f th = do
  ths <- fromSeq =<< force th
  bits <- map fromVBit <$> traverse force ths -- index bits in big-endian order
  let sel :: Integer -> [SBool] -> TheMonad Value
      sel offset []       = f offset
      sel offset (b : bs) = iteM b m1 m2
        where m1 = sel (offset + 2 ^ length bs) bs
              m2 = sel offset bs
  sel 0 bits

replicateV :: Integer -> Thunk -> TheMonad Value
replicateV n x = return (go n)
  where go 0 = VNil
        go i = VCons x (Ready (go (i - 1)))

nthV :: Thunk -> Thunk -> Integer -> TheMonad Value
nthV err xs n = do
  v <- force xs
  case v of
    VCons x xs' | n == 0    -> force x
                | otherwise -> nthV err xs' (n - 1)
    VWord x                 -> let i = bitSize x - 1 - fromInteger n
                               in if i < 0 then force err else
                                    return $ VBit (SBV.sbvTestBit x i)
    _                       -> force err

mapV :: (Thunk -> TheMonad Thunk) -> Thunk -> TheMonad Value
mapV f th = do
  v <- force th
  case v of
    VNil       -> return VNil
    VCons x xs -> do y <- f x
                     ys <- delay (mapV f xs)
                     return $ VCons y ys
    _          -> error "mapV"

catV :: Thunk -> Thunk -> TheMonad Value
catV xs ys = do
  v <- force xs
  case v of
    VCons x xs' -> VCons x <$> delay (catV xs' ys)
    VNil        -> force ys
    VWord x     -> do y <- fromWord =<< force ys
                      return $ VWord (cat x y)
    _           -> error "catV"

dropV :: Integer -> Thunk -> TheMonad Value
dropV 0 xs = force xs
dropV n xs = do
  v <- force xs
  case v of
    VCons _ xs' -> dropV (n - 1) xs'
    VNil        -> return VNil
    VWord w     -> return $ VWord $ extract (bitSize w - 1 - fromInteger n) 0 w
    _           -> error "dropV"

takeV :: Integer -> Thunk -> TheMonad Value
takeV 0 _ = return VNil
takeV n xs = do
  v <- force xs
  case v of
    VWord w     -> return $ VWord $ extract (bitSize w - 1) (bitSize w - fromInteger n) w
    VCons x xs' -> VCons x <$> delay (takeV (n - 1) xs')
    VNil        -> return VNil
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

type Binary = TValue -> Value -> Value -> TheMonad Value

binary :: Binary -> Value
binary f = VPoly $ \ty ->
           return $ VFun $ \th1 ->
           return $ VFun $ \th2 -> do
             v1 <- force th1
             v2 <- force th2
             f ty v1 v2

type Unary = TValue -> Value -> TheMonad Value

unary :: Unary -> Value
unary f = VPoly $ \ty ->
          return $ VFun $ \th -> do
            v <- force th
            f ty v

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
    loop' ty th1 th2 = delay $ do
      v1 <- force th1
      v2 <- force th2
      loop ty v1 v2
    loop ty l r =
      case ty of
        TVBit         -> evalPanic "arithBinop" ["Invalid arguments"]
        TVSeq _ TVBit -> VWord <$> (op <$> fromWord l <*> fromWord r)
        TVSeq 0 _     -> return VNil
        TVSeq n t     -> VCons <$> loop' t hl hr <*> loop' (TVSeq (n - 1) t) tl tr
                           where (hl, tl) = fromVCons l
                                 (hr, tr) = fromVCons r
        TVStream t    -> VCons <$> loop' t hl hr <*> loop' ty tl tr
                           where (hl, tl) = fromVCons l
                                 (hr, tr) = fromVCons r
        TVTuple ts    -> VTuple <$> sequenceA (zipWith3 loop' ts (fromVTuple l) (fromVTuple r))
        TVRecord fs   -> VRecord <$> traverse (traverseSnd id)
                           [ (f, loop' t (lookupRecord f l) (lookupRecord f r))
                           | (f, t) <- fs ]
        TVFun _ t     -> return $ VFun $ \ x -> do
                           lx <- fromVFun l x
                           rx <- fromVFun r x
                           loop t lx rx

-- | Models functions of type `{a} (Arith a) => a -> a`
arithUnary :: (SWord -> SWord) -> Unary
arithUnary op = loop . toTypeVal
  where
    loop' ty thunk = delay (loop ty =<< force thunk)
    loop ty v =
      case ty of
        TVBit         -> evalPanic "arithUnary" ["Invalid arguments"]
        TVSeq _ TVBit -> VWord <$> (op <$> fromWord v)
        TVSeq 0 _     -> return VNil
        TVSeq n t     -> VCons <$> loop' t vh <*> loop' (TVSeq (n - 1) t) vt
                           where (vh, vt) = fromVCons v
        TVStream t    -> VCons <$> loop' t vh <*> loop' ty vt
                           where (vh, vt) = fromVCons v
        TVTuple ts    -> VTuple <$> zipWithM loop' ts (fromVTuple v)
        TVRecord fs   -> VRecord <$> traverse (traverseSnd id)
                           [ (f, loop' t (lookupRecord f v)) | (f, t) <- fs ]
        TVFun _ t     -> return $ VFun $ \ x -> loop t =<< fromVFun v x

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

cmpValue :: (SBool -> SBool -> TheMonad a -> TheMonad a)
         -> (SWord -> SWord -> TheMonad a -> TheMonad a)
         -> (Value -> Value -> TheMonad a -> TheMonad a)
cmpValue fb fw = cmp
  where
    cmp v1 v2 k =
      case (v1, v2) of
        (VRecord fs1, VRecord fs2) -> cmpThunks (map snd fs1) (map snd fs2) k
        (VTuple ths1, VTuple ths2) -> cmpThunks ths1 ths2 k
        (VBit b1    , VBit b2    ) -> fb b1 b2 k
        (VWord w1   , VWord w2   ) -> fw w1 w2 k
        (VNil       , VNil       ) -> k
        (VCons h1 t1, VCons h2 t2) -> cmpThunks [h1,t1] [h2,t2] k
        (VFun {}    , VFun {}    ) -> error "Functions are not comparable"
        (VPoly {}   , VPoly {}   ) -> error "Polymorphic values are not comparable"
        (VWord w1   , _          ) -> do { w2 <- fromWord v2; fw w1 w2 k }
        (_          , VWord w2   ) -> do { w1 <- fromWord v1; fw w1 w2 k }
        (_          , _          ) -> error "type mismatch"
    cmpThunks (x1 : xs1) (x2 : xs2) k = do
      v1 <- force x1
      v2 <- force x2
      cmp v1 v2 (cmpThunks xs1 xs2 k)
    cmpThunks _ _ k = k

lazyConj :: Monad m => SBool -> m SBool -> m SBool
lazyConj s m
  | s `SBV.isConcretely` (== False) = return s
  | otherwise = liftM ((SBV.&&&) s) m

lazyDisj :: Monad m => SBool -> m SBool -> m SBool
lazyDisj s m
  | s `SBV.isConcretely` (== True) = return s
  | otherwise = liftM ((SBV.|||) s) m

cmpEq :: (SBV.EqSymbolic a, Monad m) => a -> a -> m SBool -> m SBool
cmpEq x y k = lazyConj ((SBV..==) x y) k

cmpNotEq :: (SBV.EqSymbolic a, Monad m) => a -> a -> m SBool -> m SBool
cmpNotEq x y k = lazyDisj ((SBV../=) x y) k

cmpLt, cmpGt :: (SBV.OrdSymbolic a, Monad m) => a -> a -> m SBool -> m SBool
cmpLt x y k = lazyDisj ((SBV..<) x y) (cmpEq x y k)
cmpGt x y k = lazyDisj ((SBV..>) x y) (cmpEq x y k)

cmpLtEq, cmpGtEq :: (SBV.OrdSymbolic a, Monad m) => a -> a -> m SBool -> m SBool
cmpLtEq x y k = lazyConj ((SBV..<=) x y) (cmpNotEq x y k)
cmpGtEq x y k = lazyConj ((SBV..>=) x y) (cmpNotEq x y k)

cmpBinary :: (SBool -> SBool -> TheMonad SBool -> TheMonad SBool)
          -> (SWord -> SWord -> TheMonad SBool -> TheMonad SBool)
          -> SBool -> Binary
cmpBinary fb fw b _ty v1 v2 = liftM VBit $ cmpValue fb fw v1 v2 (return b)


-- Logic -----------------------------------------------------------------------

errorV :: String -> TValue -> TheMonad Value
errorV msg = return . go . toTypeVal
  where
    go ty =
      case ty of
        TVBit         -> VBit (error msg)
        TVSeq n t     -> vSeq (replicate n (Ready (go t)))
        TVStream t    -> let v = VCons (Ready (go t)) (Ready v) in v
        TVTuple ts    -> VTuple [ Ready (go t) | t <- ts ]
        TVRecord fs   -> VRecord [ (n, Ready (go t)) | (n, t) <- fs ]
        TVFun _ t     -> VFun (\ _ -> return (go t))



zeroV :: TValue -> TheMonad Value
zeroV = return . go . toTypeVal
  where
    go ty =
      case ty of
        TVBit         -> VBit SBV.false
        TVSeq n TVBit -> VWord (SBV.literal (bv n 0))
        TVSeq n t     -> vSeq (replicate n (Ready (go t)))
        TVStream t    -> let v = VCons (Ready (go t)) (Ready v) in v
        TVTuple ts    -> VTuple [ Ready (go t) | t <- ts ]
        TVRecord fs   -> VRecord [ (n, Ready (go t)) | (n, t) <- fs ]
        TVFun _ t     -> VFun (\ _ -> return (go t))

-- | Merge two values given a binop.  This is used for and, or and xor.
logicBinary :: (SBool -> SBool -> SBool) -> (SWord -> SWord -> SWord) -> Binary
logicBinary bop op = loop . toTypeVal
  where
    loop' ty th1 th2 = delay $ do
      v1 <- force th1
      v2 <- force th2
      loop ty v1 v2
    loop ty l r =
      case ty of
        TVBit         -> return $ VBit (bop (fromVBit l) (fromVBit r))
        TVSeq _ TVBit -> VWord <$> (op <$> fromWord l <*> fromWord r)
        TVSeq 0 _     -> return VNil
        TVSeq n t     -> VCons <$> loop' t hl hr <*> loop' (TVSeq (n - 1) t) tl tr
                           where (hl, tl) = fromVCons l
                                 (hr, tr) = fromVCons r
        TVStream t    -> VCons <$> loop' t hl hr <*> loop' ty tl tr
                           where (hl, tl) = fromVCons l
                                 (hr, tr) = fromVCons r
        TVTuple ts    -> VTuple <$> sequenceA (zipWith3 loop' ts (fromVTuple l) (fromVTuple r))
        TVRecord fs   -> VRecord <$> traverse (traverseSnd id)
                           [ (f, loop' t (lookupRecord f l) (lookupRecord f r))
                           | (f, t) <- fs ]
        TVFun _ t     -> return $ VFun $ \ x -> do
                           lx <- fromVFun l x
                           rx <- fromVFun r x
                           loop t lx rx

logicUnary :: (SBool -> SBool) -> (SWord -> SWord) -> Unary
logicUnary bop op = loop . toTypeVal
  where
    loop' ty thunk = delay (loop ty =<< force thunk)
    loop ty v =
      case ty of
        TVBit         -> return $ VBit (bop (fromVBit v))
        TVSeq _ TVBit -> VWord <$> (op <$> fromWord v)
        TVSeq 0 _     -> return VNil
        TVSeq n t     -> VCons <$> loop' t vh <*> loop' (TVSeq (n - 1) t) vt
                           where (vh, vt) = fromVCons v
        TVStream t    -> VCons <$> loop' t vh <*> loop' ty vt
                           where (vh, vt) = fromVCons v
        TVTuple ts    -> VTuple <$> zipWithM loop' ts (fromVTuple v)
        TVRecord fs   -> VRecord <$> traverse (traverseSnd id)
                           [ (f, loop' t (lookupRecord f v)) | (f, t) <- fs ]
        TVFun _ t     -> return $ VFun $ \ x -> loop t =<< fromVFun v x
