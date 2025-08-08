{-# LANGUAGE BangPatterns, BlockArguments #-}
{- |
Module      : Data.RME.Vector
Copyright   : Galois, Inc. 2016
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : portable

Operations on big-endian vectors of RME formulas.
-}

module Data.RME.Vector
  ( RMEV
  , eq, ule, ult, sle, slt
  , neg, add, sub, mul
  , udiv, urem, sdiv, srem
  , pmul, pmod, pdiv
  , shl, ashr, lshr, ror, rol
  , integer
  , popcount
  , countLeadingZeros
  , countTrailingZeros
  ) where

import Data.RME.Base (RME)
import qualified Data.RME.Base as RME

import qualified Data.Bits as Bits
import Data.Vector (Vector)
import qualified Data.Vector as V

type RMEV = Vector RME

-- | Constant integer literals.
integer :: Int -> Integer -> RMEV
integer width x = V.reverse (V.generate width (RME.constant . Bits.testBit x))

-- | Bitvector equality.
eq :: RMEV -> RMEV -> RME
eq x y = V.foldr RME.conj RME.true (V.zipWith RME.iff x y)

-- | Unsigned less-than-or-equal.
ule :: RMEV -> RMEV -> RME
ule xv yv = go (V.toList xv) (V.toList yv)
  where
    go (x : xs) (y : ys) =
      let z = go xs ys
      in RME.xor (RME.conj y z) (RME.conj (RME.compl x) (RME.xor y z))
    go _ _ = RME.true

-- | Unsigned less-than.
ult :: RMEV -> RMEV -> RME
ult x y = RME.compl (ule y x)

swap_sign :: RMEV -> RMEV
swap_sign x
  | V.null x = x
  | otherwise = V.singleton (RME.compl (V.head x)) V.++ V.tail x

-- | Signed less-than-or-equal.
sle :: RMEV -> RMEV -> RME
sle x y = ule (swap_sign x) (swap_sign y)

-- | Signed less-than.
slt :: RMEV -> RMEV -> RME
slt x y = ult (swap_sign x) (swap_sign y)

-- | Big-endian bitvector increment with carry.
increment :: [RME] -> (RME, [RME])
increment [] = (RME.true, [])
increment (x : xs) = (RME.conj x c, RME.xor x c : ys)
  where (c, ys) = increment xs

-- | Two's complement bitvector negation.
neg :: RMEV -> RMEV
neg x = V.fromList (snd (increment (map RME.compl (V.toList x))))

-- | 1-bit full adder.
full_adder :: RME -> RME -> RME -> (RME, RME)
full_adder a b c = (carry, RME.xor (RME.xor a b) c)
  where carry = RME.xor (RME.conj a b) (RME.conj (RME.xor a b) c)

-- | Big-endian ripple-carry adder.
ripple_carry_adder :: [RME] -> [RME] -> RME -> (RME, [RME])
ripple_carry_adder [] _ c = (c, [])
ripple_carry_adder _ [] c = (c, [])
ripple_carry_adder (x : xs) (y : ys) c = (c'', z : zs)
  where (c', zs) = ripple_carry_adder xs ys c
        (c'', z) = full_adder x y c'

-- | Two's complement bitvector addition.
add :: RMEV -> RMEV -> RMEV
add x y =
  V.fromList (snd (ripple_carry_adder (V.toList x) (V.toList y) RME.false))

-- | Two's complement bitvector subtraction.
sub :: RMEV -> RMEV -> RMEV
sub x y =
  V.fromList (snd (ripple_carry_adder (V.toList x) (map RME.compl (V.toList y)) RME.true))

-- | Two's complement bitvector multiplication.
mul :: RMEV -> RMEV -> RMEV
mul x y = V.foldl f zero y
  where
    zero = V.replicate (V.length x) RME.false
    f acc c = V.zipWith (RME.mux c) (add acc2 x) acc2
      where acc2 = V.drop 1 (acc V.++ V.singleton RME.false)

-- | Unsigned bitvector division.
udiv :: RMEV -> RMEV -> RMEV
udiv x y = fst (udivrem x y)

-- | Unsigned bitvector remainder.
urem :: RMEV -> RMEV -> RMEV
urem x y = snd (udivrem x y)

-- | Signed bitvector division.
sdiv :: RMEV -> RMEV -> RMEV
sdiv x y = fst (sdivrem x y)

-- | Signed bitvector remainder.
srem :: RMEV -> RMEV -> RMEV
srem x y = snd (sdivrem x y)

udivrem :: RMEV -> RMEV -> (RMEV, RMEV)
udivrem dividend divisor = divStep 0 RME.false initial
  where
    n :: Int
    n = V.length dividend

    -- Given an n-bit dividend and divisor, 'initial' is the starting value of
    -- the 2n-bit "remainder register" that carries both the quotient and remainder;
    initial :: RMEV
    initial = integer n 0 V.++ dividend

    divStep :: Int -> RME -> RMEV -> (RMEV, RMEV)
    divStep i p rr | i == n = (q `shiftL1` p, r)
      where (r, q) = V.splitAt n rr
    divStep i p rr = divStep (i+1) b (V.zipWith (RME.mux b) (V.fromList s V.++ q) rs)
      where rs = rr `shiftL1` p
            (r, q) = V.splitAt n rs
            -- Subtract the divisor from the left half of the "remainder register"
            (b, s) = ripple_carry_adder (V.toList r) (map RME.compl (V.toList divisor)) RME.true

    shiftL1 :: RMEV -> RME -> RMEV
    shiftL1 v e = V.tail v `V.snoc` e

-- Perform udivrem on the absolute value of the operands.  Then, negate the
-- quotient if the signs of the operands differ and make the sign of a nonzero
-- remainder to match that of the dividend.
sdivrem :: RMEV -> RMEV -> (RMEV, RMEV)
sdivrem dividend divisor = (q',r')
  where
    sign1 = V.head dividend
    sign2 = V.head divisor
    signXor = RME.xor sign1 sign2
    negWhen x c = V.zipWith (RME.mux c) (neg x) x
    dividend' = negWhen dividend sign1
    divisor' = negWhen divisor sign2
    (q, r) = udivrem dividend' divisor'
    q' = negWhen q signXor
    r' = negWhen r sign1

popcount :: RMEV -> RMEV
popcount bits = if l == 0 then V.empty else (V.replicate (l-w-1) RME.false) <> pcnt
  where
    l = V.length bits
    w = Bits.countTrailingZeros l -- log_2 rounded down, w+1 is enough bits to hold popcount
    zs = V.replicate w RME.false

    pcnt = foldr1 add xs -- length is w+1
    xs = [ zs <> V.singleton b | b <- V.toList bits ]

countTrailingZeros :: RMEV -> RMEV
countTrailingZeros bits = countLeadingZeros (V.reverse bits)

-- Big endian convention means its easier to count leading zeros
countLeadingZeros :: RMEV -> RMEV
countLeadingZeros bits = if l == 0 then V.empty else (V.replicate (l-w-1) RME.false) <> (go 0 (V.toList bits))
  where
    l = V.length bits
    w = Bits.countTrailingZeros l -- log_2 rounded down, w+1 is enough bits to hold count

    go :: Integer -> [RME] -> Vector RME
    go !i []      = integer (w+1) i
    go !i (b:bs)  = V.zipWith (RME.mux b) (integer (w+1) i) (go (i+1) bs)

-- | Polynomial multiplication. Note that the algorithm works the same
-- no matter which endianness convention is used. Result length is
-- @max 0 (m+n-1)@, where @m@ and @n@ are the lengths of the inputs.
pmul :: RMEV -> RMEV -> RMEV
pmul x y = V.generate (max 0 (m + n - 1)) coeff
  where
    m = V.length x
    n = V.length y
    coeff k = foldr RME.xor RME.false
      [ RME.conj (x V.! i) (y V.! j) | i <- [0 .. k], let j = k - i, i < m, j < n ]

-- | Polynomial mod with symbolic modulus. Return value has length one
-- less than the length of the modulus.
-- This implementation is optimized for the (common) case where the modulus
-- is concrete.
pmod :: RMEV -> RMEV -> RMEV
pmod x y = findmsb (V.toList y)
  where
    findmsb :: [RME] -> RMEV
    findmsb [] = V.replicate (V.length y - 1) RME.false -- division by zero
    findmsb (c : cs)
      | c == RME.true = usemask cs
      | c == RME.false = findmsb cs
      | otherwise = V.zipWith (RME.mux c) (usemask cs) (findmsb cs)

    usemask :: [RME] -> RMEV
    usemask m = zext (V.fromList (go (V.length x - 1) p0 z0)) (V.length y - 1)
      where
        zext v r = V.replicate (r - V.length v) RME.false V.++ v
        msize = length m
        p0 = replicate (msize - 1) RME.false ++ [RME.true]
        z0 = replicate msize RME.false

        next :: [RME] -> [RME]
        next [] = []
        next (b : bs) =
          let m' = map (RME.conj b) m
              bs' = bs ++ [RME.false]
          in zipWith RME.xor m' bs'

        go :: Int -> [RME] -> [RME] -> [RME]
        go i p acc
          | i < 0 = acc
          | otherwise =
              let px = map (RME.conj (x V.! i)) p
                  acc' = zipWith RME.xor px acc
                  p' = next p
              in go (i-1) p' acc'

-- | Polynomial division. Return value has length
--   equal to the first argument.
pdiv :: RMEV -> RMEV -> RMEV
pdiv x y = fst (pdivmod x y)

-- Polynomial div/mod: resulting lengths are as in Cryptol.

-- TODO: probably this function should be disentangled to only compute
-- division, given that we have a separate polynomial modulus algorithm.
pdivmod :: RMEV -> RMEV -> (RMEV, RMEV)
pdivmod x y = findmsb (V.toList y)
  where
    findmsb :: [RME] -> (RMEV, RMEV)
    findmsb (c : cs) = muxPair c (usemask cs) (findmsb cs)
    findmsb [] = (x, V.replicate (V.length y - 1) RME.false) -- division by zero

    usemask :: [RME] -> (RMEV, RMEV)
    usemask mask = (q, r)
      where
        (qs, rs) = pdivmod_helper (V.toList x) mask
        z = RME.false
        qs' = map (const z) rs ++ qs
        rs' = replicate (V.length y - 1 - length rs) z ++ rs
        q = V.fromList qs'
        r = V.fromList rs'

    muxPair :: RME -> (RMEV, RMEV) -> (RMEV, RMEV) -> (RMEV, RMEV)
    muxPair c a b
      | c == RME.true = a
      | c == RME.false = b
      | otherwise = (V.zipWith (RME.mux c) (fst a) (fst b), V.zipWith (RME.mux c) (snd a) (snd b))

-- Divide ds by (1 : mask), giving quotient and remainder. All
-- arguments and results are big-endian. Remainder has the same length
-- as mask (but limited by length ds); total length of quotient ++
-- remainder = length ds.
pdivmod_helper :: [RME] -> [RME] -> ([RME], [RME])
pdivmod_helper ds mask = go (length ds - length mask) ds
  where
    go :: Int -> [RME] -> ([RME], [RME])
    go n cs | n <= 0 = ([], cs)
    go _ []          = error "Data.AIG.Operations.pdiv: impossible"
    go n (c : cs)    = (c : qs, rs)
      where cs' = mux_add c cs mask
            (qs, rs) = go (n - 1) cs'

    mux_add :: RME -> [RME] -> [RME] -> [RME]
    mux_add c (x : xs) (y : ys) = RME.mux c (RME.xor x y) x : mux_add c xs ys
    mux_add _ []       (_ : _ ) = error "pdiv: impossible"
    mux_add _ xs       []       = xs

bitOp :: (RMEV -> Int -> Int -> RME) -> RMEV -> RMEV -> RMEV
bitOp f x y = V.generate w \i -> pick i 0 y'
  where
    y' = V.toList y
    w = length x
    pick i j [] = f x i j
    pick i j (b:bs) = RME.mux b (pick i (1+2*j) bs) (pick i (2*j) bs)

shl :: RMEV -> RMEV -> RMEV
shl = bitOp \x i j ->
  let w = length x in 
  if i + j >= w then RME.false else x V.! (i+j)

ashr :: RMEV -> RMEV -> RMEV
ashr = bitOp \x i j ->
  if i < j then V.head x else x V.! (i-j)

lshr :: RMEV -> RMEV -> RMEV
lshr = bitOp \x i j ->
  if i < j then RME.false else x V.! (i-j)

rol :: RMEV -> RMEV -> RMEV
rol = bitOp \x i j ->
  let w = length x in
  x V.! ((i + j)`mod`w)

ror :: RMEV -> RMEV -> RMEV
ror = bitOp \x i j ->
  let w = length x in
  x V.! ((i - j)`mod`w)
