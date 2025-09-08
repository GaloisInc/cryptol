-----------------------------------------------------------------------------
-- |
-- Module    : Cryptol.PrimeEC
-- Copyright : (c) Galois, Inc.
-- License   : BSD3
-- Maintainer: rdockins@galois.com
-- Stability : experimental
--
-- This module provides fast primitives for elliptic curve cryptography
-- defined on @Z p@ for prime @p > 3@.  These are exposed in cryptol
-- by importing the built-in module "PrimeEC".  The primary primitives
-- exposed here are the doubling and addition primitives in the ECC group
-- as well as scalar multiplication and the "twin" multiplication primitive,
-- which simultaneously computes the addition of two scalar multiplies.
--
-- This module makes heavy use of some GHC internals regarding the
-- representation of the Integer type, and the underlying GMP primitives
-- in order to speed up the basic modular arithmetic operations.
-----------------------------------------------------------------------------
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UnboxedTuples #-}

#if __GLASGOW_HASKELL__ >= 900
-- On GHC 9.0 or later—that is, when building with ghc-bignum—BigNum# is an
-- unlifted type, so we need UnliftedNewtypes to declare a newtype on top of
-- it. On older versions of GHC, BigNat# is simply a synonym for BigNat. BigNat
-- is lifted, so declaring a newtype on top of it works out of the box.
{-# LANGUAGE UnliftedNewtypes #-}
#endif

module Cryptol.PrimeEC
  ( PrimeModulus
  , primeModulus
  , ProjectivePoint(..)
  , toProjectivePoint
  , BN.integerToBigNat
  , BN.bigNatToInteger

  , ec_double
  , ec_add_nonzero
  , ec_mult
  , ec_twin_mult
  ) where


import           GHC.Num.Compat (BigNat#)
import qualified GHC.Num.Compat as BN
import           GHC.Exts

import Cryptol.TypeCheck.Solver.InfNat (widthInteger)
import Cryptol.Utils.Panic

-- | Points in the projective plane represented in
--   homogenous coordinates.
data ProjectivePoint =
  ProjectivePoint
  { px :: !BigNat#
  , py :: !BigNat#
  , pz :: !BigNat#
  }


toProjectivePoint :: Integer -> Integer -> Integer -> ProjectivePoint
toProjectivePoint x y z =
  ProjectivePoint (BN.integerToBigNat x) (BN.integerToBigNat y) (BN.integerToBigNat z)

-- | The projective "point at infinity", which represents the zero element
--   of the ECC group.
zro :: ProjectivePoint
zro = ProjectivePoint (BN.oneBigNat (# #)) (BN.oneBigNat (# #)) (BN.zeroBigNat (# #))

-- | Simple newtype wrapping the @BigNat@ value of the
--   modulus of the underlying field Z p.  This modulus
--   is required to be prime.
newtype PrimeModulus = PrimeModulus { primeMod :: BigNat# }


-- | Inject an integer value into the @PrimeModulus@ type.
--   This modulus is required to be prime.
primeModulus :: Integer -> PrimeModulus
primeModulus x = PrimeModulus (BN.integerToBigNat x)
{-# INLINE primeModulus #-}


-- | Modular addition of two values.  The inputs are
--   required to be in reduced form, and will output
--   a value in reduced form.
mod_add :: PrimeModulus -> BigNat# -> BigNat# -> BigNat#
mod_add p x y =
  let r = BN.bigNatAdd x y in
  case BN.bigNatSub r (primeMod p) of
    (# (# #) | #) -> r
    (# | rmp #)   -> rmp

-- | Compute the "half" value of a modular integer.  For a given input @x@
--   this is a value @y@ such that @y+y == x@.  Such values must exist
--   in @Z p@ when @p > 2@.  The input @x@ is required to be in reduced form,
--   and will output a value in reduced form.
mod_half :: PrimeModulus -> BigNat# -> BigNat#
mod_half p x = if BN.testBitBigNat x 0# then qodd else qeven
  where
  qodd  = (BN.bigNatAdd x (primeMod p)) `BN.shiftRBigNat` 1#
  qeven = x `BN.shiftRBigNat` 1#

-- | Compute the modular multiplication of two input values.  Currently, this
--   uses naive modular reduction, and does not require the inputs to be in
--   reduced form.  The output is in reduced form.
mod_mul :: PrimeModulus -> BigNat# -> BigNat# -> BigNat#
mod_mul p x y = (BN.bigNatMul x y) `BN.bigNatRem` (primeMod p)

-- | Compute the modular difference of two input values.  The inputs are
--   required to be in reduced form, and will output a value in reduced form.
mod_sub :: PrimeModulus -> BigNat# -> BigNat# -> BigNat#
mod_sub p x y =
  case BN.bigNatSub (primeMod p) y of
    (# | y' #) -> mod_add p x y'
    (# (# #) | #) -> x -- BOGUS!

-- | Compute the modular square of an input value @x@; that is, @x*x@.
--   The input is not required to be in reduced form, and the output
--   will be in reduced form.
mod_square :: PrimeModulus -> BigNat# -> BigNat#
mod_square p x = BN.bigNatSqr x `BN.bigNatRem` primeMod p

-- | Compute the modular scalar multiplication @2x = x+x@.
--   The input is required to be in reduced form and the output
--   will be in reduced form.
mul2 :: PrimeModulus -> BigNat# -> BigNat#
mul2 p x =
  let r = x `BN.shiftLBigNat` 1# in
  case BN.bigNatSub r (primeMod p) of
    (# (# #) | #) -> r
    (# | rmp #)   -> rmp

-- | Compute the modular scalar multiplication @3x = x+x+x@.
--   The input is required to be in reduced form and the output
--   will be in reduced form.
mul3 :: PrimeModulus -> BigNat# -> BigNat#
mul3 p x = mod_add p x (mul2 p x)

-- | Compute the modular scalar multiplication @4x = x+x+x+x@.
--   The input is required to be in reduced form and the output
--   will be in reduced form.
mul4 :: PrimeModulus -> BigNat# -> BigNat#
mul4 p x = mul2 p (mul2 p x)

-- | Compute the modular scalar multiplication @8x = x+x+x+x+x+x+x+x@.
--   The input is required to be in reduced form and the output
--   will be in reduced form.
mul8 :: PrimeModulus -> BigNat# -> BigNat#
mul8 p x = mul2 p (mul4 p x)


-- | Compute the elliptic curve group doubling operation.
--   In other words, if @S@ is a projective point on a curve,
--   this operation computes @S+S@ in the ECC group.
--
--   In geometric terms, this operation computes a tangent line
--   to the curve at @S@ and finds the (unique) intersection point of this
--   line with the curve, @R@; then returns the point @R'@, which is @R@
--   reflected across the x axis.
ec_double :: PrimeModulus -> ProjectivePoint -> ProjectivePoint
ec_double p (ProjectivePoint sx sy sz) =
    if BN.bigNatIsZero sz then zro else ProjectivePoint r18 r23 r13

  where
  r7  = mod_square p sz                   {-  7: t4 <- (t3)^2  -}
  r8  = mod_sub    p sx r7                {-  8: t5 <- t1 - t4 -}
  r9  = mod_add    p sx r7                {-  9: t4 <- t1 + t4 -}
  r10 = mod_mul    p r9 r8                {- 10: t5 <- t4 * t5 -}
  r11 = mul3       p r10                  {- 11: t4 <- 3 * t5 -}
  r12 = mod_mul    p sz sy                {- 12: t3 <- t3 * t2 -}
  r13 = mul2       p r12                  {- 13: t3 <- 2 * t3 -}
  r14 = mod_square p sy                   {- 14: t2 <- (t2)^2 -}
  r15 = mod_mul    p sx r14               {- 15: t5 <- t1 * t2 -}
  r16 = mul4       p r15                  {- 16: t5 <- 4 * t5 -}
  r17 = mod_square p r11                  {- 17: t1 <- (t4)^2 -}
  r18 = mod_sub    p r17 (mul2 p r16)     {- 18: t1 <- t1 - 2 * t5 -}
  r19 = mod_square p r14                  {- 19: t2 <- (t2)^2 -}
  r20 = mul8       p r19                  {- 20: t2 <- 8 * t2 -}
  r21 = mod_sub    p r16 r18              {- 21: t5 <- t5 - t1 -}
  r22 = mod_mul    p r11 r21              {- 22: t5 <- t4 * t5 -}
  r23 = mod_sub    p r22 r20              {- 23: t2 <- t5 - t2 -}

-- | Compute the elliptic curve group addition operation, including the special
--   case for adding points which might be the identity.
ec_add :: PrimeModulus -> ProjectivePoint -> ProjectivePoint -> ProjectivePoint
ec_add p s t
  | BN.bigNatIsZero (pz s) = t
  | BN.bigNatIsZero (pz t) = s
  | otherwise = ec_add_nonzero p s t
{-# INLINE ec_add #-}



-- | Compute the elliptic curve group subtraction operation, including the special
--   cases for subtracting points which might be the identity.
ec_sub :: PrimeModulus -> ProjectivePoint -> ProjectivePoint -> ProjectivePoint
ec_sub p s t = ec_add p s u
  where u = case BN.bigNatSub (primeMod p) (py t) of
              (# | y' #)    -> t{ py = y' `BN.bigNatRem` (primeMod p) }
              (# (# #) | #) -> panic "ec_sub" ["cooridnate not in reduced form!", show (BN.bigNatToInteger (py t))]
{-# INLINE ec_sub #-}


ec_negate :: PrimeModulus -> ProjectivePoint -> ProjectivePoint
ec_negate p s = s{ py = (BN.bigNatSubUnsafe (primeMod p) (py s))  `BN.bigNatRem` (primeMod p) }
{-# INLINE ec_negate #-}

-- | Compute the elliptic curve group addition operation
--   for values known not to be the identity.
--   In other words, if @S@ and @T@ are projective points on a curve,
--   with nonzero @z@ coordinate this operation computes @S+T@ in the ECC group.
--
--   In geometric terms, this operation computes a line that passes through
--   @S@ and @T@, and finds the (unique) other point @R@ where the line intersects
--   the curve; then returns the point @R'@, which is @R@ reflected across the x axis.
--   In the special case where @S == T@, we instead call the @ec_double@ operation,
--   which instead computes a tangent line to @S@ .
ec_add_nonzero :: PrimeModulus -> ProjectivePoint -> ProjectivePoint -> ProjectivePoint
ec_add_nonzero p s@(ProjectivePoint sx sy sz) (ProjectivePoint tx ty tz) =
    if BN.bigNatIsZero r13 then
      if BN.bigNatIsZero r14 then
        ec_double p s
      else
        zro
    else
      ProjectivePoint r32 r37 r27

  where
  tNormalized = BN.bigNatIsOne tz

  tz2 = mod_square p tz
  tz3 = mod_mul p tz tz2

  r5  = if tNormalized then sx else mod_mul p sx tz2
  r7  = if tNormalized then sy else mod_mul p sy tz3

  r9  = mod_square p sz                  {-  9: t7 <- (t3)^2 -}
  r10 = mod_mul    p tx r9               {- 10: t4 <- t4 * t7 -}
  r11 = mod_mul    p sz r9               {- 11: t7 <- t3 * t7 -}
  r12 = mod_mul    p ty r11              {- 12: t5 <- t5 * t7 -}
  r13 = mod_sub    p r5 r10              {- 13: t4 <- t1 - t4 -}
  r14 = mod_sub    p r7 r12              {- 14: t5 <- t2 - t5 -}

  r22 = mod_sub    p (mul2 p r5) r13     {- 22: t1 <- 2*t1 - t4 -}
  r23 = mod_sub    p (mul2 p r7) r14     {- 23: t2 <- 2*t2 - t5 -}

  r25 = if tNormalized then sz else mod_mul p sz tz

  r27 = mod_mul    p r25 r13             {- 27: t3 <- t3 * t4 -}
  r28 = mod_square p r13                 {- 28: t7 <- (t4)^2 -}
  r29 = mod_mul    p r13 r28             {- 29: t4 <- t4 * t7 -}
  r30 = mod_mul    p r22 r28             {- 30: t7 <- t1 * t7 -}
  r31 = mod_square p r14                 {- 31: t1 <- (t5)^2 -}
  r32 = mod_sub    p r31 r30             {- 32: t1 <- t1 - t7 -}
  r33 = mod_sub    p r30 (mul2 p r32)    {- 33: t7 <- t7 - 2*t1 -}
  r34 = mod_mul    p r14 r33             {- 34: t5 <- t5 * t7 -}
  r35 = mod_mul    p r23 r29             {- 35: t4 <- t2 * t4 -}
  r36 = mod_sub    p r34 r35             {- 36: t2 <- t5 - t4 -}
  r37 = mod_half   p r36                 {- 37: t2 <- t2/2 -}


-- | Given a nonidentity projective point, normalize it so that
--   its z component is 1.  This helps to avoid some modular
--   multiplies in @ec_add@, and may be a win if the point will
--   be added many times.
ec_normalize :: PrimeModulus -> ProjectivePoint -> ProjectivePoint
ec_normalize p s@(ProjectivePoint x y z)
  | BN.bigNatIsOne z = s
  | otherwise = ProjectivePoint x' y' (BN.oneBigNat (# #))
 where
  m = primeMod p

  l  = BN.recipModBigNat z m
  l2 = BN.bigNatSqr l
  l3 = BN.bigNatMul l l2

  x' = (BN.bigNatMul x l2) `BN.bigNatRem` m
  y' = (BN.bigNatMul y l3) `BN.bigNatRem` m


-- | Given an integer @k@ and a projective point @S@, compute
--   the scalar multiplication @kS@, which is @S@ added to itself
--   @k@ times.
ec_mult :: PrimeModulus -> Integer -> ProjectivePoint -> ProjectivePoint
ec_mult p d s
  | d == 0    = zro
  | d == 1    = s
  | BN.bigNatIsZero (pz s) = zro
  | otherwise =
      case m of
        0# -> panic "ec_mult" ["integer with 0 width", show h]
        _  -> go m zro

 where
   s' = ec_normalize p s
   h  = 3*d

   d' = BN.integerToBigNat d
   h' = BN.integerToBigNat h

   m = case widthInteger h of
         BN.IS mint -> mint
         _ -> 0#

   go :: Int# -> ProjectivePoint -> ProjectivePoint
   go i !r
     | tagToEnum# (i ==# 0#) = r
     | otherwise = go (i -# 1#) r'

    where
      h_i = BN.testBitBigNat h' i
      d_i = BN.testBitBigNat d' i

      r' = if h_i then
             if d_i then r2 else ec_add p r2 s'
           else
             if d_i then ec_sub p r2 s' else r2

      r2 = ec_double p r

{-# INLINE normalizeForTwinMult #-}

-- | Compute the sum and difference of the given points,
--   and normalize all four values.  This can be done jointly
--   in a more efficient way than computing the necessary
--   field inverses separately.
--   When given points S and T, the returned tuple contains
--   normalized representations for (S, T, S+T, S-T).
--
--   Note there are some special cases that must be handled separately.
normalizeForTwinMult ::
  PrimeModulus -> ProjectivePoint -> ProjectivePoint ->
  (ProjectivePoint, ProjectivePoint, ProjectivePoint, ProjectivePoint)
normalizeForTwinMult p s t
     -- S == 0 && T == 0
   | BN.bigNatIsZero a && BN.bigNatIsZero b =
        (zro, zro, zro, zro)

     -- S == 0 && T != 0
   | BN.bigNatIsZero a =
        let tnorm = ec_normalize p t
         in (zro, tnorm, tnorm, ec_negate p tnorm)

     -- T == 0 && S != 0
   | BN.bigNatIsZero b =
        let snorm = ec_normalize p s
         in (snorm, zro, snorm, snorm)

     -- S+T == 0, both != 0
   | BN.bigNatIsZero c =
        let snorm = ec_normalize p s
         in (snorm, ec_negate p snorm, zro, ec_double p snorm)

     -- S-T == 0, both != 0
   | BN.bigNatIsZero d =
        let snorm = ec_normalize p s
         in (snorm, snorm, ec_double p snorm, zro)

     -- S, T, S+T and S-T all != 0
   | otherwise = (s',t',spt',smt')

  where
  spt = ec_add p s t
  smt = ec_sub p s t

  m = primeMod p

  a = pz s
  b = pz t
  c = pz spt
  d = pz smt

  ab  = mod_mul p a b
  cd  = mod_mul p c d
  abc = mod_mul p ab c
  abd = mod_mul p ab d
  acd = mod_mul p a cd
  bcd = mod_mul p b cd

  abcd = mod_mul p a bcd

  e = BN.recipModBigNat abcd m

  a_inv = mod_mul p e bcd
  b_inv = mod_mul p e acd
  c_inv = mod_mul p e abd
  d_inv = mod_mul p e abc

  a_inv2 = mod_square p a_inv
  a_inv3 = mod_mul p a_inv a_inv2

  b_inv2 = mod_square p b_inv
  b_inv3 = mod_mul p b_inv b_inv2

  c_inv2 = mod_square p c_inv
  c_inv3 = mod_mul p c_inv c_inv2

  d_inv2 = mod_square p d_inv
  d_inv3 = mod_mul p d_inv d_inv2

  s'   = ProjectivePoint (mod_mul p (px s) a_inv2) (mod_mul p (py s) a_inv3) (BN.oneBigNat (# #))
  t'   = ProjectivePoint (mod_mul p (px t) b_inv2) (mod_mul p (py t) b_inv3) (BN.oneBigNat (# #))

  spt' = ProjectivePoint (mod_mul p (px spt) c_inv2) (mod_mul p (py spt) c_inv3) (BN.oneBigNat (# #))
  smt' = ProjectivePoint (mod_mul p (px smt) d_inv2) (mod_mul p (py smt) d_inv3) (BN.oneBigNat (# #))


-- | Given an integer @j@ and a projective point @S@, together with
--   another integer @k@ and point @T@ compute the "twin" scalar
--   the scalar multiplication @jS + kT@.  This computation can be done
--   essentially the same number of modular arithmetic operations
--   as a single scalar multiplication by doing some additional bookkeeping
--   and setup.
ec_twin_mult :: PrimeModulus ->
  Integer -> ProjectivePoint ->
  Integer -> ProjectivePoint ->
  ProjectivePoint
ec_twin_mult p (BN.integerToBigNat -> d0) s (BN.integerToBigNat -> d1) t =
   case m of
     0# -> panic "ec_twin_mult" ["modulus too large", show (BN.bigNatToInteger (primeMod p))]
     _  -> go m init_c0 init_c1 zro

 where
  (s',t',spt',smt') = normalizeForTwinMult p s t

  m = case max 4 (widthInteger (BN.bigNatToInteger (primeMod p))) of
        BN.IS mint -> mint
        _ -> 0# -- if `m` doesn't fit into an Int, should be impossible

  init_c0 = C False False (tst d0 (m -# 1#)) (tst d0 (m -# 2#)) (tst d0 (m -# 3#)) (tst d0 (m -# 4#))
  init_c1 = C False False (tst d1 (m -# 1#)) (tst d1 (m -# 2#)) (tst d1 (m -# 3#)) (tst d1 (m -# 4#))

  tst x i
    | isTrue# (i >=# 0#) = BN.testBitBigNat x i
    | otherwise = False

  f i =
    if isTrue# (i <# 18#) then
      if isTrue# (i <# 12#) then
        if isTrue# (i <# 4#) then
          12#
        else
          14#
      else
        if isTrue# (i <# 14#) then
          12#
        else
          10#
    else
      if isTrue# (i <# 22#) then
        9#
      else
        if isTrue# (i <# 24#) then
          11#
        else
          12#

  go !k !c0 !c1 !r = if isTrue# (k <# 0#) then r else go (k -# 1#) c0' c1' r'
    where
      h0  = cStateToH c0
      h1  = cStateToH c1
      u0  = if isTrue# (h0 <# f h1) then 0# else (if cHead c0 then -1# else 1#)
      u1  = if isTrue# (h1 <# f h0) then 0# else (if cHead c1 then -1# else 1#)
      c0' = cStateUpdate u0 c0 (tst d0 (k -# 5#))
      c1' = cStateUpdate u1 c1 (tst d1 (k -# 5#))

      r2 = ec_double p r

      r' =
        case u0 of
          -1# ->
            case u1 of
              -1# -> ec_sub p r2 spt'
              1#  -> ec_sub p r2 smt'
              _   -> ec_sub p r2 s'
          1#  ->
            case u1 of
              -1# -> ec_add p r2 smt'
              1#  -> ec_add p r2 spt'
              _   -> ec_add p r2 s'
          _   ->
            case u1 of
              -1# -> ec_sub p r2 t'
              1#  -> ec_add p r2 t'
              _   -> r2

data CState = C !Bool !Bool !Bool !Bool !Bool !Bool

{-# INLINE cHead #-}
cHead :: CState -> Bool
cHead (C c0 _ _ _ _ _) = c0

{-# INLINE cStateToH #-}
cStateToH :: CState -> Int#
cStateToH c@(C c0 _ _ _ _ _) =
  if c0 then 31# -# cStateToInt c else cStateToInt c

{-# INLINE cStateToInt #-}
cStateToInt :: CState -> Int#
cStateToInt (C _ c1 c2 c3 c4 c5) =
  (dataToTag# c1 `uncheckedIShiftL#` 4#) +#
  (dataToTag# c2 `uncheckedIShiftL#` 3#) +#
  (dataToTag# c3 `uncheckedIShiftL#` 2#) +#
  (dataToTag# c4 `uncheckedIShiftL#` 1#) +#
  (dataToTag# c5)

{-# INLINE cStateUpdate #-}
cStateUpdate :: Int# -> CState -> Bool -> CState
cStateUpdate u (C _ c1 c2 c3 c4 c5) e =
  case u of
    0# -> C c1 c2 c3 c4 c5 e
    _  -> C (not c1) c2 c3 c4 c5 e
