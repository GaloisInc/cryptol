-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.BitVectors.Polynomials
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Implementation of polynomial arithmetic
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                  #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE PatternGuards        #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Data.SBV.Tools.Polynomial (Polynomial(..), crc, crcBV, ites, addPoly, mdp) where

import Data.Bits  (Bits(..))
import Data.List  (genericTake)
import Data.Maybe (fromJust)
import Data.Word  (Word8, Word16, Word32, Word64)

import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.Model
import Data.SBV.BitVectors.Splittable
import Data.SBV.Utils.Boolean

-- | Implements polynomial addition, multiplication, division, and modulus operations
-- over GF(2^n).  NB. Similar to 'sQuotRem', division by @0@ is interpreted as follows:
--
--     @x `pDivMod` 0 = (0, x)@
--
-- for all @x@ (including @0@)
--
-- Minimal complete definition: 'pMult', 'pDivMod', 'showPolynomial'
class (Num a, Bits a) => Polynomial a where
 -- | Given bit-positions to be set, create a polynomial
 -- For instance
 --
 --     @polynomial [0, 1, 3] :: SWord8@
 -- 
 -- will evaluate to @11@, since it sets the bits @0@, @1@, and @3@. Mathematicans would write this polynomial
 -- as @x^3 + x + 1@. And in fact, 'showPoly' will show it like that.
 polynomial :: [Int] -> a
 -- | Add two polynomials in GF(2^n).
 pAdd  :: a -> a -> a
 -- | Multiply two polynomials in GF(2^n), and reduce it by the irreducible specified by
 -- the polynomial as specified by coefficients of the third argument. Note that the third
 -- argument is specifically left in this form as it is usally in GF(2^(n+1)), which is not available in our
 -- formalism. (That is, we would need SWord9 for SWord8 multiplication, etc.) Also note that we do not
 -- support symbolic irreducibles, which is a minor shortcoming. (Most GF's will come with fixed irreducibles,
 -- so this should not be a problem in practice.)
 --
 -- Passing [] for the third argument will multiply the polynomials and then ignore the higher bits that won't
 -- fit into the resulting size.
 pMult :: (a, a, [Int]) -> a
 -- | Divide two polynomials in GF(2^n), see above note for division by 0.
 pDiv  :: a -> a -> a
 -- | Compute modulus of two polynomials in GF(2^n), see above note for modulus by 0.
 pMod  :: a -> a -> a
 -- | Division and modulus packed together.
 pDivMod :: a -> a -> (a, a)
 -- | Display a polynomial like a mathematician would (over the monomial @x@), with a type.
 showPoly :: a -> String
 -- | Display a polynomial like a mathematician would (over the monomial @x@), the first argument
 -- controls if the final type is shown as well.
 showPolynomial :: Bool -> a -> String

 -- defaults.. Minumum complete definition: pMult, pDivMod, showPolynomial
 polynomial = foldr (flip setBit) 0
 pAdd       = xor
 pDiv x y   = fst (pDivMod x y)
 pMod x y   = snd (pDivMod x y)
 showPoly   = showPolynomial False


instance Polynomial Word8   where {showPolynomial   = sp;           pMult = lift polyMult; pDivMod = liftC polyDivMod}
instance Polynomial Word16  where {showPolynomial   = sp;           pMult = lift polyMult; pDivMod = liftC polyDivMod}
instance Polynomial Word32  where {showPolynomial   = sp;           pMult = lift polyMult; pDivMod = liftC polyDivMod}
instance Polynomial Word64  where {showPolynomial   = sp;           pMult = lift polyMult; pDivMod = liftC polyDivMod}
instance Polynomial SWord8  where {showPolynomial b = liftS (sp b); pMult = polyMult;      pDivMod = polyDivMod}
instance Polynomial SWord16 where {showPolynomial b = liftS (sp b); pMult = polyMult;      pDivMod = polyDivMod}
instance Polynomial SWord32 where {showPolynomial b = liftS (sp b); pMult = polyMult;      pDivMod = polyDivMod}
instance Polynomial SWord64 where {showPolynomial b = liftS (sp b); pMult = polyMult;      pDivMod = polyDivMod}

lift :: SymWord a => ((SBV a, SBV a, [Int]) -> SBV a) -> (a, a, [Int]) -> a
lift f (x, y, z) = fromJust $ unliteral $ f (literal x, literal y, z)
liftC :: SymWord a => (SBV a -> SBV a -> (SBV a, SBV a)) -> a -> a -> (a, a)
liftC f x y = let (a, b) = f (literal x) (literal y) in (fromJust (unliteral a), fromJust (unliteral b))
liftS :: SymWord a => (a -> String) -> SBV a -> String
liftS f s
  | Just x <- unliteral s = f x
  | True                  = show s

-- | Pretty print as a polynomial
sp :: Bits a => Bool -> a -> String
sp st a
 | null cs = '0' : t
 | True    = foldr (\x y -> sh x ++ " + " ++ y) (sh (last cs)) (init cs) ++ t
 where t | st   = " :: GF(2^" ++ show n ++ ")"
         | True = ""
#if __GLASGOW_HASKELL__ >= 708
       n  = maybe (error "SBV.Polynomial.sp: Unexpected non-finite usage!") id (bitSizeMaybe a)
#else
       n  = bitSize a
#endif
       is = [n-1, n-2 .. 0]
       cs = map fst $ filter snd $ zip is (map (testBit a) is)
       sh 0 = "1"
       sh 1 = "x"
       sh i = "x^" ++ show i

-- | Add two polynomials
addPoly :: [SBool] -> [SBool] -> [SBool]
addPoly xs    []      = xs
addPoly []    ys      = ys
addPoly (x:xs) (y:ys) = x <+> y : addPoly xs ys

ites :: SBool -> [SBool] -> [SBool] -> [SBool]
ites s xs ys
 | Just t <- unliteral s
 = if t then xs else ys
 | True
 = go xs ys
 where go [] []         = []
       go []     (b:bs) = ite s false b : go [] bs
       go (a:as) []     = ite s a false : go as []
       go (a:as) (b:bs) = ite s a b : go as bs

-- | Multiply two polynomials and reduce by the third (concrete) irreducible, given by its coefficients.
-- See the remarks for the 'pMult' function for this design choice
polyMult :: (Num a, Bits a, SymWord a, FromBits (SBV a)) => (SBV a, SBV a, [Int]) -> SBV a
polyMult (x, y, red)
  | isReal x
  = error $ "SBV.polyMult: Received a real value: " ++ show x
  | not (isBounded x)
  = error $ "SBV.polyMult: Received infinite precision value: " ++ show x
  | True
  = fromBitsLE $ genericTake sz $ r ++ repeat false
  where (_, r) = mdp ms rs
        ms = genericTake (2*sz) $ mul (blastLE x) (blastLE y) [] ++ repeat false
        rs = genericTake (2*sz) $ [if i `elem` red then true else false |  i <- [0 .. foldr max 0 red] ] ++ repeat false
        sz = intSizeOf x
        mul _  []     ps = ps
        mul as (b:bs) ps = mul (false:as) bs (ites b (as `addPoly` ps) ps)

polyDivMod :: (Num a, Bits a, SymWord a, FromBits (SBV a)) => SBV a -> SBV a -> (SBV a, SBV a)
polyDivMod x y
   | isReal x
   = error $ "SBV.polyDivMod: Received a real value: " ++ show x
   | not (isBounded x)
   = error $ "SBV.polyDivMod: Received infinite precision value: " ++ show x
   | True
   = ite (y .== 0) (0, x) (adjust d, adjust r)
   where adjust xs = fromBitsLE $ genericTake sz $ xs ++ repeat false
         sz        = intSizeOf x
         (d, r)    = mdp (blastLE x) (blastLE y)

-- conservative over-approximation of the degree
degree :: [SBool] -> Int
degree xs = walk (length xs - 1) $ reverse xs
  where walk n []     = n
        walk n (b:bs)
         | Just t <- unliteral b
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
               ys' = replicate degQuot false ++ ys
               (qs, rs) = divx (degQuot+1) degTop xs ys'

-- return the element at index i; if not enough elements, return false
-- N.B. equivalent to '(xs ++ repeat false) !! i', but more efficient
idx :: [SBool] -> Int -> SBool
idx []     _ = false
idx (x:_)  0 = x
idx (_:xs) i = idx xs (i-1)

divx :: Int -> Int -> [SBool] -> [SBool] -> ([SBool], [SBool])
divx n _ xs _ | n <= 0 = ([], xs)
divx n i xs ys'        = (q:qs, rs)
  where q        = xs `idx` i
        xs'      = ites q (xs `addPoly` ys') xs
        (qs, rs) = divx (n-1) (i-1) xs' (tail ys')

-- | Compute CRCs over bit-vectors. The call @crcBV n m p@ computes
-- the CRC of the message @m@ with respect to polynomial @p@. The
-- inputs are assumed to be blasted big-endian. The number
-- @n@ specifies how many bits of CRC is needed. Note that @n@
-- is actually the degree of the polynomial @p@, and thus it seems
-- redundant to pass it in. However, in a typical proof context,
-- the polynomial can be symbolic, so we cannot compute the degree
-- easily. While this can be worked-around by generating code that
-- accounts for all possible degrees, the resulting code would
-- be unnecessarily big and complicated, and much harder to reason
-- with. (Also note that a CRC is just the remainder from the
-- polynomial division, but this routine is much faster in practice.)
--
-- NB. The @n@th bit of the polynomial @p@ /must/ be set for the CRC
-- to be computed correctly. Note that the polynomial argument 'p' will
-- not even have this bit present most of the time, as it will typically
-- contain bits @0@ through @n-1@ as usual in the CRC literature. The higher
-- order @n@th bit is simply assumed to be set, as it does not make
-- sense to use a polynomial of a lesser degree. This is usually not a problem
-- since CRC polynomials are designed and expressed this way.
--
-- NB. The literature on CRC's has many variants on how CRC's are computed.
-- We follow the painless guide (<http://www.ross.net/crc/download/crc_v3.txt>)
-- and compute the CRC as follows:
--
--     * Extend the message 'm' by adding 'n' 0 bits on the right
--
--     * Divide the polynomial thus obtained by the 'p'
--
--     * The remainder is the CRC value.
--
-- There are many variants on final XOR's, reversed polynomials etc., so
-- it is essential to double check you use the correct /algorithm/.
crcBV :: Int -> [SBool] -> [SBool] -> [SBool]
crcBV n m p = take n $ go (replicate n false) (m ++ replicate n false)
  where mask = drop (length p - n) p
        go c []     = c
        go c (b:bs) = go next bs
          where c' = drop 1 c ++ [b]
                next = ite (head c) (zipWith (<+>) c' mask) c'

-- | Compute CRC's over polynomials, i.e., symbolic words. The first
-- 'Int' argument plays the same role as the one in the 'crcBV' function.
crc :: (FromBits (SBV a), FromBits (SBV b), Num a, Num b, Bits a, Bits b, SymWord a, SymWord b) => Int -> SBV a -> SBV b -> SBV b
crc n m p
  | isReal m || isReal p
  = error $ "SBV.crc: Received a real value: " ++ show (m, p)
  | not (isBounded m) || not (isBounded p)
  = error $ "SBV.crc: Received an infinite precision value: " ++ show (m, p)
  | True
  = fromBitsBE $ replicate (sz - n) false ++ crcBV n (blastBE m) (blastBE p)
  where sz = intSizeOf p
