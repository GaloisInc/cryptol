-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.BitVectors.AlgReals
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Algrebraic reals in Haskell.
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.SBV.BitVectors.AlgReals (AlgReal(..), mkPolyReal, algRealToSMTLib2, algRealToHaskell, mergeAlgReals, isExactRational, algRealStructuralEqual, algRealStructuralCompare) where

import Data.List       (sortBy, isPrefixOf, partition)
import Data.Ratio      ((%), numerator, denominator)
import Data.Function   (on)
import System.Random
import Test.QuickCheck (Arbitrary(..))

-- | Algebraic reals. Note that the representation is left abstract. We represent
-- rational results explicitly, while the roots-of-polynomials are represented
-- implicitly by their defining equation
data AlgReal = AlgRational Bool Rational          -- bool says it's exact (i.e., SMT-solver did not return it with ? at the end.)
             | AlgPolyRoot (Integer,  Polynomial) -- which root
                           (Maybe String)         -- approximate decimal representation with given precision, if available

-- | Check wheter a given argument is an exact rational
isExactRational :: AlgReal -> Bool
isExactRational (AlgRational True _) = True
isExactRational _                    = False

-- | A univariate polynomial, represented simply as a
-- coefficient list. For instance, "5x^3 + 2x - 5" is
-- represented as [(5, 3), (2, 1), (-5, 0)]
newtype Polynomial = Polynomial [(Integer, Integer)]
                   deriving (Eq, Ord)

-- | Construct a poly-root real with a given approximate value (either as a decimal, or polynomial-root)
mkPolyReal :: Either (Bool, String) (Integer, [(Integer, Integer)]) -> AlgReal
mkPolyReal (Left (exact, str))
 = case (str, break (== '.') str) of
      ("", (_, _))    -> AlgRational exact 0
      (_, (x, '.':y)) -> AlgRational exact (read (x++y) % (10 ^ length y))
      (_, (x, _))     -> AlgRational exact (read x % 1)
mkPolyReal (Right (k, coeffs))
 = AlgPolyRoot (k, Polynomial (normalize coeffs)) Nothing
 where normalize :: [(Integer, Integer)] -> [(Integer, Integer)]
       normalize = merge . reverse . sortBy (compare `on` snd)
       merge []                     = []
       merge [x]                    = [x]
       merge ((a, b):r@((c, d):xs))
         | b == d                   = merge ((a+c, b):xs)
         | True                     = (a, b) : merge r

instance Show Polynomial where
  show (Polynomial xs) = chkEmpty (join (concat [term p | p@(_, x) <- xs, x /= 0])) ++ " = " ++ show c
     where c  = -1 * head ([k | (k, 0) <- xs] ++ [0])
           term ( 0, _) = []
           term ( 1, 1) = [ "x"]
           term ( 1, p) = [ "x^" ++ show p]
           term (-1, 1) = ["-x"]
           term (-1, p) = ["-x^" ++ show p]
           term (k,  1) = [show k ++ "x"]
           term (k,  p) = [show k ++ "x^" ++ show p]
           join []      = ""
           join (k:ks) = k ++ s ++ join ks
             where s = case ks of
                        []    -> ""
                        (y:_) | "-" `isPrefixOf` y -> ""
                              | "+" `isPrefixOf` y -> ""
                              | True               -> "+"
           chkEmpty s = if null s then "0" else s

instance Show AlgReal where
  show (AlgRational exact a)         = showRat exact a
  show (AlgPolyRoot (i, p) mbApprox) = "root(" ++ show i ++ ", " ++ show p ++ ")" ++ maybe "" app mbApprox
     where app v | last v == '?' = " = " ++ init v ++ "..."
                 | True          = " = " ++ v

-- lift unary op through an exact rational, otherwise bail
lift1 :: String -> (Rational -> Rational) -> AlgReal -> AlgReal
lift1 _  o (AlgRational e a) = AlgRational e (o a)
lift1 nm _ a                 = error $ "AlgReal." ++ nm ++ ": unsupported argument: " ++ show a

-- lift binary op through exact rationals, otherwise bail
lift2 :: String -> (Rational -> Rational -> Rational) -> AlgReal -> AlgReal -> AlgReal
lift2 _  o (AlgRational True a) (AlgRational True b) = AlgRational True (a `o` b)
lift2 nm _ a                    b                    = error $ "AlgReal." ++ nm ++ ": unsupported arguments: " ++ show (a, b)

-- The idea in the instances below is that we will fully support operations
-- on "AlgRational" AlgReals, but leave everything else undefined. When we are
-- on the Haskell side, the AlgReal's are *not* reachable. They only represent
-- return values from SMT solvers, which we should *not* need to manipulate.
instance Eq AlgReal where
  AlgRational True a == AlgRational True b = a == b
  a                  == b                  = error $ "AlgReal.==: unsupported arguments: " ++ show (a, b)

instance Ord AlgReal where
  AlgRational True a `compare` AlgRational True b = a `compare` b
  a                  `compare` b                  = error $ "AlgReal.compare: unsupported arguments: " ++ show (a, b)

-- | Structural equality for AlgReal; used when constants are Map keys
algRealStructuralEqual   :: AlgReal -> AlgReal -> Bool
AlgRational a b `algRealStructuralEqual` AlgRational c d = (a, b) == (c, d)
AlgPolyRoot a b `algRealStructuralEqual` AlgPolyRoot c d = (a, b) == (c, d)
_               `algRealStructuralEqual` _               = False

-- | Structural comparisons for AlgReal; used when constants are Map keys
algRealStructuralCompare :: AlgReal -> AlgReal -> Ordering
AlgRational a b `algRealStructuralCompare` AlgRational c d = (a, b) `compare` (c, d)
AlgRational _ _ `algRealStructuralCompare` AlgPolyRoot _ _ = LT
AlgPolyRoot _ _ `algRealStructuralCompare` AlgRational _ _ = GT
AlgPolyRoot a b `algRealStructuralCompare` AlgPolyRoot c d = (a, b) `compare` (c, d)

instance Num AlgReal where
  (+)         = lift2 "+"      (+)
  (*)         = lift2 "*"      (*)
  (-)         = lift2 "-"      (-)
  negate      = lift1 "negate" negate
  abs         = lift1 "abs"    abs
  signum      = lift1 "signum" signum
  fromInteger = AlgRational True . fromInteger

instance Fractional AlgReal where
  (/)          = lift2 "/" (/)
  fromRational = AlgRational True

instance Real AlgReal where
  toRational (AlgRational True v) = v
  toRational x                    = error $ "AlgReal.toRational: Argument cannot be represented as a rational value: " ++ algRealToHaskell x

instance Random Rational where
  random g = let (a, g')  = random g
                 (b, g'') = random g'
             in (a % b, g'')
  -- this may not be quite kosher, but will do for our purposes (test-generation, mainly)
  randomR (l, h) g = let (ln, ld) = (numerator l, denominator l)
                         (hn, hd) = (numerator h, denominator h)
                         (a, g')  = randomR (ln*hd, hn*ld) g
                     in (a % (ld * hd), g')

instance Random AlgReal where
  random g = let (a, g') = random g in (AlgRational True a, g')
  randomR (AlgRational True l, AlgRational True h) g = let (a, g') = randomR (l, h) g in (AlgRational True a, g')
  randomR lh                                       _ = error $ "AlgReal.randomR: unsupported bounds: " ++ show lh

-- | Render an 'AlgReal' as an SMTLib2 value. Only supports rationals for the time being.
algRealToSMTLib2 :: AlgReal -> String
algRealToSMTLib2 (AlgRational True r)
   | m == 0 = "0.0"
   | m < 0  = "(- (/ "  ++ show (abs m) ++ ".0 " ++ show n ++ ".0))"
   | True   =    "(/ "  ++ show m       ++ ".0 " ++ show n ++ ".0)"
  where (m, n) = (numerator r, denominator r)
algRealToSMTLib2 r@(AlgRational False _)
   = error $ "SBV: Unexpected inexact rational to be converted to SMTLib2: " ++ show r
algRealToSMTLib2 (AlgPolyRoot (i, Polynomial xs) _) = "(root-obj (+ " ++ unwords (concatMap term xs) ++ ") " ++ show i ++ ")"
  where term (0, _) = []
        term (k, 0) = [coeff k]
        term (1, 1) = ["x"]
        term (1, p) = ["(^ x " ++ show p ++ ")"]
        term (k, 1) = ["(* " ++ coeff k ++ " x)"]
        term (k, p) = ["(* " ++ coeff k ++ " (^ x " ++ show p ++ "))"]
        coeff n | n < 0 = "(- " ++ show (abs n) ++ ")"
                | True  = show n

-- | Render an 'AlgReal' as a Haskell value. Only supports rationals, since there is no corresponding
-- standard Haskell type that can represent root-of-polynomial variety.
algRealToHaskell :: AlgReal -> String
algRealToHaskell (AlgRational True r) = "((" ++ show r ++ ") :: Rational)"
algRealToHaskell r                    = error $ "SBV.algRealToHaskell: Unsupported argument: " ++ show r

-- Try to show a rational precisely if we can, with finite number of
-- digits. Otherwise, show it as a rational value.
showRat :: Bool -> Rational -> String
showRat exact r = p $ case f25 (denominator r) [] of
                       Nothing               -> show r   -- bail out, not precisely representable with finite digits
                       Just (noOfZeros, num) -> let present = length num
                                                in neg $ case noOfZeros `compare` present of
                                                           LT -> let (b, a) = splitAt (present - noOfZeros) num in b ++ "." ++ if null a then "0" else a
                                                           EQ -> "0." ++ num
                                                           GT -> "0." ++ replicate (noOfZeros - present) '0' ++ num
  where p   = if exact then id else (++ "...")
        neg = if r < 0 then ('-':) else id
        -- factor a number in 2's and 5's if possible
        -- If so, it'll return the number of digits after the zero
        -- to reach the next power of 10, and the numerator value scaled
        -- appropriately and shown as a string
        f25 :: Integer -> [Integer] -> Maybe (Int, String)
        f25 1 sofar = let (ts, fs)   = partition (== 2) sofar
                          [lts, lfs] = map length [ts, fs]
                          noOfZeros  = lts `max` lfs
                      in Just (noOfZeros, show (abs (numerator r)  * factor ts fs))
        f25 v sofar = let (q2, r2) = v `quotRem` 2
                          (q5, r5) = v `quotRem` 5
                      in case (r2, r5) of
                           (0, _) -> f25 q2 (2 : sofar)
                           (_, 0) -> f25 q5 (5 : sofar)
                           _      -> Nothing
        -- compute the next power of 10 we need to get to
        factor []     fs     = product [2 | _ <- fs]
        factor ts     []     = product [5 | _ <- ts]
        factor (_:ts) (_:fs) = factor ts fs

-- | Merge the representation of two algebraic reals, one assumed to be
-- in polynomial form, the other in decimal. Arguments can be the same
-- kind, so long as they are both rationals and equivalent; if not there
-- must be one that is precise. It's an error to pass anything
-- else to this function! (Used in reconstructing SMT counter-example values with reals).
mergeAlgReals :: String -> AlgReal -> AlgReal -> AlgReal
mergeAlgReals _ f@(AlgRational exact r) (AlgPolyRoot kp Nothing)
  | exact = f
  | True  = AlgPolyRoot kp (Just (showRat False r))
mergeAlgReals _ (AlgPolyRoot kp Nothing) f@(AlgRational exact r)
  | exact = f
  | True  = AlgPolyRoot kp (Just (showRat False r))
mergeAlgReals _ f@(AlgRational e1 r1) s@(AlgRational e2 r2)
  | (e1, r1) == (e2, r2) = f
  | e1                   = f
  | e2                   = s
mergeAlgReals m _ _ = error m

-- Quickcheck instance
instance Arbitrary AlgReal where
  arbitrary = AlgRational True `fmap` arbitrary
