-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- This module defines intervals and interval arithmetic.

{-# LANGUAGE Safe #-}
module Cryptol.TypeCheck.Solver.Interval
  ( Interval(..)
  , anything
  , iConst

  , iAdd, iMul, iExp
  , iMin, iMax
  , iLg2, iWidth

  , iSub, iDiv, iMod

  , iLenFromThen, iLenFromTo, iLenFromThenTo

  , iLeq, iLt, iDisjoint
  ) where


import Cryptol.TypeCheck.Solver.InfNat


{- | Representation of intervals.
Intervals always include the lower bound.
Intervals include the upper bound if:
  * either the upper bound is finite, or
  * the upper bound is 'Inf' and @isFinite == False@.

Invariant: if the upper bound is finite, then `isFinite == True`.

> [x,y]     Interval (Nat x) (Nat y) True
> [x,inf]   Interval (Nat x) Inf     False
> [x,inf)   Interval (Nat x) Inf     True

-}
data Interval = Interval
  { lowerBound     :: Nat'  -- ^ Lower bound
  , upperBound     :: Nat'  -- ^ Upper bound
  , isFinite       :: Bool  -- ^ Do we know this to be a finite value.
      -- Note that for @[inf,inf]@ this field is `False`
      -- (i.e., this field is not talking about the size of the interval,
      -- but, rather, about if it contains infinity).
  } deriving Show

-- | Any possible value.
anything :: Interval
anything = Interval { lowerBound = Nat 0
                    , upperBound = Inf
                    , isFinite   = False
                    }

anyFinite :: Interval
anyFinite = anything { isFinite = True }

iConst :: Nat' -> Interval
iConst x = Interval { lowerBound = x, upperBound = x, isFinite = x < Inf }

iAdd :: Interval -> Interval -> Interval
iAdd = liftMono2 nAdd (&&)

iMul :: Interval -> Interval -> Interval
iMul = liftMono2 nMul (&&)

iMin :: Interval -> Interval -> Interval
iMin = liftMono2 nMin (||)

iMax :: Interval -> Interval -> Interval
iMax = liftMono2 nMax (&&)

iLg2 :: Interval -> Interval
iLg2 = liftMono1 nLg2

iWidth :: Interval -> Interval
iWidth = liftMono1 nWidth


iExp :: Interval -> Interval -> Interval
iExp i1 i2 = fixUp (liftMono2 nExp (&&) i1 i2)
  where
  -- exp k : is a monotonic function for k >= 1
  -- exp 0 : is a monotonic from 1 onwards
  -- Example of why we need fixing, consdier:
  -- [0,0] ^ [0,5]
  -- Monotonic computation results in:
  -- [1,0]
  fixUp i3
    | lowerBound i1 == Nat 0 &&
      lowerBound i2 == Nat 0 &&
      upperBound i2 >= Nat 1 =
        Interval { lowerBound = Nat 0
                 , upperBound = nMax (Nat 1) (upperBound i3)
                 , isFinite   = isFinite i3
                 }
  fixUp i3 = i3


iSub :: Interval -> Interval -> Interval
iSub = liftPosNeg nSub

iDiv :: Interval -> Interval -> Interval
iDiv = liftPosNeg nDiv

iMod :: Interval -> Interval -> Interval
iMod _ i2 = Interval { lowerBound = Nat 0
                     , upperBound = case upperBound i2 of
                                      Inf   -> Inf
                                      Nat n -> Nat (n - 1)
                     , isFinite   = True -- we never have infinite reminder.
                     }

-- XXX
iLenFromThen :: Interval -> Interval -> Interval -> Interval
iLenFromThen _ _ _ = anyFinite

-- XXX
iLenFromTo :: Interval -> Interval -> Interval
iLenFromTo _ _ = anyFinite

-- XXX
iLenFromThenTo :: Interval -> Interval -> Interval -> Interval
iLenFromThenTo _ _ _ = anyFinite




-- | The first interval is definiately smaller
iLeq :: Interval -> Interval -> Bool
iLeq i1 i2 = upperBound i1 <= lowerBound i2

-- | The first interval is definiately smaller
iLt :: Interval -> Interval -> Bool
iLt i1 i2 = upperBound i1 < lowerBound i2
         || (isFinite i1 && lowerBound i2 == Inf)

-- | The two intervals do not overlap.
iDisjoint :: Interval -> Interval -> Bool
iDisjoint i1 i2 = iLt i1 i2 || iLt i2 i1


--------------------------------------------------------------------------------


liftMono1 :: (Nat' -> Nat')     -- ^ Binary monotonic fun. to lift
          -> Interval -> Interval
liftMono1 f i =
  let u = f (upperBound i)
  in Interval { lowerBound = f (lowerBound i)
              , upperBound = u
              , isFinite   = mkFin (isFinite i) u
              }

liftMono2 :: (Nat' -> Nat' -> Nat')     -- ^ Binary monotonic fun. to lift
          -> (Bool -> Bool -> Bool)     -- ^ Compute finitneness
          -> Interval -> Interval -> Interval
liftMono2 f isF i1 i2 =
  let u = f (upperBound i1) (upperBound i2)
  in Interval { lowerBound = f (lowerBound i1) (lowerBound i2)
              , upperBound = u
              , isFinite   = mkFin (isF (isFinite i1) (isFinite i2)) u
              }


-- For div and sub, increase in first argument, decrease in second.
liftPosNeg :: (Nat' -> Nat' -> Maybe Nat')
           -> Interval -> Interval -> Interval
liftPosNeg f i1 i2 =
  Interval { lowerBound = case f (lowerBound i1) (upperBound i2) of
                            Nothing -> Nat 0
                            Just n  -> n
          , upperBound  = case f (upperBound i1) (lowerBound i2) of
                            Just n  -> n
                            Nothing -> upperBound i1
          , isFinite    = isFinite i1
          }

mkFin :: Bool -> Nat' -> Bool
mkFin ifInf ub = case ub of
                   Nat _ -> True
                   Inf   -> ifInf


