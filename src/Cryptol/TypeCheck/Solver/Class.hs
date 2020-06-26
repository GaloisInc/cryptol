-- |
-- Module      :  Cryptol.TypeCheck.Solver.Class
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Solving class constraints.

{-# LANGUAGE PatternGuards, OverloadedStrings #-}
module Cryptol.TypeCheck.Solver.Class
  ( solveZeroInst
  , solveLogicInst
  , solveRingInst
  , solveFieldInst
  , solveIntegralInst
  , solveRoundInst
  , solveEqInst
  , solveCmpInst
  , solveSignedCmpInst
  , solveLiteralInst
  , solveFLiteralInst
  , solveValidFloat
  ) where

import qualified LibBF as FP

import Cryptol.TypeCheck.Type
import Cryptol.TypeCheck.SimpType (tAdd,tWidth)
import Cryptol.TypeCheck.Solver.Types
import Cryptol.TypeCheck.PP
import Cryptol.Utils.RecordMap

{- | This places constraints on the floating point numbers that
we can work with.  This is a bit of an odd check, as it is really
a limitiation of the backend, and not the language itself.

On the other hand, it helps us give sane results if one accidentally
types a polymorphic float at the REPL.  Hopefully, most users will
stick to particular FP sizes, so this should be quite transparent.
-}
solveValidFloat :: Type -> Type -> Solved
solveValidFloat e p
  | Just _ <- knownSupportedFloat e p = SolvedIf []
  | otherwise = Unsolved

-- | Check that the type parameters correspond to a float that
-- we support, and if so make the precision settings for the BigFloat library.
knownSupportedFloat :: Type -> Type -> Maybe FP.BFOpts
knownSupportedFloat et pt
  | Just e <- tIsNum et, Just p <- tIsNum pt
  , minExp <= e && e <= maxExp && minPrec <= p && p <= maxPrec =
    Just (FP.expBits (fromInteger e) <> FP.precBits (fromInteger p)
                                     <> FP.allowSubnormal)
  | otherwise = Nothing
  where
  minExp  = max 2 (toInteger FP.expBitsMin)
  maxExp  = toInteger FP.expBitsMax

  minPrec = max 2 (toInteger FP.precBitsMin)
  maxPrec = toInteger FP.precBitsMax




-- | Solve a Zero constraint by instance, if possible.
solveZeroInst :: Type -> Solved
solveZeroInst ty = case tNoUser ty of

  -- Zero Error -> fails
  TCon (TError _ e) _ -> Unsolvable e

  -- Zero Bit
  TCon (TC TCBit) [] -> SolvedIf []

  -- Zero Integer
  TCon (TC TCInteger) [] -> SolvedIf []

  -- Zero (Z n)
  TCon (TC TCIntMod) [n] -> SolvedIf [ pFin n, n >== tOne ]

  -- Zero Real

  -- Zero Rational
  TCon (TC TCRational) [] -> SolvedIf []

  -- ValidVloat e p => Zero (Float e p)
  TCon (TC TCFloat) [e,p] -> SolvedIf [ pValidFloat e p ]

  -- Zero a => Zero [n]a
  TCon (TC TCSeq) [_, a] -> SolvedIf [ pZero a ]

  -- Zero b => Zero (a -> b)
  TCon (TC TCFun) [_, b] -> SolvedIf [ pZero b ]

  -- (Zero a, Zero b) => Zero (a,b)
  TCon (TC (TCTuple _)) es -> SolvedIf [ pZero e | e <- es ]

  -- (Zero a, Zero b) => Zero { x1 : a, x2 : b }
  TRec fs -> SolvedIf [ pZero ety | (_,ety) <- canonicalFields fs ]

  _ -> Unsolved

-- | Solve a Logic constraint by instance, if possible.
solveLogicInst :: Type -> Solved
solveLogicInst ty = case tNoUser ty of

  -- Logic Error -> fails
  TCon (TError _ e) _ -> Unsolvable e

  -- Logic Bit
  TCon (TC TCBit) [] -> SolvedIf []

  -- Logic a => Logic [n]a
  TCon (TC TCSeq) [_, a] -> SolvedIf [ pLogic a ]

  -- Logic b => Logic (a -> b)
  TCon (TC TCFun) [_, b] -> SolvedIf [ pLogic b ]

  -- (Logic a, Logic b) => Logic (a,b)
  TCon (TC (TCTuple _)) es -> SolvedIf [ pLogic e | e <- es ]

  -- (Logic a, Logic b) => Logic { x1 : a, x2 : b }
  TRec fs -> SolvedIf [ pLogic ety | (_,ety) <- canonicalFields fs ]

  _ -> Unsolved

-- | Solve a Ring constraint by instance, if possible.
solveRingInst :: Type -> Solved
solveRingInst ty = case tNoUser ty of

  -- Ring Error -> fails
  TCon (TError _ e) _ -> Unsolvable e

  -- Ring [n]e
  TCon (TC TCSeq) [n, e] -> solveRingSeq n e

  -- Ring b => Ring (a -> b)
  TCon (TC TCFun) [_,b] -> SolvedIf [ pRing b ]

  -- (Ring a, Ring b) => Arith (a,b)
  TCon (TC (TCTuple _)) es -> SolvedIf [ pRing e | e <- es ]

  -- Ring Bit fails
  TCon (TC TCBit) [] ->
    Unsolvable $ TCErrorMessage "Arithmetic cannot be done on individual bits."

  -- Ring Integer
  TCon (TC TCInteger) [] -> SolvedIf []

  -- Ring (Z n)
  TCon (TC TCIntMod) [n] -> SolvedIf [ pFin n, n >== tOne ]

  -- Ring Rational
  TCon (TC TCRational) [] -> SolvedIf []

  -- ValidFloat e p => Ring (Float e p)
  TCon (TC TCFloat) [e,p] -> SolvedIf [ pValidFloat e p ]

  -- (Ring a, Ring b) => Ring { x1 : a, x2 : b }
  TRec fs -> SolvedIf [ pRing ety | (_,ety) <- canonicalFields fs ]

  _ -> Unsolved


-- | Solve a Ring constraint for a sequence.  The type passed here is the
-- element type of the sequence.
solveRingSeq :: Type -> Type -> Solved
solveRingSeq n ty = case tNoUser ty of

  -- fin n => Ring [n]Bit
  TCon (TC TCBit) [] -> SolvedIf [ pFin n ]

  -- variables are not solvable.
  TVar {} -> case tNoUser n of
                {- We are sure that the lenght is not `fin`, so the
                special case for `Bit` does not apply.
                Arith ty => Arith [n]ty -}
                TCon (TC TCInf) [] -> SolvedIf [ pRing ty ]
                _                  -> Unsolved

  -- Ring ty => Ring [n]ty
  _ -> SolvedIf [ pRing ty ]


-- | Solve an Integral constraint by instance, if possible.
solveIntegralInst :: Type -> Solved
solveIntegralInst ty = case tNoUser ty of

  -- Integral Error -> fails
  TCon (TError _ e) _ -> Unsolvable e

  -- Integral Bit fails
  TCon (TC TCBit) [] ->
    Unsolvable $ TCErrorMessage "Arithmetic cannot be done on individual bits."

  -- Integral Integer
  TCon (TC TCInteger) [] -> SolvedIf []

  -- fin n => Integral [n]
  TCon (TC TCSeq) [n, elTy] ->
    case tNoUser elTy of
      TCon (TC TCBit) [] -> SolvedIf [ pFin n ]
      TVar _ -> Unsolved
      _ -> Unsolvable $ TCErrorMessage $ show
          $ "Type" <+> quotes (pp ty) <+> "is not an intergral type."

  TVar _ -> Unsolved

  _ -> Unsolvable $ TCErrorMessage $ show
          $ "Type" <+> quotes (pp ty) <+> "is not an intergral type."


-- | Solve a Field constraint by instance, if possible.
solveFieldInst :: Type -> Solved
solveFieldInst ty = case tNoUser ty of

  -- Field Error -> fails
  TCon (TError _ e) _ -> Unsolvable e

  -- Field Rational
  TCon (TC TCRational) [] -> SolvedIf []

  -- ValidFloat e p => Field (Float e p)
  TCon (TC TCFloat) [e,p] -> SolvedIf [ pValidFloat e p ]

  -- Field Real
  -- Field (Z n)
--  TCon (TC TCIntMod) [n] -> SolvedIf [ pFin n, n >== tOne, pPrime n ]

  _ -> Unsolved


-- | Solve a Round constraint by instance, if possible.
solveRoundInst :: Type -> Solved
solveRoundInst ty = case tNoUser ty of

  -- Round Error -> fails
  TCon (TError _ e) _ -> Unsolvable e

  -- Round Rational
  TCon (TC TCRational) [] -> SolvedIf []

  -- ValidFloat e p => Round (Float e p)
  TCon (TC TCFloat) [e,p] -> SolvedIf [ pValidFloat e p ]

  -- Round Real

  _ -> Unsolved



-- | Solve Eq constraints.
solveEqInst :: Type -> Solved
solveEqInst ty = case tNoUser ty of

  -- Eq Error -> fails
  TCon (TError _ e) _ -> Unsolvable e

  -- eq Bit
  TCon (TC TCBit) [] -> SolvedIf []

  -- Eq Integer
  TCon (TC TCInteger) [] -> SolvedIf []

  -- Eq Rational
  TCon (TC TCRational) [] -> SolvedIf []

  -- ValidFloat e p => Eq (Float e p)
  TCon (TC TCFloat) [e,p] -> SolvedIf [ pValidFloat e p ]

  -- Eq (Z n)
  TCon (TC TCIntMod) [n] -> SolvedIf [ pFin n, n >== tOne ]

  -- (fin n, Eq a) => Eq [n]a
  TCon (TC TCSeq) [n,a] -> SolvedIf [ pFin n, pEq a ]

  -- (Eq a, Eq b) => Eq (a,b)
  TCon (TC (TCTuple _)) es -> SolvedIf (map pEq es)

  -- Eq (a -> b) fails
  TCon (TC TCFun) [_,_] ->
    Unsolvable $ TCErrorMessage "Comparisons may not be performed on functions."

  -- (Eq a, Eq b) => Eq { x:a, y:b }
  TRec fs -> SolvedIf [ pEq e | (_,e) <- canonicalFields fs ]

  _ -> Unsolved


-- | Solve Cmp constraints.
solveCmpInst :: Type -> Solved
solveCmpInst ty = case tNoUser ty of

  -- Cmp Error -> fails
  TCon (TError _ e) _ -> Unsolvable e

  -- Cmp Bit
  TCon (TC TCBit) [] -> SolvedIf []

  -- Cmp Integer
  TCon (TC TCInteger) [] -> SolvedIf []

  -- Cmp Rational
  TCon (TC TCRational) [] -> SolvedIf []

  -- Cmp (Z n) fails
  TCon (TC TCIntMod) [_] ->
    Unsolvable $ TCErrorMessage "Values of Z_n type cannot be compared for order"

  -- ValidFloat e p => Cmp (Float e p)
  TCon (TC TCFloat) [e,p] -> SolvedIf [ pValidFloat e p ]

  -- (fin n, Cmp a) => Cmp [n]a
  TCon (TC TCSeq) [n,a] -> SolvedIf [ pFin n, pCmp a ]

  -- (Cmp a, Cmp b) => Cmp (a,b)
  TCon (TC (TCTuple _)) es -> SolvedIf (map pCmp es)

  -- Cmp (a -> b) fails
  TCon (TC TCFun) [_,_] ->
    Unsolvable $ TCErrorMessage "Comparisons may not be performed on functions."

  -- (Cmp a, Cmp b) => Cmp { x:a, y:b }
  TRec fs -> SolvedIf [ pCmp e | (_,e) <- canonicalFields fs ]

  _ -> Unsolved


-- | Solve a SignedCmp constraint for a sequence.  The type passed here is the
-- element type of the sequence.
solveSignedCmpSeq :: Type -> Type -> Solved
solveSignedCmpSeq n ty = case tNoUser ty of

  -- (fin n, n >=1 ) => SignedCmp [n]Bit
  TCon (TC TCBit) [] -> SolvedIf [ pFin n, n >== tNum (1 :: Integer) ]

  -- variables are not solvable.
  TVar {} -> Unsolved

  -- (fin n, SignedCmp ty) => SignedCmp [n]ty, when ty != Bit
  _ -> SolvedIf [ pFin n, pSignedCmp ty ]


-- | Solve SignedCmp constraints.
solveSignedCmpInst :: Type -> Solved
solveSignedCmpInst ty = case tNoUser ty of

  -- SignedCmp Error -> fails
  TCon (TError _ e) _ -> Unsolvable e

  -- SignedCmp Bit
  TCon (TC TCBit) [] -> Unsolvable $ TCErrorMessage "Signed comparisons may not be performed on bits"

  -- SignedCmp for sequences
  TCon (TC TCSeq) [n,a] -> solveSignedCmpSeq n a

  -- (SignedCmp a, SignedCmp b) => SignedCmp (a,b)
  TCon (TC (TCTuple _)) es -> SolvedIf (map pSignedCmp es)

  -- SignedCmp (a -> b) fails
  TCon (TC TCFun) [_,_] ->
    Unsolvable $ TCErrorMessage "Signed comparisons may not be performed on functions."

  -- (SignedCmp a, SignedCmp b) => SignedCmp { x:a, y:b }
  TRec fs -> SolvedIf [ pSignedCmp e | (_,e) <- canonicalFields fs ]

  _ -> Unsolved


-- | Solving fractional literal constraints.
solveFLiteralInst :: Type -> Type -> Type -> Type -> Solved
solveFLiteralInst numT denT rndT ty
  | TCon (TError _ e) _ <- tNoUser numT = Unsolvable e
  | TCon (TError _ e) _ <- tNoUser denT = Unsolvable e
  | tIsInf numT || tIsInf denT || tIsInf rndT =
    Unsolvable $ TCErrorMessage $ "Fractions may not use `inf`"
  | Just 0 <- tIsNum denT =
    Unsolvable $ TCErrorMessage
               $ "Fractions may not have 0 as the denominator."

  | otherwise =
    case tNoUser ty of
      TVar {} -> Unsolved

      TCon (TError _ e) _ -> Unsolvable e

      TCon (TC TCRational) [] -> SolvedIf []

      TCon (TC TCFloat) [e,p]
        | Just 0    <- tIsNum rndT -> SolvedIf [ pValidFloat e p ]
        | Just _    <- tIsNum rndT
        , Just opts <- knownSupportedFloat e p
        , Just n    <- tIsNum numT
        , Just d    <- tIsNum denT
         -> case FP.bfDiv opts (FP.bfFromInteger n) (FP.bfFromInteger d) of
              (_, FP.Ok) -> SolvedIf []
              _ -> Unsolvable $ TCErrorMessage
                              $ show n ++ "/" ++ show d ++ " cannot be " ++
                                "represented in " ++ show (pp ty)

        | otherwise -> Unsolved

      _ -> Unsolvable $ TCErrorMessage $ show
         $ "Type" <+> quotes (pp ty) <+> "does not support fractional literals."

-- | Solve Literal constraints.
solveLiteralInst :: Type -> Type -> Solved
solveLiteralInst val ty
  | TCon (TError _ e) _ <- tNoUser val = Unsolvable e
  | otherwise =
    case tNoUser ty of

      -- Literal n Error -> fails
      TCon (TError _ e) _ -> Unsolvable e

      -- (fin val) => Literal val Integer
      TCon (TC TCInteger) [] -> SolvedIf [ pFin val ]

      -- (fin val) => Literal val Rational
      TCon (TC TCRational) [] -> SolvedIf [ pFin val ]

      -- (fin val, fin m, m >= val + 1) => Literal val (Z m)
      TCon (TC TCIntMod) [modulus] ->
        SolvedIf [ pFin val, pFin modulus, modulus >== tAdd val tOne ]

      -- (fin bits, bits => width n) => Literal n [bits]
      TCon (TC TCSeq) [bits, elTy]
        | TCon (TC TCBit) [] <- ety ->
            SolvedIf [ pFin val, pFin bits, bits >== tWidth val ]
        | TVar _ <- ety -> Unsolved
        where ety = tNoUser elTy

      TVar _ -> Unsolved

      _ -> Unsolvable $ TCErrorMessage $ show
         $ "Type" <+> quotes (pp ty) <+> "does not support integer literals."


