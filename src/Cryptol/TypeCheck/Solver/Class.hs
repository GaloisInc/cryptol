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
  , solveCmpInst
  , solveSignedCmpInst
  , solveLiteralInst
  , expandProp
  ) where

import Cryptol.TypeCheck.Type
import Cryptol.TypeCheck.SimpType (tAdd,tWidth)
import Cryptol.TypeCheck.Solver.Types
import Cryptol.TypeCheck.PP


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

  -- Zero Rational
  -- Zero Real
  -- Zero Float

  -- Zero a => Zero [n]a
  TCon (TC TCSeq) [_, a] -> SolvedIf [ pZero a ]

  -- Zero b => Zero (a -> b)
  TCon (TC TCFun) [_, b] -> SolvedIf [ pZero b ]

  -- (Zero a, Zero b) => Zero (a,b)
  TCon (TC (TCTuple _)) es -> SolvedIf [ pZero e | e <- es ]

  -- (Zero a, Zero b) => Zero { x1 : a, x2 : b }
  TRec fs -> SolvedIf [ pZero ety | (_,ety) <- fs ]

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
  TRec fs -> SolvedIf [ pLogic ety | (_,ety) <- fs ]

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

  -- (Ring a, Ring b) => Arith { x1 : a, x2 : b }
  TRec fs -> SolvedIf [ pRing ety | (_,ety) <- fs ]

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

  -- Integral (Z n)
  TCon (TC TCIntMod) [n] -> SolvedIf [ pFin n, n >== tOne ]

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
  -- Field Real
  -- Field Float
  -- Field (Z n)
--  TCon (TC TCIntMod) [n] -> SolvedIf [ pFin n, n >== tOne, pPrime n ]

  _ -> Unsolved

-- | Solve a Round constraint by instance, if possible.
solveRoundInst :: Type -> Solved
solveRoundInst ty = case tNoUser ty of

  -- Round Error -> fails
  TCon (TError _ e) _ -> Unsolvable e

  -- Round Rational
  -- Round Real
  -- Round Float

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

  -- Cmp (Z n)
  TCon (TC TCIntMod) [n] -> SolvedIf [ pFin n, n >== tOne ]

  -- (fin n, Cmp a) => Cmp [n]a
  TCon (TC TCSeq) [n,a] -> SolvedIf [ pFin n, pCmp a ]

  -- (Cmp a, Cmp b) => Cmp (a,b)
  TCon (TC (TCTuple _)) es -> SolvedIf (map pCmp es)

  -- Cmp (a -> b) fails
  TCon (TC TCFun) [_,_] ->
    Unsolvable $ TCErrorMessage "Comparisons may not be performed on functions."

  -- (Cmp a, Cmp b) => Cmp { x:a, y:b }
  TRec fs -> SolvedIf [ pCmp e | (_,e) <- fs ]

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
  TRec fs -> SolvedIf [ pSignedCmp e | (_,e) <- fs ]

  _ -> Unsolved


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
         $ "Type" <+> quotes (pp ty) <+> "does not support literals."


-- | Add propositions that are implied by the given one.
-- The result contains the orignal proposition, and maybe some more.
expandProp :: Prop -> [Prop]
expandProp prop =
  prop : subclasses ++ substructure

  where
  subclasses =
    case tNoUser prop of
      TCon (PC pc) [ty] ->
        case pc of
          -- Ring a => Zero a
          PRing     -> expandProp (pZero ty)

          -- Logic a => Zero a
          PLogic    -> expandProp (pZero ty)

          -- Integral a => Ring a
          PIntegral -> expandProp (pRing ty)

          -- Field a => Ring a
          PField    -> expandProp (pRing ty)

          -- Round a => (Cmp a, Field a)
          PRound    -> expandProp (pCmp ty) ++ expandProp (pField ty)
          _ -> []
      _ -> []

  substructure =
    case tNoUser prop of

      TCon (PC pc) [ty] ->
        case (pc, tNoUser ty) of

          -- Logic [n]a => Logic a
          (PLogic, TCon (TC TCSeq) [_n,a]) -> expandProp (pLogic a)

          -- Logic (a -> b) => Logic b
          (PLogic, TCon (TC TCFun) [_a,b]) -> expandProp (pLogic b)

          -- Logic (a,b) => (Logic a, Logic b)
          (PLogic, TCon (TC (TCTuple _)) ts) -> concatMap (expandProp . pLogic) ts

          -- Logic { x1 : a, x2 : b } => (Logic a, Logic b)
          (PLogic, TRec fs) -> concatMap (expandProp . pLogic . snd) fs

          -- Ring [n]Bit => fin n
          -- (Ring [n]a, a/=Bit) => Ring a
          (PRing, TCon (TC TCSeq) [n,a])
            | TCon (TC TCBit) _ <- ty1  -> [pFin n]
            | TCon _ _          <- ty1  -> expandProp (pRing ty1)
            | TRec {}           <- ty1  -> expandProp (pRing ty1)
            where
            ty1 = tNoUser a

          -- Ring (a -> b) => Ring b
          (PRing, TCon (TC TCFun) [_,b]) -> expandProp (pRing b)

          -- Ring (a,b) => (Ring a, Ring b)
          (PRing, TCon (TC (TCTuple _)) ts) -> concatMap (expandProp . pRing) ts

          -- Ring { x1 : a, x2 : b } => (Ring a, Ring b)
          (PRing, TRec fs) -> concatMap (expandProp . pRing. snd) fs

          -- Cmp [n]a => (fin n, Cmp a)
          (PCmp, TCon (TC TCSeq) [n,a]) -> pFin n : expandProp (pCmp a)

          -- Cmp (a,b) => (Cmp a, Cmp b)
          (PCmp, TCon (TC (TCTuple _)) ts) -> concatMap (expandProp . pCmp) ts

          -- Cmp { x:a, y:b } => (Cmp a, Cmp b)
          (PCmp, TRec fs) -> concatMap (expandProp . pCmp . snd) fs

          -- SignedCmp [n]Bit => (fin n, n >= 1)
          -- (SignedCmp [n]a, a /= Bit) => SignedCmp a
          (PSignedCmp, TCon (TC TCSeq) [n,a])
            | TCon (TC TCBit) _ <- ty1 -> [pFin n, n >== tOne]
            | TCon _ _          <- ty1 -> expandProp (pSignedCmp ty1)
            | TRec {}           <- ty1 -> expandProp (pSignedCmp ty1)
            where
            ty1 = tNoUser a

          -- SignedCmp (a,b) => (SignedCmp a, SignedCmp b)
          (PSignedCmp, TCon (TC (TCTuple _)) ts) -> concatMap (expandProp . pSignedCmp) ts

          -- Cmp { x:a, y:b } => (Cmp a, Cmp b)
          (PSignedCmp, TRec fs) -> concatMap (expandProp . pSignedCmp . snd) fs

          _ -> []

      _ -> []
