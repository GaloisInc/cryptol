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
  ( classStep
  , solveZeroInst
  , solveLogicInst
  , solveArithInst
  , solveCmpInst
  , solveSignedCmpInst
  , solveLiteralInst
  , expandProp
  ) where

import Cryptol.TypeCheck.Type
import Cryptol.TypeCheck.SimpType (tAdd,tWidth)
import Cryptol.TypeCheck.Solver.Types
import Cryptol.TypeCheck.PP

-- | Solve class constraints.
-- If not, then we return 'Nothing'.
-- If solved, then we return 'Just' a list of sub-goals.
classStep :: Prop -> Solved
classStep p = case tNoUser p of
  TCon (PC PLogic) [ty] -> solveLogicInst (tNoUser ty)
  TCon (PC PArith) [ty] -> solveArithInst (tNoUser ty)
  TCon (PC PCmp) [ty]   -> solveCmpInst   (tNoUser ty)
  _                     -> Unsolved

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

-- | Solve an Arith constraint by instance, if possible.
solveArithInst :: Type -> Solved
solveArithInst ty = case tNoUser ty of

  -- Arith Error -> fails
  TCon (TError _ e) _ -> Unsolvable e

  -- Arith [n]e
  TCon (TC TCSeq) [n, e] -> solveArithSeq n e

  -- Arith b => Arith (a -> b)
  TCon (TC TCFun) [_,b] -> SolvedIf [ pArith b ]

  -- (Arith a, Arith b) => Arith (a,b)
  TCon (TC (TCTuple _)) es -> SolvedIf [ pArith e | e <- es ]

  -- Arith Bit fails
  TCon (TC TCBit) [] ->
    Unsolvable $ TCErrorMessage "Arithmetic cannot be done on individual bits."

  -- Arith Integer
  TCon (TC TCInteger) [] -> SolvedIf []

  -- Arith (Z n)
  TCon (TC TCIntMod) [n] -> SolvedIf [ pFin n, n >== tOne ]

  -- (Arith a, Arith b) => Arith { x1 : a, x2 : b }
  TRec fs -> SolvedIf [ pArith ety | (_,ety) <- fs ]

  _ -> Unsolved

-- | Solve an Arith constraint for a sequence.  The type passed here is the
-- element type of the sequence.
solveArithSeq :: Type -> Type -> Solved
solveArithSeq n ty = case tNoUser ty of

  -- fin n => Arith [n]Bit
  TCon (TC TCBit) [] -> SolvedIf [ pFin n ]

  -- variables are not solvable.
  TVar {} -> case tNoUser n of
                {- We are sure that the lenght is not `fin`, so the
                special case for `Bit` does not apply.
                Arith ty => Arith [n]ty -}
                TCon (TC TCInf) [] -> SolvedIf [ pArith ty ]
                _                  -> Unsolved

  -- Arith ty => Arith [n]ty
  _ -> SolvedIf [ pArith ty ]


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
  prop :
  case tNoUser prop of

    TCon (PC pc) [ty] ->
      case (pc, tNoUser ty) of

        -- Arith [n]Bit => fin n
        -- (Arith [n]a, a/=Bit) => Arith a
        (PArith, TCon (TC TCSeq) [n,a])
          | TCon (TC TCBit) _ <- ty1  -> [pFin n]
          | TCon _ _          <- ty1  -> expandProp (pArith ty1)
          | TRec {}           <- ty1  -> expandProp (pArith ty1)
          where
          ty1 = tNoUser a

        -- Arith (a -> b) => Arith b
        (PArith, TCon (TC TCFun) [_,b]) -> expandProp (pArith b)

        -- Arith (a,b) => (Arith a, Arith b)
        (PArith, TCon (TC (TCTuple _)) ts) -> concatMap (expandProp . pArith) ts

        -- Arith { x1 : a, x2 : b } => (Arith a, Arith b)
        (PArith, TRec fs) -> concatMap (expandProp . pArith. snd) fs

        -- Cmp [n]a => (fin n, Cmp a)
        (PCmp, TCon (TC TCSeq) [n,a]) -> pFin n : expandProp (pCmp a)

        -- Cmp (a,b) => (Cmp a, Cmp b)
        (PCmp, TCon (TC (TCTuple _)) ts) -> concatMap (expandProp . pCmp) ts

        -- Cmp { x:a, y:b } => (Cmp a, Cmp b)
        (PCmp, TRec fs) -> concatMap (expandProp . pCmp . snd) fs

        _ -> []

    _ -> []



