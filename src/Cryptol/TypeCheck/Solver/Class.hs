-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Solving class constraints.

{-# LANGUAGE PatternGuards #-}
module Cryptol.TypeCheck.Solver.Class
  ( classStep
  , solveArithInst
  , solveCmpInst
  , expandProp
  ) where

import Cryptol.TypeCheck.Type
import Cryptol.TypeCheck.Solver.Types

-- | Solve class constraints.
-- If not, then we return 'Nothing'.
-- If solved, ther we return 'Just' a list of sub-goals.
classStep :: Prop -> Solved
classStep p = case tNoUser p of
  TCon (PC PArith) [ty] -> solveArithInst (tNoUser ty)
  TCon (PC PCmp) [ty]   -> solveCmpInst   (tNoUser ty)
  _                     -> Unsolved

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
  TVar {} -> Unsolved

  -- Arith ty => Arith [n]ty
  _ -> SolvedIf [ pArith ty ]


-- | Solve Cmp constraints.
solveCmpInst :: Type -> Solved
solveCmpInst ty = case tNoUser ty of

  -- Cmp Error -> fails
  TCon (TError _ e) _ -> Unsolvable e

  -- Cmp Bit
  TCon (TC TCBit) [] -> SolvedIf []

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



