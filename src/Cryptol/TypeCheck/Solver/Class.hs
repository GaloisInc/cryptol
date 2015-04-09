-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Solving class constraints.

{-# LANGUAGE PatternGuards #-}
module Cryptol.TypeCheck.Solver.Class (classStep, expandProp) where

import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.InferTypes(Goal(..))


-- | Solve class constraints.
-- If not, then we return 'Nothing'.
-- If solved, ther we return 'Just' a list of sub-goals.
classStep :: Goal -> Maybe [Goal]
classStep g = case goal g of
  TCon (PC PArith) [ty] -> solveArithInst g (tNoUser ty)
  TCon (PC PCmp) [ty]   -> solveCmpInst g   (tNoUser ty)
  _                     -> Nothing

-- | Solve an original goal in terms of the give sub-goals.
solved :: Goal -> [Prop] -> Maybe [Goal]
solved g ps = Just [ g { goal = p } | p <- ps ]

-- | Solve an Arith constraint by instance, if possible.
solveArithInst :: Goal -> Type -> Maybe [Goal]
solveArithInst g ty = case ty of

  -- Arith [n]e
  TCon (TC TCSeq) [n, e] -> solveArithSeq g n e

  -- Arith b => Arith (a -> b)
  TCon (TC TCFun) [_,b] -> solved g [ pArith b ]

  -- (Arith a, Arith b) => Arith (a,b)
  TCon (TC (TCTuple _)) es -> solved g [ pArith e | e <- es ]

  -- (Arith a, Arith b) => Arith { x1 : a, x2 : b }
  TRec fs -> solved g [ pArith ety | (_,ety) <- fs ]

  _ -> Nothing

-- | Solve an Arith constraint for a sequence.  The type passed here is the
-- element type of the sequence.
solveArithSeq :: Goal -> Type -> Type -> Maybe [Goal]
solveArithSeq g n ty = case ty of

  -- fin n => Arith [n]Bit
  TCon (TC TCBit) [] -> solved g [ pFin n ]

  -- variables are not solvable.
  TVar {} -> Nothing

  -- Arith ty => Arith [n]ty
  _ -> solved g [ pArith ty ]


-- | Solve Cmp constraints.
solveCmpInst :: Goal -> Type -> Maybe [Goal]
solveCmpInst g ty = case ty of

  -- Cmp Bit
  TCon (TC TCBit) [] -> solved g []

  -- (fin n, Cmp a) => Cmp [n]a
  TCon (TC TCSeq) [n,a] -> solved g [ pFin n, pCmp a ]

  -- (Cmp a, Cmp b) => Cmp (a,b)
  TCon (TC (TCTuple _)) es -> solved g (map pCmp es)

  -- (Cmp a, Cmp b) => Cmp { x:a, y:b }
  TRec fs -> solved g [ pCmp e | (_,e) <- fs ]

  _ -> Nothing


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



