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
  , solveArithInst
  , solveCmpInst
  , solveSignedCmpInst
  , solveLiteralInst
  , solveFLiteralInst
  , solveValidFloat
  , expandProp
  ) where

import qualified LibBF as FP

import Cryptol.TypeCheck.Type
import Cryptol.TypeCheck.SimpType (tAdd,tWidth)
import Cryptol.TypeCheck.Solver.Types
import Cryptol.TypeCheck.PP


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
    Just (FP.expBits (fromInteger e) <> FP.precBits (fromInteger p))
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

  -- ValieVloat e p => Zero (Float e p)
  TCon (TC TCFloat) [e,p] -> SolvedIf [ pValidFloat e p ]

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

  -- Arith (Float e p)
  TCon (TC TCFloat) [ e, p ] -> SolvedIf [ pValidFloat e p ]

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



-- | Solving fractional literal constraints.
solveFLiteralInst :: Type -> Type -> Type -> Solved
solveFLiteralInst numT denT ty
  | TCon (TError _ e) _ <- tNoUser numT = Unsolvable e
  | TCon (TError _ e) _ <- tNoUser denT = Unsolvable e
  | tIsInf numT || tIsInf denT =
    Unsolvable $ TCErrorMessage $ "Fractions may not use `inf`"
  | Just 0 <- tIsNum denT =
    Unsolvable $ TCErrorMessage
               $ "Fractions may not have 0 as the denominator."

  | otherwise =
    case tNoUser ty of
      TVar {} -> Unsolved

      TCon (TError _ e) _ -> Unsolvable e

      TCon (TC TCFloat) [e,p]
        | Just n    <- tIsNum numT
        , Just d    <- tIsNum denT
        , Just opts <- knownSupportedFloat e p ->
          case FP.bfDiv opts (FP.bfFromInteger n) (FP.bfFromInteger d) of
            (_,FP.Ok) -> SolvedIf []
            -- NOTE: this does not allow for subnormal numbers

            _ -> Unsolvable $ TCErrorMessage $ show $
                    integer n <.> "/" <.> integer d <+>
                    "cannot be represented in" <+> pp ty

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

      -- (fin val, fin m, m >= val + 1) => Literal val (Z m)
      TCon (TC TCIntMod) [modulus] ->
        SolvedIf [ pFin val, pFin modulus, modulus >== tAdd val tOne ]

      -- Literal f (Float e p)  is solved as long as the number fits
      TCon (TC TCFloat) [ et, pt ] ->
        case (tIsNum val, knownSupportedFloat et pt) of
          (Just n, Just opts) ->
            case FP.bfRoundFloat opts (FP.bfFromInteger n) of
              (_,FP.Ok) -> SolvedIf []
              _ -> Unsolvable $ TCErrorMessage $ show $
                   integer n <+> "cannot be represented in" <+> pp ty
          _ -> Unsolved

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



