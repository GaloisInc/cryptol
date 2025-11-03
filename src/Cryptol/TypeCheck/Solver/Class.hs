-- |
-- Module      :  Cryptol.TypeCheck.Solver.Class
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Solving class constraints.
-- If you make changes to this file, please update the documenation in RefMan.md

{-# LANGUAGE PatternGuards #-}
module Cryptol.TypeCheck.Solver.Class
  ( solveDerivedInst
    -- * Built-in instances
    --
    -- $builtInInstances
  , solveZeroInst
  , solveLogicInst
  , solveRingInst
  , solveFieldInst
  , solveIntegralInst
  , solveRoundInst
  , solveEqInst
  , solveCmpInst
  , solveSignedCmpInst
  , solveLiteralInst
  , solveLiteralLessThanInst
  , solveFLiteralInst
  , solveValidFloat
  ) where

import qualified Data.Map as Map
import qualified LibBF as FP

import Cryptol.TypeCheck.Type hiding (tSub)
import Cryptol.TypeCheck.SimpType (tAdd,tSub,tWidth,tMax)
import Cryptol.TypeCheck.Solver.Types
import Cryptol.TypeCheck.Subst
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




-- | Solve a constraint on a nominal type by looking up its derived instance.
solveDerivedInst :: PC          -- ^ the typeclass (of kind @* -> Prop@)
                 -> NominalType -- ^ the type constructor
                 -> [Type]      -- ^ type arguments to the 'NominalType'
                 -> Solved
solveDerivedInst pc nt targs =
  case Map.lookup pc (ntDeriving nt) of
    Just conds ->
      -- The conditions saved in the type may refer to the type parameters, so
      -- we need to instantiate them with the type arguments.
      let conds' = apSubst (listParamSubst (zip (ntParams nt) targs)) conds
      -- apSubst calls simplify so it may return TError. In that case the
      -- constraint is unsolvable.
      in  if any tHasErrors conds' then Unsolvable else SolvedIf conds'
    Nothing -> Unsolvable

-- $builtInInstances
-- The functions below only solve for built-in instances. To solve for derived
-- instances, check first if the type is 'TNominal' and use 'solveDerivedInst'
-- in that case.

-- | Solve a Zero constraint by instance, if possible.
solveZeroInst :: Type -> Solved
solveZeroInst ty = case tNoUser ty of

  -- Zero Error -> fails
  TCon (TError {}) _ -> Unsolvable

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
  TRec fs -> SolvedIf [ pZero ety | ety <- recordElements fs ]

  _ -> Unsolved

-- | Solve a Logic constraint by instance, if possible.
solveLogicInst :: Type -> Solved
solveLogicInst ty = case tNoUser ty of

  -- Logic Error -> fails
  TCon (TError {}) _ -> Unsolvable

  -- Logic Bit
  TCon (TC TCBit) [] -> SolvedIf []

  -- Logic Integer fails
  TCon (TC TCInteger) [] -> Unsolvable

  -- Logic (Z n) fails
  TCon (TC TCIntMod) [_] -> Unsolvable

  -- Logic Rational fails
  TCon (TC TCRational) [] -> Unsolvable

  -- Logic (Float e p) fails
  TCon (TC TCFloat) [_, _] -> Unsolvable

  -- Logic a => Logic [n]a
  TCon (TC TCSeq) [_, a] -> SolvedIf [ pLogic a ]

  -- Logic b => Logic (a -> b)
  TCon (TC TCFun) [_, b] -> SolvedIf [ pLogic b ]

  -- (Logic a, Logic b) => Logic (a,b)
  TCon (TC (TCTuple _)) es -> SolvedIf [ pLogic e | e <- es ]

  -- (Logic a, Logic b) => Logic { x1 : a, x2 : b }
  TRec fs -> SolvedIf [ pLogic ety | ety <- recordElements fs ]

  _ -> Unsolved


-- | Solve a Ring constraint by instance, if possible.
solveRingInst :: Type -> Solved
solveRingInst ty = case tNoUser ty of

  -- Ring Error -> fails
  TCon (TError {}) _ -> Unsolvable

  -- Ring [n]e
  TCon (TC TCSeq) [n, e] -> solveRingSeq n e

  -- Ring b => Ring (a -> b)
  TCon (TC TCFun) [_,b] -> SolvedIf [ pRing b ]

  -- (Ring a, Ring b) => Arith (a,b)
  TCon (TC (TCTuple _)) es -> SolvedIf [ pRing e | e <- es ]

  -- Ring Bit fails
  TCon (TC TCBit) [] -> Unsolvable

  -- Ring Integer
  TCon (TC TCInteger) [] -> SolvedIf []

  -- Ring (Z n)
  TCon (TC TCIntMod) [n] -> SolvedIf [ pFin n, n >== tOne ]

  -- Ring Rational
  TCon (TC TCRational) [] -> SolvedIf []

  -- ValidFloat e p => Ring (Float e p)
  TCon (TC TCFloat) [e,p] -> SolvedIf [ pValidFloat e p ]

  -- (Ring a, Ring b) => Ring { x1 : a, x2 : b }
  TRec fs -> SolvedIf [ pRing ety | ety <- recordElements fs ]

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
  TCon (TError {}) _ -> Unsolvable

  -- Integral Bit fails
  TCon (TC TCBit) [] -> Unsolvable

  -- Integral Integer
  TCon (TC TCInteger) [] -> SolvedIf []

  -- fin n => Integral [n]
  TCon (TC TCSeq) [n, elTy] ->
    case tNoUser elTy of
      TCon (TC TCBit) [] -> SolvedIf [ pFin n ]
      TVar _ -> Unsolved
      _ -> Unsolvable

  TVar _ -> Unsolved

  _ -> Unsolvable


-- | Solve a Field constraint by instance, if possible.
solveFieldInst :: Type -> Solved
solveFieldInst ty = case tNoUser ty of

  -- Field Error -> fails
  TCon (TError {}) _ -> Unsolvable

  -- Field Bit fails
  TCon (TC TCBit) [] -> Unsolvable

  -- Field Integer fails
  TCon (TC TCInteger) [] -> Unsolvable

  -- Field Rational
  TCon (TC TCRational) [] -> SolvedIf []

  -- ValidFloat e p => Field (Float e p)
  TCon (TC TCFloat) [e,p] -> SolvedIf [ pValidFloat e p ]

  -- Field Real

  -- Field (Z n)
  TCon (TC TCIntMod) [n] -> SolvedIf [ pPrime n ]

  -- Field ([n]a) fails
  TCon (TC TCSeq) [_, _] -> Unsolvable

  -- Field (a -> b) fails
  TCon (TC TCFun) [_, _] -> Unsolvable

  -- Field (a, b, ...) fails
  TCon (TC (TCTuple _)) _ -> Unsolvable

  -- Field {x : a, y : b, ...} fails
  TRec _ -> Unsolvable

  -- Field <nominal> -> fails
  TNominal {} -> Unsolvable

  _ -> Unsolved


-- | Solve a Round constraint by instance, if possible.
solveRoundInst :: Type -> Solved
solveRoundInst ty = case tNoUser ty of

  -- Round Error -> fails
  TCon (TError {}) _ -> Unsolvable

  -- Round Bit fails
  TCon (TC TCBit) [] -> Unsolvable

  -- Round Integer fails
  TCon (TC TCInteger) [] -> Unsolvable

  -- Round (Z n) fails
  TCon (TC TCIntMod) [_] -> Unsolvable

  -- Round Rational
  TCon (TC TCRational) [] -> SolvedIf []

  -- ValidFloat e p => Round (Float e p)
  TCon (TC TCFloat) [e,p] -> SolvedIf [ pValidFloat e p ]

  -- Round Real

  -- Round ([n]a) fails
  TCon (TC TCSeq) [_, _] -> Unsolvable

  -- Round (a -> b) fails
  TCon (TC TCFun) [_, _] -> Unsolvable

  -- Round (a, b, ...) fails
  TCon (TC (TCTuple _)) _ -> Unsolvable

  -- Round {x : a, y : b, ...} fails
  TRec _ -> Unsolvable

  -- Round <nominal> -> fails
  TNominal {} -> Unsolvable

  _ -> Unsolved



-- | Solve Eq constraints.
solveEqInst :: Type -> Solved
solveEqInst ty = case tNoUser ty of

  -- Eq Error -> fails
  TCon (TError {}) _ -> Unsolvable

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
  TCon (TC TCFun) [_,_] -> Unsolvable

  -- (Eq a, Eq b) => Eq { x:a, y:b }
  TRec fs -> SolvedIf [ pEq e | e <- recordElements fs ]

  _ -> Unsolved


-- | Solve Cmp constraints.
solveCmpInst :: Type -> Solved
solveCmpInst ty = case tNoUser ty of

  -- Cmp Error -> fails
  TCon (TError {}) _ -> Unsolvable

  -- Cmp Bit
  TCon (TC TCBit) [] -> SolvedIf []

  -- Cmp Integer
  TCon (TC TCInteger) [] -> SolvedIf []

  -- Cmp Rational
  TCon (TC TCRational) [] -> SolvedIf []

  -- Cmp (Z n) fails
  TCon (TC TCIntMod) [_] -> Unsolvable

  -- ValidFloat e p => Cmp (Float e p)
  TCon (TC TCFloat) [e,p] -> SolvedIf [ pValidFloat e p ]

  -- (fin n, Cmp a) => Cmp [n]a
  TCon (TC TCSeq) [n,a] -> SolvedIf [ pFin n, pCmp a ]

  -- (Cmp a, Cmp b) => Cmp (a,b)
  TCon (TC (TCTuple _)) es -> SolvedIf (map pCmp es)

  -- Cmp (a -> b) fails
  TCon (TC TCFun) [_,_] -> Unsolvable

  -- (Cmp a, Cmp b) => Cmp { x:a, y:b }
  TRec fs -> SolvedIf [ pCmp e | e <- recordElements fs ]

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
  TCon (TError {}) _ -> Unsolvable

  -- SignedCmp Bit fails
  TCon (TC TCBit) [] -> Unsolvable

  -- SignedCmp Integer fails
  TCon (TC TCInteger) [] -> Unsolvable

  -- SignedCmp (Z n) fails
  TCon (TC TCIntMod) [_] -> Unsolvable

  -- SignedCmp Rational fails
  TCon (TC TCRational) [] -> Unsolvable

  -- SignedCmp (Float e p) fails
  TCon (TC TCFloat) [_, _] -> Unsolvable

  -- SignedCmp for sequences
  TCon (TC TCSeq) [n,a] -> solveSignedCmpSeq n a

  -- (SignedCmp a, SignedCmp b) => SignedCmp (a,b)
  TCon (TC (TCTuple _)) es -> SolvedIf (map pSignedCmp es)

  -- SignedCmp (a -> b) fails
  TCon (TC TCFun) [_,_] -> Unsolvable

  -- (SignedCmp a, SignedCmp b) => SignedCmp { x:a, y:b }
  TRec fs -> SolvedIf [ pSignedCmp e | e <- recordElements fs ]

  _ -> Unsolved


-- | Solving fractional literal constraints.
solveFLiteralInst :: Type -> Type -> Type -> Type -> Solved
solveFLiteralInst numT denT rndT ty
  | TCon (TError {}) _ <- tNoUser numT = Unsolvable
  | TCon (TError {}) _ <- tNoUser denT = Unsolvable
  | tIsInf numT || tIsInf denT || tIsInf rndT = Unsolvable
  | Just 0 <- tIsNum denT = Unsolvable

  | otherwise =
    case tNoUser ty of
      TVar {} -> Unsolved

      TCon (TError {}) _ -> Unsolvable

      TCon (TC TCRational) [] ->
        SolvedIf [ pFin numT, pFin denT, denT >== tOne ]

      TCon (TC TCFloat) [e,p]
        | Just 0    <- tIsNum rndT ->
          SolvedIf [ pValidFloat e p
                   , pFin numT, pFin denT, denT >== tOne ]

        | Just _    <- tIsNum rndT
        , Just opts <- knownSupportedFloat e p
        , Just n    <- tIsNum numT
        , Just d    <- tIsNum denT
         -> case FP.bfDiv opts (FP.bfFromInteger n) (FP.bfFromInteger d) of
              (_, FP.Ok) -> SolvedIf []
              _ -> Unsolvable

        | otherwise -> Unsolved

      _ -> Unsolvable


-- | Solve Literal constraints.
solveLiteralInst :: Type -> Type -> Solved
solveLiteralInst val ty
  | TCon (TError {}) _ <- tNoUser val = Unsolvable
  | otherwise =
    case tNoUser ty of

      -- Literal n Error -> fails
      TCon (TError {}) _ -> Unsolvable

      -- (1 >= val) => Literal val Bit
      TCon (TC TCBit) [] -> SolvedIf [ tOne >== val ]

      -- (fin val) => Literal val Integer
      TCon (TC TCInteger) [] -> SolvedIf [ pFin val ]

      -- (fin val) => Literal val Rational
      TCon (TC TCRational) [] -> SolvedIf [ pFin val ]

      -- ValidFloat e p => Literal val (Float e p)   if `val` is representable
      TCon (TC TCFloat) [e,p]
        | Just n    <- tIsNum val
        , Just opts <- knownSupportedFloat e p ->
          let bf = FP.bfFromInteger n
          in case FP.bfRoundFloat opts bf of
               (bf1,FP.Ok) | bf == bf1 -> SolvedIf []
               _ -> Unsolvable

        | otherwise -> Unsolved


      -- (fin val, fin m, m >= val + 1) => Literal val (Z m)
      TCon (TC TCIntMod) [modulus] ->
        SolvedIf [ pFin val, pFin modulus, modulus >== tAdd val tOne ]

      -- (fin bits, bits >= width n) => Literal n [bits]
      TCon (TC TCSeq) [bits, elTy]
        | TCon (TC TCBit) [] <- ety ->
            SolvedIf [ pFin val, pFin bits, bits >== tWidth val ]
        | TVar _ <- ety -> Unsolved
        where ety = tNoUser elTy

      TVar _ -> Unsolved

      _ -> Unsolvable


-- | Solve Literal constraints.
solveLiteralLessThanInst :: Type -> Type -> Solved
solveLiteralLessThanInst val ty
  | TCon (TError {}) _ <- tNoUser val = Unsolvable
  | otherwise =
    case tNoUser ty of

      -- Literal n Error -> fails
      TCon (TError {}) _ -> Unsolvable

      -- (2 >= val) => LiteralLessThan val Bit
      TCon (TC TCBit) [] -> SolvedIf [ tTwo >== val ]

      -- LiteralLessThan val Integer
      TCon (TC TCInteger) [] -> SolvedIf [ ]

      -- LiteralLessThan val Rational
      TCon (TC TCRational) [] -> SolvedIf [ ]

      -- ValidFloat e p => LiteralLessThan val (Float e p)   if `val-1` is representable
      -- RWD Should we remove this instance for floats?
      TCon (TC TCFloat) [e, p]
        | Just n <- tIsNum val
        , n > 0
        , Just opts  <- knownSupportedFloat e p ->
          let bf = FP.bfFromInteger (n-1)
          in case FP.bfRoundFloat opts bf of
               (bf1,FP.Ok) | bf == bf1 -> SolvedIf []
               _ -> Unsolvable

        | otherwise -> Unsolved

      -- (fin val, fin m, m >= val) => LiteralLessThan val (Z m)
      TCon (TC TCIntMod) [modulus] ->
        SolvedIf [ pFin val, pFin modulus, modulus >== val ]

      -- (fin bits, bits >= lg2 n) => LiteralLessThan n [bits]
      TCon (TC TCSeq) [bits, elTy]
        | TCon (TC TCBit) [] <- ety ->
            SolvedIf [ pFin val, pFin bits, bits >== tWidth val' ]
        | TVar _ <- ety -> Unsolved
        where ety  = tNoUser elTy
              val' = tSub (tMax val tOne) tOne

      TVar _ -> Unsolved

      _ -> Unsolvable
