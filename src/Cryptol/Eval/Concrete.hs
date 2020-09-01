-- |
-- Module      :  Cryptol.Eval.Concrete
-- Copyright   :  (c) 2013-2020 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
module Cryptol.Eval.Concrete
  ( module Cryptol.Eval.Concrete.Value
  , primTable
  , toExpr
  ) where

import Control.Monad (guard, zipWithM)
import Data.Bits (Bits(..))
import Data.Ratio(numerator,denominator)
import MonadLib( ChoiceT, findOne, lift )
import qualified LibBF as FP

import qualified Data.Map.Strict as Map

import Cryptol.TypeCheck.Solver.InfNat (Nat'(..))
import Cryptol.Eval.Backend
import Cryptol.Eval.Concrete.Float(floatPrims)
import Cryptol.Eval.Concrete.FloatHelpers(bfValue)
import Cryptol.Eval.Concrete.Value
import Cryptol.Eval.Generic
import Cryptol.Eval.Monad
import Cryptol.Eval.Type
import Cryptol.Eval.Value
import Cryptol.ModuleSystem.Name
import Cryptol.Testing.Random (randomV)
import Cryptol.TypeCheck.AST as AST
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.Ident (PrimIdent,prelPrim,floatPrim)
import Cryptol.Utils.PP
import Cryptol.Utils.Logger(logPrint)
import Cryptol.Utils.RecordMap


-- Value to Expression conversion ----------------------------------------------

-- | Given an expected type, returns an expression that evaluates to
-- this value, if we can determine it.
toExpr :: PrimMap -> AST.Type -> Value -> Eval (Maybe AST.Expr)
toExpr prims t0 v0 = findOne (go t0 v0)
  where

  prim n = ePrim prims (prelPrim n)


  go :: AST.Type -> Value -> ChoiceT Eval Expr
  go ty val =
    case val of
      VRecord vfs ->
        do tfs <- maybe mismatch pure (tIsRec ty)
           -- NB, vfs first argument to keep their display order
           res <- zipRecordsM (\_lbl v t -> go t =<< lift v) vfs tfs
           case res of
             Left _ -> mismatch -- different fields
             Right efs -> pure (ERec efs)
      VTuple tvs ->
        do ts <- maybe mismatch pure (tIsTuple ty)
           guard (length ts == length tvs)
           ETuple <$> (zipWithM go ts =<< lift (sequence tvs))
      VBit b ->
        pure (prim (if b then "True" else "False"))
      VInteger i ->
        -- This works uniformly for values of type Integer or Z n
        pure $ ETApp (ETApp (prim "number") (tNum i)) ty
      VRational (SRational n d) ->
        do let n' = ETApp (ETApp (prim "number") (tNum n)) tInteger
           let d' = ETApp (ETApp (prim "number") (tNum d)) tInteger
           pure $ EApp (EApp (prim "ratio") n') d'
      VFloat i ->
        do (eT, pT) <- maybe mismatch pure (tIsFloat ty)
           pure (floatToExpr prims eT pT (bfValue i))
      VSeq (Nat n) _ svs ->
        do (_len, b) <- maybe mismatch pure (tIsSeq ty)
           if tIsBit b then
             do BV _ v <- lift (packSeqMap Concrete n svs)
                pure $ ETApp (ETApp (prim "number") (tNum v)) ty
           else
             do ses <- traverse (go b) =<< lift (sequence (enumerateSeqMap Concrete n svs))
                pure $ EList ses b

      VSeq Inf _ _ -> fail "cannot construct infinite expressions"
      VFun _     -> fail "cannot convert function values to expressions"
      VPoly _    -> fail "cannot convert polymorphic values to expressions"
      VNumPoly _ -> fail "cannot convert polymorphic values to expressions"
    where
      mismatch :: forall a. ChoiceT Eval a
      mismatch =
        do panic "Cryptol.Eval.Concrete.toExpr"
             ["type mismatch:"
             , pretty ty
             ]

floatToExpr :: PrimMap -> AST.Type -> AST.Type -> FP.BigFloat -> AST.Expr
floatToExpr prims eT pT f =
  case FP.bfToRep f of
    FP.BFNaN -> mkP "fpNaN"
    FP.BFRep sign num ->
      case (sign,num) of
        (FP.Pos, FP.Zero)   -> mkP "fpPosZero"
        (FP.Neg, FP.Zero)   -> mkP "fpNegZero"
        (FP.Pos, FP.Inf)    -> mkP "fpPosInf"
        (FP.Neg, FP.Inf)    -> mkP "fpNegInf"
        (_, FP.Num m e) ->
            let r = toRational m * (2 ^^ e)
            in EProofApp $ ePrim prims (prelPrim "fraction")
                          `ETApp` tNum (numerator r)
                          `ETApp` tNum (denominator r)
                          `ETApp` tNum (0 :: Int)
                          `ETApp` tFloat eT pT
  where
  mkP n = EProofApp $ ePrim prims (floatPrim n) `ETApp` eT `ETApp` pT

-- Primitives ------------------------------------------------------------------

primTable :: EvalOpts -> Map.Map PrimIdent Value
primTable eOpts = let sym = Concrete in
  Map.union (floatPrims sym) $
  Map.fromList $ map (\(n, v) -> (prelPrim n, v))

  [ -- Literals
    ("True"       , VBit (bitLit sym True))
  , ("False"      , VBit (bitLit sym False))
  , ("number"     , {-# SCC "Prelude::number" #-}
                    ecNumberV sym)
  , ("ratio"      , {-# SCC "Prelude::ratio" #-}
                    ratioV sym)
  , ("fraction"   , ecFractionV sym)


    -- Zero
  , ("zero"       , {-# SCC "Prelude::zero" #-}
                    VPoly (zeroV sym))

    -- Logic
  , ("&&"         , {-# SCC "Prelude::(&&)" #-}
                    binary (andV sym))
  , ("||"         , {-# SCC "Prelude::(||)" #-}
                    binary (orV sym))
  , ("^"          , {-# SCC "Prelude::(^)" #-}
                    binary (xorV sym))
  , ("complement" , {-# SCC "Prelude::complement" #-}
                    unary  (complementV sym))

    -- Ring
  , ("fromInteger", {-# SCC "Prelude::fromInteger" #-}
                    fromIntegerV sym)
  , ("+"          , {-# SCC "Prelude::(+)" #-}
                    binary (addV sym))
  , ("-"          , {-# SCC "Prelude::(-)" #-}
                    binary (subV sym))
  , ("*"          , {-# SCC "Prelude::(*)" #-}
                    binary (mulV sym))
  , ("negate"     , {-# SCC "Prelude::negate" #-}
                    unary (negateV sym))

    -- Integral
  , ("toInteger"  , {-# SCC "Prelude::toInteger" #-}
                    toIntegerV sym)
  , ("/"          , {-# SCC "Prelude::(/)" #-}
                    binary (divV sym))
  , ("%"          , {-# SCC "Prelude::(%)" #-}
                    binary (modV sym))
  , ("^^"         , {-# SCC "Prelude::(^^)" #-}
                    expV sym)
  , ("infFrom"    , {-# SCC "Prelude::infFrom" #-}
                    infFromV sym)
  , ("infFromThen", {-# SCC "Prelude::infFromThen" #-}
                    infFromThenV sym)

    -- Field
  , ("recip"      , {-# SCC "Prelude::recip" #-}
                    recipV sym)
  , ("/."         , {-# SCC "Prelude::(/.)" #-}
                    fieldDivideV sym)

    -- Round
  , ("floor"      , {-# SCC "Prelude::floor" #-}
                    unary (floorV sym))
  , ("ceiling"    , {-# SCC "Prelude::ceiling" #-}
                    unary (ceilingV sym))
  , ("trunc"      , {-# SCC "Prelude::trunc" #-}
                    unary (truncV sym))
  , ("roundAway"  , {-# SCC "Prelude::roundAway" #-}
                    unary (roundAwayV sym))
  , ("roundToEven", {-# SCC "Prelude::roundToEven" #-}
                    unary (roundToEvenV sym))

    -- Bitvector specific operations
  , ("/$"         , {-# SCC "Prelude::(/$)" #-}
                    sdivV sym)
  , ("%$"         , {-# SCC "Prelude::(%$)" #-}
                    smodV sym)
  , ("lg2"        , {-# SCC "Prelude::lg2" #-}
                    lg2V sym)
  , (">>$"        , {-# SCC "Prelude::(>>$)" #-}
                    sshrV)

    -- Cmp
  , ("<"          , {-# SCC "Prelude::(<)" #-}
                    binary (lessThanV sym))
  , (">"          , {-# SCC "Prelude::(>)" #-}
                    binary (greaterThanV sym))
  , ("<="         , {-# SCC "Prelude::(<=)" #-}
                    binary (lessThanEqV sym))
  , (">="         , {-# SCC "Prelude::(>=)" #-}
                    binary (greaterThanEqV sym))
  , ("=="         , {-# SCC "Prelude::(==)" #-}
                    binary (eqV sym))
  , ("!="         , {-# SCC "Prelude::(!=)" #-}
                    binary (distinctV sym))

    -- SignedCmp
  , ("<$"         , {-# SCC "Prelude::(<$)" #-}
                    binary (signedLessThanV sym))

    -- Finite enumerations
  , ("fromTo"     , {-# SCC "Prelude::fromTo" #-}
                    fromToV sym)
  , ("fromThenTo" , {-# SCC "Prelude::fromThenTo" #-}
                    fromThenToV sym)

    -- Sequence manipulations
  , ("#"          , {-# SCC "Prelude::(#)" #-}
                    ilam $ \ front ->
                    nlam $ \ back  ->
                    tlam $ \ elty  ->
                    lam  $ \ l     -> return $
                    lam  $ \ r     -> ccatV sym front back elty l r)


  , ("join"       , {-# SCC "Prelude::join" #-}
                    nlam $ \ parts ->
                    ilam $ \ each  ->
                    tlam $ \ a     ->
                    lam  $ \ x     -> joinV sym parts each a x)

  , ("split"      , {-# SCC "Prelude::split" #-}
                    nlam $ \parts ->
                    ilam $ \each ->
                    tlam $ \a ->
                    lam  $ \x -> splitV sym parts each a x)

  , ("splitAt"    , {-# SCC "Prelude::splitAt" #-}
                    ilam $ \ front ->
                    nlam $ \ back  ->
                    tlam $ \ a     ->
                    lam  $ \ x     -> splitAtV sym front back a x)

  , ("take"       , {-# SCC "Prelude::take" #-}
                    nlam $ \front ->
                    nlam $ \_back ->
                    tlam $ \a ->
                     lam $ \xs -> takeV sym front a xs)

    -- Shifts and rotates
  , ("<<"         , {-# SCC "Prelude::(<<)" #-}
                    logicShift sym "<<" shiftIntShrink shiftWordShrink
                      leftShiftSeqMap rightShiftSeqMap)
  , (">>"         , {-# SCC "Prelude::(>>)" #-}
                    logicShift sym ">>" shiftIntShrink shiftWordShrink
                      rightShiftSeqMap leftShiftSeqMap)
  , ("<<<"        , {-# SCC "Prelude::(<<<)" #-}
                    logicShift sym "<<<" rotateIntShrink rotateWordShrink
                      leftRotateSeqMap rightRotateSeqMap)
  , (">>>"        , {-# SCC "Prelude::(>>>)" #-}
                    logicShift sym ">>>" rotateIntShrink rotateWordShrink
                      rightRotateSeqMap leftRotateSeqMap)

    -- Indexing and updates
  , ("@"          , {-# SCC "Prelude::(@)" #-}
                    indexPrim sym indexFront_int indexFront)
  , ("!"          , {-# SCC "Prelude::(!)" #-}
                    indexPrim sym indexBack_int indexBack)

  , ("update"     , {-# SCC "Prelude::update" #-}
                    updatePrim sym updateFront)

  , ("updateEnd"  , {-# SCC "Prelude::updateEnd" #-}
                    updatePrim sym updateBack)

    -- Misc
  , ("foldl"      , {-# SCC "Prelude::foldl" #-}
                    foldlV sym)

  , ("foldl'"     , {-# SCC "Prelude::foldl'" #-}
                    foldl'V sym)


  , ("seq"        , {-# SCC "Prelude::seq" #-}
                    tlam $ \_a ->
                    tlam $ \_b ->
                     lam $ \x -> pure $
                     lam $ \y ->
                       do _ <- x
                          y)

  , ("deepseq"    , {-# SCC "Prelude::deepseq" #-}
                    tlam $ \_a ->
                    tlam $ \_b ->
                     lam $ \x -> pure $
                     lam $ \y ->
                       do _ <- forceValue =<< x
                          y)

  , ("parmap"     , {-# SCC "Prelude::parmap" #-}
                    parmapV sym)

  , ("deepseq"    , {-# SCC "Prelude::deepseq" #-}
                    tlam $ \_a ->
                    tlam $ \_b ->
                     lam $ \x -> pure $
                     lam $ \y ->
                      do _ <- forceValue sym =<< x
                         y)

  , ("fromZ"      , {-# SCC "Prelude::fromZ" #-}
                    fromZV sym)

  , ("error"      , {-# SCC "Prelude::error" #-}
                      tlam $ \a ->
                      nlam $ \_ ->
                       lam $ \s -> errorV sym a =<< (valueToString sym =<< s))

  , ("random"      , {-# SCC "Prelude::random" #-}
                     tlam $ \a ->
                     wlam sym $ \(bvVal -> x) -> randomV sym a x)

  , ("trace"       , {-# SCC "Prelude::trace" #-}
                     nlam $ \_n ->
                     tlam $ \_a ->
                     tlam $ \_b ->
                      lam $ \s -> return $
                      lam $ \x -> return $
                      lam $ \y -> do
                         msg <- valueToString sym =<< s
                         let EvalOpts { evalPPOpts, evalLogger } = eOpts
                         doc <- ppValue sym evalPPOpts =<< x
                         yv <- y
                         io $ logPrint evalLogger
                             $ if null msg then doc else text msg <+> doc
                         return yv)
  ]


--------------------------------------------------------------------------------

sshrV :: Value
sshrV =
  nlam $ \_n ->
  tlam $ \ix ->
  wlam Concrete $ \(BV w x) -> return $
  lam $ \y ->
   do idx <- either id bvVal <$> (asIndex Concrete ">>$" ix =<< y)
      word Concrete w $! signedShiftRW w x idx

-- signed right shift for words
signedShiftRW :: Integer -> Integer -> Integer -> Integer
signedShiftRW w ival by
  | by < 0    = shiftLW w ival (negate by)
  | otherwise =
     let by' = min w by in
     if by' > toInteger (maxBound :: Int) then
       panic "signedShiftRW" ["Shift amount too large", show by]
     else
       shiftR (signedValue w ival) (fromInteger by')

-- Left shift for words.
shiftLW :: Integer -> Integer -> Integer -> Integer
shiftLW w ival by
  | by <  0   = shiftRW w ival (negate by)
  | by >= w   = 0
  | by > toInteger (maxBound :: Int) = panic "shiftLW" ["Shift amount too large", show by]
  | otherwise = mask w (shiftL ival (fromInteger by))

-- Right shift for words
shiftRW :: Integer -> Integer -> Integer -> Integer
shiftRW w ival by
  | by <  0   = shiftLW w ival (negate by)
  | by >= w   = 0
  | by > toInteger (maxBound :: Int) = panic "shiftRW" ["Shift amount too large", show by]
  | otherwise = shiftR ival (fromInteger by)

-- XXX integer doesn't implement rotateL, as there's no bit bound
-- rotateLW :: Integer -> Integer -> Integer -> Integer
-- rotateLW 0 i _  = i
-- rotateLW w i by = mask w $ (i `shiftL` b) .|. (i `shiftR` (fromInteger w - b))
--   where b = fromInteger (by `mod` w)

-- -- XXX integer doesn't implement rotateR, as there's no bit bound
-- rotateRW :: Integer -> Integer -> Integer -> Integer
-- rotateRW 0 i _  = i
-- rotateRW w i by = mask w $ (i `shiftR` b) .|. (i `shiftL` (fromInteger w - b))
--   where b = fromInteger (by `mod` w)


-- Sequence Primitives ---------------------------------------------------------

indexFront :: Nat' -> TValue -> SeqMap Concrete -> TValue -> BV -> Eval Value
indexFront _mblen _a vs _ix (bvVal -> ix) = lookupSeqMap Concrete ix vs

indexFront_int :: Nat' -> TValue -> SeqMap Concrete -> TValue -> Integer -> Eval Value
indexFront_int _mblen _a vs _ix idx = lookupSeqMap Concrete idx vs

indexBack :: Nat' -> TValue -> SeqMap Concrete -> TValue -> BV -> Eval Value
indexBack mblen a vs ix (bvVal -> idx) = indexBack_int mblen a vs ix idx

indexBack_int :: Nat' -> TValue -> SeqMap Concrete -> TValue -> Integer -> Eval Value
indexBack_int mblen _a vs _ix idx =
  case mblen of
    Nat len -> lookupSeqMap Concrete (len - idx - 1) vs
    Inf     -> evalPanic "indexBack" ["unexpected infinite sequence"]

updateFront ::
  Nat'               {- ^ length of the sequence -} ->
  TValue             {- ^ type of values in the sequence -} ->
  Eval (SeqMap Concrete) {- ^ sequence to update -} ->
  Either Integer (SWord Concrete) {- ^ index -} ->
  Eval Value         {- ^ new value at index -} ->
  Eval (SeqMap Concrete)
updateFront _len _eltTy vs (Left idx) val = do
  do vs' <- delaySeqMap Concrete vs
     updateSeqMap Concrete vs' idx val

updateFront _len _eltTy vs (Right w) val = do
  do vs' <- delaySeqMap Concrete vs
     updateSeqMap Concrete vs' (bvVal w) val

updateBack ::
  Nat'               {- ^ length of the sequence -} ->
  TValue             {- ^ type of values in the sequence -} ->
  Eval (SeqMap Concrete) {- ^ sequence to update -} ->
  Either Integer (SWord Concrete) {- ^ index -} ->
  Eval Value         {- ^ new value at index -} ->
  Eval (SeqMap Concrete)
updateBack Inf _eltTy _vs _w _val =
  evalPanic "Unexpected infinite sequence in updateEnd" []
updateBack (Nat n) _eltTy vs (Left idx) val =
  do vs' <- delaySeqMap Concrete vs
     updateSeqMap Concrete vs' (n - idx - 1) val
updateBack (Nat n) _eltTy vs (Right w) val =
  do vs' <- delaySeqMap Concrete vs
     updateSeqMap Concrete vs' (n - (bvVal w) - 1) val
