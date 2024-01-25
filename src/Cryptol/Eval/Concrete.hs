-- |
-- Module      :  Cryptol.Eval.Concrete
-- Copyright   :  (c) 2013-2020 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
module Cryptol.Eval.Concrete
  ( module Cryptol.Backend.Concrete
  , Value
  , primTable
  , toExpr
  ) where

import Control.Monad (guard, zipWithM, foldM, mzero)
import Data.Foldable (foldl')
import Data.List (find)
import Data.Ratio(numerator,denominator)
import Data.Word(Word32, Word64)
import MonadLib( ChoiceT, findOne, lift )
import qualified LibBF as FP
import qualified Cryptol.F2 as F2

import qualified Data.Map.Strict as Map
import Data.Map(Map)
import qualified Data.Vector as Vector
import qualified Data.IntMap.Strict as IMap

import Cryptol.TypeCheck.Solver.InfNat (Nat'(..))

import Cryptol.Backend
import Cryptol.Backend.Concrete
import Cryptol.Backend.FloatHelpers
import Cryptol.Backend.Monad
import Cryptol.Backend.SeqMap
import Cryptol.Backend.WordValue

import Cryptol.Eval.Generic
import Cryptol.Eval.Prims
import Cryptol.Eval.Type
import Cryptol.Eval.Value
import qualified Cryptol.SHA as SHA
import qualified Cryptol.AES as AES
import qualified Cryptol.PrimeEC as PrimeEC
import Cryptol.ModuleSystem.Name
import Cryptol.TypeCheck.AST as AST
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.Ident (PrimIdent,prelPrim,floatPrim,suiteBPrim,primeECPrim)
import Cryptol.Utils.PP
import Cryptol.Utils.RecordMap

type Value = GenValue Concrete

-- Value to Expression conversion ----------------------------------------------

-- | Given an expected type, returns an expression that evaluates to
-- this value, if we can determine it.
toExpr :: PrimMap -> TValue -> Value -> Eval (Maybe AST.Expr)
toExpr prims t0 v0 = findOne (go t0 v0)
  where

  prim n = ePrim prims (prelPrim n)


  go :: TValue -> Value -> ChoiceT Eval Expr
  go ty val =
    case (ty,val) of
      (TVRec tfs, VRecord vfs) ->
        do -- NB, vfs first argument to keep their display order
           res <- zipRecordsM (\_lbl v t -> go t =<< lift v) vfs tfs
           case res of
             Left _ -> mismatch -- different fields
             Right efs -> pure (ERec efs)

      (TVNewtype nt ts (TVStruct tfs), VRecord vfs) ->
        do -- NB, vfs first argument to keep their display order
           res <- zipRecordsM (\_lbl v t -> go t =<< lift v) vfs tfs
           case res of
             Left _ -> mismatch -- different fields
             Right efs ->
               let c = case ntDef nt of
                         Struct co -> ntConName co
                         Enum {} -> panic "toExpr" ["Enum vs Record"]
                   f = foldl (\x t -> ETApp x (tNumValTy t)) (EVar c) ts
                in pure (EApp f (ERec efs))
      (TVNewtype nt ts (TVEnum tfss), VEnum i' vf_map) ->
        let i = fromInteger i'
        in
        case tfss Vector.!? i of
          Nothing -> mismatch -- enum constructor not found
          Just conT ->
            do let tfs = conFields conT
               vfs <- case IMap.lookup i vf_map of
                        Just con -> pure (conFields con)
                        Nothing  -> panic "toExpr" ["Missing constructor"]
               guard (Vector.length tfs == Vector.length vfs)
               c <- case ntDef nt of
                      Struct {} -> panic "toExpr" ["Enum vs Record"]
                      Enum cons ->
                        case find (\con -> ecNumber con == i) cons of
                          Just con -> pure (ecName con)
                          Nothing -> mismatch
               let f = foldl' (\x t -> ETApp x (tNumValTy t)) (EVar c) ts
               foldl' EApp f <$>
                  (zipWithM go (Vector.toList tfs) =<<
                              lift (sequence (Vector.toList vfs)))

      (TVTuple ts, VTuple tvs) ->
        do guard (length ts == length tvs)
           ETuple <$> (zipWithM go ts =<< lift (sequence tvs))
      (TVBit, VBit b) ->
        pure (prim (if b then "True" else "False"))
      (TVInteger, VInteger i) ->
        pure $ ETApp (ETApp (prim "number") (tNum i)) tInteger
      (TVIntMod n, VInteger i) ->
        pure $ ETApp (ETApp (prim "number") (tNum i)) (tIntMod (tNum n))

      (TVRational, VRational (SRational n d)) ->
        do let n' = ETApp (ETApp (prim "number") (tNum n)) tInteger
           let d' = ETApp (ETApp (prim "number") (tNum d)) tInteger
           pure $ EApp (EApp (prim "ratio") n') d'

      (TVFloat e p, VFloat i) ->
           pure (floatToExpr prims (tNum e) (tNum p) (bfValue i))
      (TVSeq _ b, VSeq n svs) ->
        do ses <- traverse (go b) =<< lift (sequence (enumerateSeqMap n svs))
           pure $ EList ses (tValTy b)
      (TVSeq n TVBit, VWord _ wval) ->
        do BV _ v <- lift (asWordVal Concrete wval)
           pure $ ETApp (ETApp (prim "number") (tNum v)) (tWord (tNum n))

      (_,VStream{})  -> mzero
      (_,VFun{})     -> mzero
      (_,VPoly{})    -> mzero
      (_,VNumPoly{}) -> mzero
      _ -> mismatch
    where
      mismatch :: forall a. ChoiceT Eval a
      mismatch =
        do doc <- lift (ppValue Concrete defaultPPOpts val)
           panic "Cryptol.Eval.Concrete.toExpr"
             ["type mismatch:"
             , pretty (tValTy ty)
             , show doc
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

primTable :: IO EvalOpts -> Map PrimIdent (Prim Concrete)
primTable getEOpts = let sym = Concrete in
  Map.union (genericPrimTable sym getEOpts) $
  Map.union (genericFloatTable sym) $
  Map.union suiteBPrims $
  Map.union primeECPrims $

  Map.fromList $ map (\(n, v) -> (prelPrim n, v))

  [ -- Indexing and updates
    ("@"          , {-# SCC "Prelude::(@)" #-}
                    indexPrim sym IndexForward indexFront_int indexFront_segs)
  , ("!"          , {-# SCC "Prelude::(!)" #-}
                    indexPrim sym IndexBackward indexFront_int indexFront_segs)

  , ("update"     , {-# SCC "Prelude::update" #-}
                    updatePrim sym updateFront_word updateFront)

  , ("updateEnd"  , {-# SCC "Prelude::updateEnd" #-}
                    updatePrim sym updateBack_word updateBack)

   , ("pmult",
        PFinPoly \u ->
        PFinPoly \v ->
        PWordFun \(BV _ x) ->
        PWordFun \(BV _ y) ->
        PPrim
            let z = if u <= v then
                      F2.pmult (fromInteger (u+1)) x y
                    else
                      F2.pmult (fromInteger (v+1)) y x
             in return . VWord (1+u+v) . wordVal . mkBv (1+u+v) $! z)

   , ("pmod",
        PFinPoly \_u ->
        PFinPoly \v ->
        PWordFun \(BV w x) ->
        PWordFun \(BV _ m) ->
        PPrim
          do assertSideCondition sym (m /= 0) DivideByZero
             return . VWord v . wordVal . mkBv v $! F2.pmod (fromInteger w) x m)

  , ("pdiv",
        PFinPoly \_u ->
        PFinPoly \_v ->
        PWordFun \(BV w x) ->
        PWordFun \(BV _ m) ->
        PPrim
          do assertSideCondition sym (m /= 0) DivideByZero
             return . VWord w . wordVal . mkBv w $! F2.pdiv (fromInteger w) x m)
  ]


primeECPrims :: Map.Map PrimIdent (Prim Concrete)
primeECPrims = Map.fromList $ map (\(n,v) -> (primeECPrim n, v))
  [ ("ec_double", {-# SCC "PrimeEC::ec_double" #-}
       PFinPoly \p ->
       PFun     \s ->
       PPrim
          do s' <- toProjectivePoint =<< s
             let r = PrimeEC.ec_double (PrimeEC.primeModulus p) s'
             fromProjectivePoint $! r)

  , ("ec_add_nonzero", {-# SCC "PrimeEC::ec_add_nonzero" #-}
       PFinPoly \p ->
       PFun     \s ->
       PFun     \t ->
       PPrim
          do s' <- toProjectivePoint =<< s
             t' <- toProjectivePoint =<< t
             let r = PrimeEC.ec_add_nonzero (PrimeEC.primeModulus p) s' t'
             fromProjectivePoint $! r)

  , ("ec_mult", {-# SCC "PrimeEC::ec_mult" #-}
       PFinPoly \p ->
       PFun     \d ->
       PFun     \s ->
       PPrim
          do d' <- fromVInteger <$> d
             s' <- toProjectivePoint =<< s
             let r = PrimeEC.ec_mult (PrimeEC.primeModulus p) d' s'
             fromProjectivePoint $! r)

  , ("ec_twin_mult", {-# SCC "PrimeEC::ec_twin_mult" #-}
       PFinPoly \p  ->
       PFun     \d0 ->
       PFun     \s  ->
       PFun     \d1 ->
       PFun     \t  ->
       PPrim
          do d0' <- fromVInteger <$> d0
             s'  <- toProjectivePoint =<< s
             d1' <- fromVInteger <$> d1
             t'  <- toProjectivePoint =<< t
             let r = PrimeEC.ec_twin_mult (PrimeEC.primeModulus p) d0' s' d1' t'
             fromProjectivePoint $! r)
  ]

toProjectivePoint :: Value -> Eval PrimeEC.ProjectivePoint
toProjectivePoint v = PrimeEC.toProjectivePoint <$> f "x" <*> f "y" <*> f "z"
  where
   f nm = fromVInteger <$> lookupRecord nm v

fromProjectivePoint :: PrimeEC.ProjectivePoint -> Eval Value
fromProjectivePoint (PrimeEC.ProjectivePoint x y z) =
   pure . VRecord . recordFromFields $ [("x", f x), ("y", f y), ("z", f z)]
  where
   f i = pure (VInteger (PrimeEC.bigNatToInteger i))



suiteBPrims :: Map.Map PrimIdent (Prim Concrete)
suiteBPrims = Map.fromList $ map (\(n, v) -> (suiteBPrim n, v))
  [ ("processSHA2_224", {-# SCC "SuiteB::processSHA2_224" #-}
     PFinPoly \n ->
     PFun     \xs ->
     PPrim
        do blks <- enumerateSeqMap n . fromVSeq <$> xs
           (SHA.SHA256S w0 w1 w2 w3 w4 w5 w6 _) <-
              foldM (\st blk -> seq st (SHA.processSHA256Block st <$> (toSHA256Block =<< blk)))
                    SHA.initialSHA224State blks
           let f :: Word32 -> Eval Value
               f = pure . VWord 32 . wordVal . BV 32 . toInteger
               zs = finiteSeqMap Concrete (map f [w0,w1,w2,w3,w4,w5,w6])
           seq zs (pure (VSeq 7 zs)))

  , ("processSHA2_256", {-# SCC "SuiteB::processSHA2_256" #-}
     PFinPoly \n ->
     PFun     \xs ->
     PPrim
        do blks <- enumerateSeqMap n . fromVSeq <$> xs
           (SHA.SHA256S w0 w1 w2 w3 w4 w5 w6 w7) <-
             foldM (\st blk -> seq st (SHA.processSHA256Block st <$> (toSHA256Block =<< blk)))
                   SHA.initialSHA256State blks
           let f :: Word32 -> Eval Value
               f = pure . VWord 32 . wordVal . BV 32 . toInteger
               zs = finiteSeqMap Concrete (map f [w0,w1,w2,w3,w4,w5,w6,w7])
           seq zs (pure (VSeq 8 zs)))

  , ("processSHA2_384", {-# SCC "SuiteB::processSHA2_384" #-}
     PFinPoly \n ->
     PFun     \xs ->
     PPrim
        do blks <- enumerateSeqMap n . fromVSeq <$> xs
           (SHA.SHA512S w0 w1 w2 w3 w4 w5 _ _) <-
             foldM (\st blk -> seq st (SHA.processSHA512Block st <$> (toSHA512Block =<< blk)))
                   SHA.initialSHA384State blks
           let f :: Word64 -> Eval Value
               f = pure . VWord 64 . wordVal . BV 64 . toInteger
               zs = finiteSeqMap Concrete (map f [w0,w1,w2,w3,w4,w5])
           seq zs (pure (VSeq 6 zs)))

  , ("processSHA2_512", {-# SCC "SuiteB::processSHA2_512" #-}
     PFinPoly \n ->
     PFun     \xs ->
     PPrim
        do blks <- enumerateSeqMap n . fromVSeq <$> xs
           (SHA.SHA512S w0 w1 w2 w3 w4 w5 w6 w7) <-
             foldM (\st blk -> seq st (SHA.processSHA512Block st <$> (toSHA512Block =<< blk)))
                   SHA.initialSHA512State blks
           let f :: Word64 -> Eval Value
               f = pure . VWord 64 . wordVal . BV 64 . toInteger
               zs = finiteSeqMap Concrete (map f [w0,w1,w2,w3,w4,w5,w6,w7])
           seq zs (pure (VSeq 8 zs)))

  , ("AESKeyExpand", {-# SCC "SuiteB::AESKeyExpand" #-}
      PFinPoly \k ->
      PFun     \seed ->
      PPrim
         do ss <- fromVSeq <$> seed
            let toWord :: Integer -> Eval Word32
                toWord i = fromInteger. bvVal <$> (fromVWord Concrete "AESInfKeyExpand" =<< lookupSeqMap ss i)
            let fromWord :: Word32 -> Eval Value
                fromWord = pure . VWord 32 . wordVal . BV 32 . toInteger
            kws <- mapM toWord [0 .. k-1]
            let ws = AES.keyExpansionWords k kws
            let len = 4*(k+7)
            pure (VSeq len (finiteSeqMap Concrete (map fromWord ws))))

  , ("AESInvMixColumns", {-# SCC "SuiteB::AESInvMixColumns" #-}
      PFun \st ->
      PPrim
         do ss <- fromVSeq <$> st
            let toWord :: Integer -> Eval Word32
                toWord i = fromInteger. bvVal <$> (fromVWord Concrete "AESInvMixColumns" =<< lookupSeqMap ss i)
            let fromWord :: Word32 -> Eval Value
                fromWord = pure . VWord 32 . wordVal . BV 32 . toInteger
            ws <- mapM toWord [0,1,2,3]
            let ws' = AES.invMixColumns ws
            pure . VSeq 4 . finiteSeqMap Concrete . map fromWord $ ws')

  , ("AESEncRound", {-# SCC "SuiteB::AESEncRound" #-}
      PFun \st ->
      PPrim
         do ss <- fromVSeq <$> st
            let toWord :: Integer -> Eval Word32
                toWord i = fromInteger. bvVal <$> (fromVWord Concrete "AESEncRound" =<< lookupSeqMap ss i)
            let fromWord :: Word32 -> Eval Value
                fromWord = pure . VWord 32 . wordVal . BV 32 . toInteger
            ws <- mapM toWord [0,1,2,3]
            let ws' = AES.aesRound ws
            pure . VSeq 4 . finiteSeqMap Concrete . map fromWord $ ws')

  , ("AESEncFinalRound", {-# SCC "SuiteB::AESEncFinalRound" #-}
     PFun \st ->
     PPrim
         do ss <- fromVSeq <$> st
            let toWord :: Integer -> Eval Word32
                toWord i = fromInteger. bvVal <$> (fromVWord Concrete "AESEncFinalRound" =<< lookupSeqMap ss i)
            let fromWord :: Word32 -> Eval Value
                fromWord = pure . VWord 32 . wordVal . BV 32 . toInteger
            ws <- mapM toWord [0,1,2,3]
            let ws' = AES.aesFinalRound ws
            pure . VSeq 4 . finiteSeqMap Concrete . map fromWord $ ws')

  , ("AESDecRound", {-# SCC "SuiteB::AESDecRound" #-}
      PFun \st ->
      PPrim
         do ss <- fromVSeq <$> st
            let toWord :: Integer -> Eval Word32
                toWord i = fromInteger. bvVal <$> (fromVWord Concrete "AESDecRound" =<< lookupSeqMap ss i)
            let fromWord :: Word32 -> Eval Value
                fromWord = pure . VWord 32 . wordVal . BV 32 . toInteger
            ws <- mapM toWord [0,1,2,3]
            let ws' = AES.aesInvRound ws
            pure . VSeq 4 . finiteSeqMap Concrete . map fromWord $ ws')

  , ("AESDecFinalRound", {-# SCC "SuiteB::AESDecFinalRound" #-}
     PFun \st ->
     PPrim
         do ss <- fromVSeq <$> st
            let toWord :: Integer -> Eval Word32
                toWord i = fromInteger. bvVal <$> (fromVWord Concrete "AESDecFinalRound" =<< lookupSeqMap ss i)
            let fromWord :: Word32 -> Eval Value
                fromWord = pure . VWord 32 . wordVal . BV 32 . toInteger
            ws <- mapM toWord [0,1,2,3]
            let ws' = AES.aesInvFinalRound ws
            pure . VSeq 4 . finiteSeqMap Concrete . map fromWord $ ws')
  ]


toSHA256Block :: Value -> Eval SHA.SHA256Block
toSHA256Block blk =
  do let ws = fromVSeq blk
     let toWord i = fromInteger . bvVal <$> (fromVWord Concrete "toSHA256Block" =<< lookupSeqMap ws i)
     SHA.SHA256Block <$>
        (toWord 0) <*>
        (toWord 1) <*>
        (toWord 2) <*>
        (toWord 3) <*>
        (toWord 4) <*>
        (toWord 5) <*>
        (toWord 6) <*>
        (toWord 7) <*>
        (toWord 8) <*>
        (toWord 9) <*>
        (toWord 10) <*>
        (toWord 11) <*>
        (toWord 12) <*>
        (toWord 13) <*>
        (toWord 14) <*>
        (toWord 15)


toSHA512Block :: Value -> Eval SHA.SHA512Block
toSHA512Block blk =
  do let ws = fromVSeq blk
     let toWord i = fromInteger . bvVal <$> (fromVWord Concrete "toSHA512Block" =<< lookupSeqMap ws i)
     SHA.SHA512Block <$>
        (toWord 0) <*>
        (toWord 1) <*>
        (toWord 2) <*>
        (toWord 3) <*>
        (toWord 4) <*>
        (toWord 5) <*>
        (toWord 6) <*>
        (toWord 7) <*>
        (toWord 8) <*>
        (toWord 9) <*>
        (toWord 10) <*>
        (toWord 11) <*>
        (toWord 12) <*>
        (toWord 13) <*>
        (toWord 14) <*>
        (toWord 15)


-- Sequence Primitives ---------------------------------------------------------

indexFront_int :: Nat' -> TValue -> SeqMap Concrete (GenValue Concrete) -> TValue -> Integer -> Eval Value
indexFront_int _mblen _a vs _ix idx = lookupSeqMap vs idx

indexFront_segs :: Nat' -> TValue -> SeqMap Concrete (GenValue Concrete) -> TValue -> Integer -> [IndexSegment Concrete] -> Eval Value
indexFront_segs _mblen _a vs _ix idx_bits segs = lookupSeqMap vs $! packSegments idx_bits segs

packSegments :: Integer -> [IndexSegment Concrete] -> Integer
packSegments = loop 0
  where
  loop !val !n segs =
    case segs of
      [] -> val
      [WordIndexSegment (BV _ x)] -> val + x
      WordIndexSegment (BV xlen x) : bs ->
        let n' = n - xlen
         in loop (val + (x*2^n')) n' bs
      BitIndexSegment True : bs ->
        let n' = n - 1
         in loop (val + 2^n') n' bs
      BitIndexSegment False : bs ->
        let n' = n - 1
         in loop val n' bs

updateFront ::
  Nat'               {- ^ length of the sequence -} ->
  TValue             {- ^ type of values in the sequence -} ->
  SeqMap Concrete (GenValue Concrete) {- ^ sequence to update -} ->
  Either Integer (WordValue Concrete) {- ^ index -} ->
  Eval Value         {- ^ new value at index -} ->
  Eval (SeqMap Concrete (GenValue Concrete))
updateFront _len _eltTy vs (Left idx) val = do
  return $ updateSeqMap vs idx val

updateFront _len _eltTy vs (Right w) val = do
  idx <- bvVal <$> asWordVal Concrete w
  return $ updateSeqMap vs idx val

updateFront_word ::
  Nat'               {- ^ length of the sequence -} ->
  TValue             {- ^ type of values in the sequence -} ->
  WordValue Concrete {- ^ bit sequence to update -} ->
  Either Integer (WordValue Concrete) {- ^ index -} ->
  Eval Value         {- ^ new value at index -} ->
  Eval (WordValue Concrete)
updateFront_word _len _eltTy bs (Left idx) val = do
  updateWordValue Concrete bs idx (fromVBit <$> val)

updateFront_word _len _eltTy bs (Right w) val = do
  idx <- bvVal <$> asWordVal Concrete w
  updateWordValue Concrete bs idx (fromVBit <$> val)

updateBack ::
  Nat'               {- ^ length of the sequence -} ->
  TValue             {- ^ type of values in the sequence -} ->
  SeqMap Concrete (GenValue Concrete) {- ^ sequence to update -} ->
  Either Integer (WordValue Concrete) {- ^ index -} ->
  Eval Value         {- ^ new value at index -} ->
  Eval (SeqMap Concrete (GenValue Concrete))
updateBack Inf _eltTy _vs _w _val =
  evalPanic "Unexpected infinite sequence in updateEnd" []
updateBack (Nat n) _eltTy vs (Left idx) val = do
  return $ updateSeqMap vs (n - idx - 1) val
updateBack (Nat n) _eltTy vs (Right w) val = do
  idx <- bvVal <$> asWordVal Concrete w
  return $ updateSeqMap vs (n - idx - 1) val

updateBack_word ::
  Nat'               {- ^ length of the sequence -} ->
  TValue             {- ^ type of values in the sequence -} ->
  WordValue Concrete {- ^ bit sequence to update -} ->
  Either Integer (WordValue Concrete) {- ^ index -} ->
  Eval Value         {- ^ new value at index -} ->
  Eval (WordValue Concrete)
updateBack_word Inf _eltTy _bs _w _val =
  evalPanic "Unexpected infinite sequence in updateEnd" []
updateBack_word (Nat n) _eltTy bs (Left idx) val = do
  updateWordValue Concrete bs (n - idx - 1) (fromVBit <$> val)
updateBack_word (Nat n) _eltTy bs (Right w) val = do
  idx <- bvVal <$> asWordVal Concrete w
  updateWordValue Concrete bs (n - idx - 1) (fromVBit <$> val)
