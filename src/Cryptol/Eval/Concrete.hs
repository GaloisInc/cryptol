-- |
-- Module      :  Cryptol.Eval.Concrete
-- Copyright   :  (c) 2013-2020 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
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
  ( module Cryptol.Backend.Concrete
  , Value
  , primTable
  , toExpr
  ) where

import Control.Monad (join, guard, zipWithM, foldM)
import Data.Bits (Bits(..))
import Data.Ratio((%),numerator,denominator)
import Data.Word(Word32, Word64)
import MonadLib( ChoiceT, findOne, lift )
import qualified LibBF as FP
import qualified Cryptol.F2 as F2

import qualified Data.Map.Strict as Map
import Data.Map(Map)

import Cryptol.TypeCheck.Solver.InfNat (Nat'(..))

import Cryptol.Backend
import Cryptol.Backend.Concrete
import Cryptol.Backend.FloatHelpers
import Cryptol.Backend.Monad

import Cryptol.Eval.Generic hiding (logicShift)
import Cryptol.Eval.Type
import Cryptol.Eval.Value
import qualified Cryptol.SHA as SHA
import qualified Cryptol.AES as AES
import qualified Cryptol.PrimeEC as PrimeEC
import Cryptol.ModuleSystem.Name
import Cryptol.Testing.Random (randomV)
import Cryptol.TypeCheck.AST as AST
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.Ident (PrimIdent,prelPrim,floatPrim,suiteBPrim,primeECPrim)
import Cryptol.Utils.PP
import Cryptol.Utils.Logger(logPrint)
import Cryptol.Utils.RecordMap

type Value = GenValue Concrete

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
      VSeq n svs ->
        do (_a, b) <- maybe mismatch pure (tIsSeq ty)
           ses <- traverse (go b) =<< lift (sequence (enumerateSeqMap n svs))
           pure $ EList ses b
      VWord _ wval ->
        do BV _ v <- lift (asWordVal Concrete =<< wval)
           pure $ ETApp (ETApp (prim "number") (tNum v)) ty
      VStream _  -> fail "cannot construct infinite expressions"
      VFun _     -> fail "cannot convert function values to expressions"
      VPoly _    -> fail "cannot convert polymorphic values to expressions"
      VNumPoly _ -> fail "cannot convert polymorphic values to expressions"
    where
      mismatch :: forall a. ChoiceT Eval a
      mismatch =
        do doc <- lift (ppValue Concrete defaultPPOpts val)
           panic "Cryptol.Eval.Concrete.toExpr"
             ["type mismatch:"
             , pretty ty
             , render doc
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

primTable :: EvalOpts -> Map PrimIdent Value
primTable eOpts = let sym = Concrete in
  Map.union (floatPrims sym) $
  Map.union suiteBPrims $
  Map.union primeECPrims $

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
                    nlam $ \ front ->
                    nlam $ \ back  ->
                    tlam $ \ elty  ->
                    lam  $ \ l     -> return $
                    lam  $ \ r     -> join (ccatV sym front back elty <$> l <*> r))


  , ("join"       , {-# SCC "Prelude::join" #-}
                    nlam $ \ parts ->
                    nlam $ \ (finNat' -> each)  ->
                    tlam $ \ a     ->
                    lam  $ \ x     ->
                      joinV sym parts each a =<< x)

  , ("split"      , {-# SCC "Prelude::split" #-}
                    ecSplitV sym)

  , ("splitAt"    , {-# SCC "Prelude::splitAt" #-}
                    nlam $ \ front ->
                    nlam $ \ back  ->
                    tlam $ \ a     ->
                    lam  $ \ x     ->
                       splitAtV sym front back a =<< x)

  , ("reverse"    , {-# SCC "Prelude::reverse" #-}
                    nlam $ \_a ->
                    tlam $ \_b ->
                     lam $ \xs -> reverseV sym =<< xs)

  , ("transpose"  , {-# SCC "Prelude::transpose" #-}
                    nlam $ \a ->
                    nlam $ \b ->
                    tlam $ \c ->
                     lam $ \xs -> transposeV sym a b c =<< xs)

    -- Shifts and rotates
  , ("<<"         , {-# SCC "Prelude::(<<)" #-}
                    logicShift shiftLW shiftLS)
  , (">>"         , {-# SCC "Prelude::(>>)" #-}
                    logicShift shiftRW shiftRS)
  , ("<<<"        , {-# SCC "Prelude::(<<<)" #-}
                    logicShift rotateLW rotateLS)
  , (">>>"        , {-# SCC "Prelude::(>>>)" #-}
                    logicShift rotateRW rotateRS)

    -- Indexing and updates
  , ("@"          , {-# SCC "Prelude::(@)" #-}
                    indexPrim sym indexFront_int indexFront_bits indexFront)
  , ("!"          , {-# SCC "Prelude::(!)" #-}
                    indexPrim sym indexBack_int indexBack_bits indexBack)

  , ("update"     , {-# SCC "Prelude::update" #-}
                    updatePrim sym updateFront_word updateFront)

  , ("updateEnd"  , {-# SCC "Prelude::updateEnd" #-}
                    updatePrim sym updateBack_word updateBack)

    -- Misc
  , ("foldl"      , {-# SCC "Prelude::foldl" #-}
                    foldlV sym)

  , ("foldl'"     , {-# SCC "Prelude::foldl'" #-}
                    foldl'V sym)

  , ("deepseq"    , {-# SCC "Prelude::deepseq" #-}
                    tlam $ \_a ->
                    tlam $ \_b ->
                     lam $ \x -> pure $
                     lam $ \y ->
                       do _ <- forceValue =<< x
                          y)

  , ("parmap"     , {-# SCC "Prelude::parmap" #-}
                    parmapV sym)

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

   , ("pmult",
        ilam $ \u ->
        ilam $ \v ->
          wlam Concrete $ \(BV _ x) -> return $
          wlam Concrete $ \(BV _ y) ->
            let z = if u <= v then
                      F2.pmult (fromInteger (u+1)) x y
                    else
                      F2.pmult (fromInteger (v+1)) y x
             in return . VWord (1+u+v) . pure . WordVal . mkBv (1+u+v) $! z)

   , ("pmod",
        ilam $ \_u ->
        ilam $ \v ->
        wlam Concrete $ \(BV w x) -> return $
        wlam Concrete $ \(BV _ m) ->
          do assertSideCondition sym (m /= 0) DivideByZero
             return . VWord v . pure . WordVal . mkBv v $! F2.pmod (fromInteger w) x m)

  , ("pdiv",
        ilam $ \_u ->
        ilam $ \_v ->
        wlam Concrete $ \(BV w x) -> return $
        wlam Concrete $ \(BV _ m) ->
          do assertSideCondition sym (m /= 0) DivideByZero
             return . VWord w . pure . WordVal . mkBv w $! F2.pdiv (fromInteger w) x m)
  ]


primeECPrims :: Map.Map PrimIdent Value
primeECPrims = Map.fromList $ map (\(n,v) -> (primeECPrim n, v))
  [ ("ec_double", {-# SCC "PrimeEC::ec_double" #-}
       ilam $ \p ->
        lam $ \s ->
          do s' <- toProjectivePoint =<< s
             let r = PrimeEC.ec_double (PrimeEC.primeModulus p) s'
             fromProjectivePoint $! r)

  , ("ec_add_nonzero", {-# SCC "PrimeEC::ec_add_nonzero" #-}
       ilam $ \p ->
        lam $ \s -> pure $
        lam $ \t ->
          do s' <- toProjectivePoint =<< s
             t' <- toProjectivePoint =<< t
             let r = PrimeEC.ec_add_nonzero (PrimeEC.primeModulus p) s' t'
             fromProjectivePoint $! r)

  , ("ec_mult", {-# SCC "PrimeEC::ec_mult" #-}
       ilam $ \p ->
        lam $ \d -> pure $
        lam $ \s ->
          do d' <- fromVInteger <$> d
             s' <- toProjectivePoint =<< s
             let r = PrimeEC.ec_mult (PrimeEC.primeModulus p) d' s'
             fromProjectivePoint $! r)

  , ("ec_twin_mult", {-# SCC "PrimeEC::ec_twin_mult" #-}
       ilam $ \p ->
        lam $ \d0 -> pure $
        lam $ \s  -> pure $
        lam $ \d1 -> pure $
        lam $ \t  ->
          do d0' <- fromVInteger <$> d0
             s'  <- toProjectivePoint =<< s
             d1' <- fromVInteger <$> d1
             t'  <- toProjectivePoint =<< t
             let r = PrimeEC.ec_twin_mult (PrimeEC.primeModulus p) d0' s' d1' t'
             fromProjectivePoint $! r)
  ]

toProjectivePoint :: Value -> Eval PrimeEC.ProjectivePoint
toProjectivePoint v = PrimeEC.ProjectivePoint <$> f "x" <*> f "y" <*> f "z"
  where
   f nm = PrimeEC.integerToBigNat . fromVInteger <$> lookupRecord nm v

fromProjectivePoint :: PrimeEC.ProjectivePoint -> Eval Value
fromProjectivePoint (PrimeEC.ProjectivePoint x y z) =
   pure . VRecord . recordFromFields $ [("x", f x), ("y", f y), ("z", f z)]
  where
   f i = pure (VInteger (PrimeEC.bigNatToInteger i))



suiteBPrims :: Map.Map PrimIdent Value
suiteBPrims = Map.fromList $ map (\(n, v) -> (suiteBPrim n, v))
  [ ("processSHA2_224", {-# SCC "SuiteB::processSHA2_224" #-}
                      ilam $ \n ->
                       lam $ \xs ->
                         do blks <- enumerateSeqMap n . fromVSeq <$> xs
                            (SHA.SHA256S w0 w1 w2 w3 w4 w5 w6 _) <-
                               foldM (\st blk -> seq st (SHA.processSHA256Block st <$> (toSHA256Block =<< blk)))
                                     SHA.initialSHA224State blks
                            let f :: Word32 -> Eval Value
                                f = pure . VWord 32 . pure . WordVal . BV 32 . toInteger
                                zs = finiteSeqMap Concrete (map f [w0,w1,w2,w3,w4,w5,w6])
                            seq zs (pure (VSeq 7 zs)))

  , ("processSHA2_256", {-# SCC "SuiteB::processSHA2_256" #-}
                      ilam $ \n ->
                       lam $ \xs ->
                         do blks <- enumerateSeqMap n . fromVSeq <$> xs
                            (SHA.SHA256S w0 w1 w2 w3 w4 w5 w6 w7) <-
                              foldM (\st blk -> seq st (SHA.processSHA256Block st <$> (toSHA256Block =<< blk)))
                                    SHA.initialSHA256State blks
                            let f :: Word32 -> Eval Value
                                f = pure . VWord 32 . pure . WordVal . BV 32 . toInteger
                                zs = finiteSeqMap Concrete (map f [w0,w1,w2,w3,w4,w5,w6,w7])
                            seq zs (pure (VSeq 8 zs)))

  , ("processSHA2_384", {-# SCC "SuiteB::processSHA2_384" #-}
                      ilam $ \n ->
                       lam $ \xs ->
                         do blks <- enumerateSeqMap n . fromVSeq <$> xs
                            (SHA.SHA512S w0 w1 w2 w3 w4 w5 _ _) <-
                              foldM (\st blk -> seq st (SHA.processSHA512Block st <$> (toSHA512Block =<< blk)))
                                    SHA.initialSHA384State blks
                            let f :: Word64 -> Eval Value
                                f = pure . VWord 64 . pure . WordVal . BV 64 . toInteger
                                zs = finiteSeqMap Concrete (map f [w0,w1,w2,w3,w4,w5])
                            seq zs (pure (VSeq 6 zs)))

  , ("processSHA2_512", {-# SCC "SuiteB::processSHA2_512" #-}
                      ilam $ \n ->
                       lam $ \xs ->
                         do blks <- enumerateSeqMap n . fromVSeq <$> xs
                            (SHA.SHA512S w0 w1 w2 w3 w4 w5 w6 w7) <-
                              foldM (\st blk -> seq st (SHA.processSHA512Block st <$> (toSHA512Block =<< blk)))
                                    SHA.initialSHA512State blks
                            let f :: Word64 -> Eval Value
                                f = pure . VWord 64 . pure . WordVal . BV 64 . toInteger
                                zs = finiteSeqMap Concrete (map f [w0,w1,w2,w3,w4,w5,w6,w7])
                            seq zs (pure (VSeq 8 zs)))

  , ("AESKeyExpand", {-# SCC "SuiteB::AESKeyExpand" #-}
      ilam $ \k ->
       lam $ \seed ->
         do ss <- fromVSeq <$> seed
            let toWord :: Integer -> Eval Word32
                toWord i = fromInteger. bvVal <$> (fromVWord Concrete "AESInfKeyExpand" =<< lookupSeqMap ss i)
            let fromWord :: Word32 -> Eval Value
                fromWord = pure . VWord 32 . pure . WordVal . BV 32 . toInteger
            kws <- mapM toWord [0 .. k-1]
            let ws = AES.keyExpansionWords k kws
            let len = 4*(k+7)
            pure (VSeq len (finiteSeqMap Concrete (map fromWord ws))))

  , ("AESInvMixColumns", {-# SCC "SuiteB::AESInvMixColumns" #-}
      lam $ \st ->
         do ss <- fromVSeq <$> st
            let toWord :: Integer -> Eval Word32
                toWord i = fromInteger. bvVal <$> (fromVWord Concrete "AESInvMixColumns" =<< lookupSeqMap ss i)
            let fromWord :: Word32 -> Eval Value
                fromWord = pure . VWord 32 . pure . WordVal . BV 32 . toInteger
            ws <- mapM toWord [0,1,2,3]
            let ws' = AES.invMixColumns ws
            pure . VSeq 4 . finiteSeqMap Concrete . map fromWord $ ws')

  , ("AESEncRound", {-# SCC "SuiteB::AESEncRound" #-}
      lam $ \st ->
         do ss <- fromVSeq <$> st
            let toWord :: Integer -> Eval Word32
                toWord i = fromInteger. bvVal <$> (fromVWord Concrete "AESEncRound" =<< lookupSeqMap ss i)
            let fromWord :: Word32 -> Eval Value
                fromWord = pure . VWord 32 . pure . WordVal . BV 32 . toInteger
            ws <- mapM toWord [0,1,2,3]
            let ws' = AES.aesRound ws
            pure . VSeq 4 . finiteSeqMap Concrete . map fromWord $ ws')

  , ("AESEncFinalRound", {-# SCC "SuiteB::AESEncFinalRound" #-}
      lam $ \st ->
         do ss <- fromVSeq <$> st
            let toWord :: Integer -> Eval Word32
                toWord i = fromInteger. bvVal <$> (fromVWord Concrete "AESEncFinalRound" =<< lookupSeqMap ss i)
            let fromWord :: Word32 -> Eval Value
                fromWord = pure . VWord 32 . pure . WordVal . BV 32 . toInteger
            ws <- mapM toWord [0,1,2,3]
            let ws' = AES.aesFinalRound ws
            pure . VSeq 4 . finiteSeqMap Concrete . map fromWord $ ws')

  , ("AESDecRound", {-# SCC "SuiteB::AESDecRound" #-}
      lam $ \st ->
         do ss <- fromVSeq <$> st
            let toWord :: Integer -> Eval Word32
                toWord i = fromInteger. bvVal <$> (fromVWord Concrete "AESDecRound" =<< lookupSeqMap ss i)
            let fromWord :: Word32 -> Eval Value
                fromWord = pure . VWord 32 . pure . WordVal . BV 32 . toInteger
            ws <- mapM toWord [0,1,2,3]
            let ws' = AES.aesInvRound ws
            pure . VSeq 4 . finiteSeqMap Concrete . map fromWord $ ws')

  , ("AESDecFinalRound", {-# SCC "SuiteB::AESDecFinalRound" #-}
      lam $ \st ->
         do ss <- fromVSeq <$> st
            let toWord :: Integer -> Eval Word32
                toWord i = fromInteger. bvVal <$> (fromVWord Concrete "AESDecFinalRound" =<< lookupSeqMap ss i)
            let fromWord :: Word32 -> Eval Value
                fromWord = pure . VWord 32 . pure . WordVal . BV 32 . toInteger
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

--------------------------------------------------------------------------------

sshrV :: Value
sshrV =
  nlam $ \_n ->
  tlam $ \ix ->
  wlam Concrete $ \(BV w x) -> return $
  lam $ \y ->
   do idx <- y >>= asIndex Concrete ">>$" ix >>= \case
                 Left idx -> pure idx
                 Right wv -> bvVal <$> asWordVal Concrete wv
      return $ VWord w $ pure $ WordVal $ mkBv w $ signedShiftRW w x idx

logicShift :: (Integer -> Integer -> Integer -> Integer)
              -- ^ The function may assume its arguments are masked.
              -- It is responsible for masking its result if needed.
           -> (Nat' -> TValue -> SeqMap Concrete -> Integer -> SeqMap Concrete)
           -> Value
logicShift opW opS
  = nlam $ \ a ->
    tlam $ \ _ix ->
    tlam $ \ c ->
     lam  $ \ l -> return $
     lam  $ \ r -> do
        i <- r >>= \case
          VInteger i -> pure i
          VWord _ wval -> bvVal <$> (asWordVal Concrete =<< wval)
          _ -> evalPanic "logicShift" ["not an index"]
        l >>= \case
          VWord w wv -> return $ VWord w $ wv >>= \case
                          WordVal (BV _ x) -> return $ WordVal (BV w (opW w x i))
                          LargeBitsVal n xs -> return $ LargeBitsVal n $ opS (Nat n) c xs i

          _ -> mkSeq a c <$> (opS a c <$> (fromSeq "logicShift" =<< l) <*> return i)

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

shiftLS :: Nat' -> TValue -> SeqMap Concrete -> Integer -> SeqMap Concrete
shiftLS w ety vs by
  | by < 0 = shiftRS w ety vs (negate by)

shiftLS w ety vs by = IndexSeqMap $ \i ->
  case w of
    Nat len
      | i+by < len -> lookupSeqMap vs (i+by)
      | i    < len -> zeroV Concrete ety
      | otherwise  -> evalPanic "shiftLS" ["Index out of bounds"]
    Inf            -> lookupSeqMap vs (i+by)

shiftRS :: Nat' -> TValue -> SeqMap Concrete -> Integer -> SeqMap Concrete
shiftRS w ety vs by
  | by < 0 = shiftLS w ety vs (negate by)

shiftRS w ety vs by = IndexSeqMap $ \i ->
  case w of
    Nat len
      | i >= by   -> lookupSeqMap vs (i-by)
      | i < len   -> zeroV Concrete ety
      | otherwise -> evalPanic "shiftLS" ["Index out of bounds"]
    Inf
      | i >= by   -> lookupSeqMap vs (i-by)
      | otherwise -> zeroV Concrete ety


-- XXX integer doesn't implement rotateL, as there's no bit bound
rotateLW :: Integer -> Integer -> Integer -> Integer
rotateLW 0 i _  = i
rotateLW w i by = mask w $ (i `shiftL` b) .|. (i `shiftR` (fromInteger w - b))
  where b = fromInteger (by `mod` w)

rotateLS :: Nat' -> TValue -> SeqMap Concrete -> Integer -> SeqMap Concrete
rotateLS w _ vs by = IndexSeqMap $ \i ->
  case w of
    Nat len -> lookupSeqMap vs ((by + i) `mod` len)
    _ -> panic "Cryptol.Eval.Prim.rotateLS" [ "unexpected infinite sequence" ]

-- XXX integer doesn't implement rotateR, as there's no bit bound
rotateRW :: Integer -> Integer -> Integer -> Integer
rotateRW 0 i _  = i
rotateRW w i by = mask w $ (i `shiftR` b) .|. (i `shiftL` (fromInteger w - b))
  where b = fromInteger (by `mod` w)

rotateRS :: Nat' -> TValue -> SeqMap Concrete -> Integer -> SeqMap Concrete
rotateRS w _ vs by = IndexSeqMap $ \i ->
  case w of
    Nat len -> lookupSeqMap vs ((len - by + i) `mod` len)
    _ -> panic "Cryptol.Eval.Prim.rotateRS" [ "unexpected infinite sequence" ]


-- Sequence Primitives ---------------------------------------------------------

indexFront :: Nat' -> TValue -> SeqMap Concrete -> TValue -> BV -> Eval Value
indexFront _mblen _a vs _ix (bvVal -> ix) = lookupSeqMap vs ix

indexFront_bits :: Nat' -> TValue -> SeqMap Concrete -> TValue -> [Bool] -> Eval Value
indexFront_bits mblen a vs ix bs = indexFront mblen a vs ix =<< packWord Concrete bs

indexFront_int :: Nat' -> TValue -> SeqMap Concrete -> TValue -> Integer -> Eval Value
indexFront_int _mblen _a vs _ix idx = lookupSeqMap vs idx

indexBack :: Nat' -> TValue -> SeqMap Concrete -> TValue -> BV -> Eval Value
indexBack mblen a vs ix (bvVal -> idx) = indexBack_int mblen a vs ix idx

indexBack_bits :: Nat' -> TValue -> SeqMap Concrete -> TValue -> [Bool] -> Eval Value
indexBack_bits mblen a vs ix bs = indexBack mblen a vs ix =<< packWord Concrete bs

indexBack_int :: Nat' -> TValue -> SeqMap Concrete -> TValue -> Integer -> Eval Value
indexBack_int mblen _a vs _ix idx =
  case mblen of
    Nat len -> lookupSeqMap vs (len - idx - 1)
    Inf     -> evalPanic "indexBack" ["unexpected infinite sequence"]

updateFront ::
  Nat'               {- ^ length of the sequence -} ->
  TValue             {- ^ type of values in the sequence -} ->
  SeqMap Concrete    {- ^ sequence to update -} ->
  Either Integer (WordValue Concrete) {- ^ index -} ->
  Eval Value         {- ^ new value at index -} ->
  Eval (SeqMap Concrete)
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
  SeqMap Concrete    {- ^ sequence to update -} ->
  Either Integer (WordValue Concrete) {- ^ index -} ->
  Eval Value         {- ^ new value at index -} ->
  Eval (SeqMap Concrete)
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


floatPrims :: Concrete -> Map PrimIdent Value
floatPrims sym = Map.fromList [ (floatPrim i,v) | (i,v) <- nonInfixTable ]
  where
  (~>) = (,)
  nonInfixTable =
    [ "fpNaN"       ~> ilam \e -> ilam \p ->
                        VFloat BF { bfValue = FP.bfNaN
                                  , bfExpWidth = e, bfPrecWidth = p }

    , "fpPosInf"    ~> ilam \e -> ilam \p ->
                       VFloat BF { bfValue = FP.bfPosInf
                                 , bfExpWidth = e, bfPrecWidth = p }

    , "fpFromBits"  ~> ilam \e -> ilam \p -> wlam sym \bv ->
                       pure $ VFloat $ floatFromBits e p $ bvVal bv

    , "fpToBits"    ~> ilam \e -> ilam \p -> flam \x ->
                       pure $ word sym (e + p)
                            $ floatToBits e p
                            $ bfValue x
    , "=.="         ~> ilam \_ -> ilam \_ -> flam \x -> pure $ flam \y ->
                       pure $ VBit
                            $ bitLit sym
                            $ FP.bfCompare (bfValue x) (bfValue y) == EQ

    , "fpIsFinite"  ~> ilam \_ -> ilam \_ -> flam \x ->
                       pure $ VBit $ bitLit sym $ FP.bfIsFinite $ bfValue x

      -- From Backend class
    , "fpAdd"      ~> fpBinArithV sym fpPlus
    , "fpSub"      ~> fpBinArithV sym fpMinus
    , "fpMul"      ~> fpBinArithV sym fpMult
    , "fpDiv"      ~> fpBinArithV sym fpDiv

    , "fpFromRational" ~>
      ilam \e -> ilam \p -> wlam sym \r -> pure $ lam \x ->
        do rat <- fromVRational <$> x
           VFloat <$> do mode <- fpRoundMode sym r
                         pure $ floatFromRational e p mode
                              $ sNum rat % sDenom rat
    , "fpToRational" ~>
      ilam \_e -> ilam \_p -> flam \fp ->
      case floatToRational "fpToRational" fp of
        Left err -> raiseError sym err
        Right r  -> pure $
                      VRational
                        SRational { sNum = numerator r, sDenom = denominator r }
    ]


