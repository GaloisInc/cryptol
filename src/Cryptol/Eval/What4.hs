-- |
-- Module      :  Cryptol.Eval.What4
-- Copyright   :  (c) 2020 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com

{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
module Cryptol.Eval.What4
  ( Value
  , primTable
  ) where

import qualified Control.Exception as X
import           Control.Concurrent.MVar
import           Control.Monad (foldM)
import           Control.Monad.IO.Class
import           Data.Bits
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Parameterized.Context
import           Data.Parameterized.TraversableFC
import           Data.Parameterized.Some
import qualified Data.BitVector.Sized as BV

import qualified What4.Interface as W4
import qualified What4.SWord as SW
import qualified What4.Utils.AbstractDomains as W4

import Cryptol.Backend
import Cryptol.Backend.Monad ( EvalError(..), Unsupported(..) )
import Cryptol.Backend.What4

import Cryptol.Eval.Generic
import Cryptol.Eval.Prims
import Cryptol.Eval.Type (TValue(..))
import Cryptol.Eval.Value

import qualified Cryptol.SHA as SHA

import Cryptol.TypeCheck.Solver.InfNat( Nat'(..), widthInteger )

import Cryptol.Utils.Ident
import Cryptol.Utils.Panic
import Cryptol.Utils.RecordMap

type Value sym = GenValue (What4 sym)

-- See also Cryptol.Prims.Eval.primTable
primTable :: W4.IsSymExprBuilder sym => What4 sym -> IO EvalOpts -> Map.Map PrimIdent (Prim (What4 sym))
primTable sym getEOpts =
  let w4sym = w4 sym in
  Map.union (suiteBPrims sym) $
  Map.union (primeECPrims sym) $
  Map.union (genericFloatTable sym) $
  Map.union (genericPrimTable sym getEOpts) $

  Map.fromList $ map (\(n, v) -> (prelPrim n, v))

  [ (">>$"         , sshrV sym)

    -- Shifts and rotates
  , ("<<"          , logicShift sym "<<"  shiftShrink
                        (w4bvShl w4sym) (w4bvLshr w4sym)
                        shiftLeftReindex shiftRightReindex)
  , (">>"          , logicShift sym ">>"  shiftShrink
                        (w4bvLshr w4sym) (w4bvShl w4sym)
                        shiftRightReindex shiftLeftReindex)
  , ("<<<"         , logicShift sym "<<<" rotateShrink
                        (w4bvRol w4sym) (w4bvRor w4sym)
                        rotateLeftReindex rotateRightReindex)
  , (">>>"         , logicShift sym ">>>" rotateShrink
                        (w4bvRor w4sym) (w4bvRol w4sym)
                        rotateRightReindex rotateLeftReindex)

    -- Indexing and updates
  , ("@"           , indexPrim sym (indexFront_int sym) (indexFront_bits sym) (indexFront_word sym))
  , ("!"           , indexPrim sym (indexBack_int sym) (indexBack_bits sym) (indexBack_word sym))

  , ("update"      , updatePrim sym (updateFrontSym_word sym) (updateFrontSym sym))
  , ("updateEnd"   , updatePrim sym (updateBackSym_word sym)  (updateBackSym sym))

  ]

primeECPrims :: W4.IsSymExprBuilder sym => What4 sym -> Map.Map PrimIdent (Prim (What4 sym))
primeECPrims sym = Map.fromList $ [ (primeECPrim n, v) | (n,v) <- prims ]
 where
 (~>) = (,)

 prims =
  [ -- {p} (prime p, p > 3) => ProjectivePoint p -> ProjectivePoint p
    "ec_double" ~>
      PFinPoly \p ->
      PFun     \s ->
      PPrim
         do p' <- integerLit sym p
            s' <- toProjectivePoint sym =<< s
            addUninterpWarning sym "Prime ECC"
            fn <- liftIO $ getUninterpFn sym "ec_double"
                              (Empty :> W4.BaseIntegerRepr :> projectivePointRepr) projectivePointRepr
            z  <- liftIO $ W4.applySymFn (w4 sym) fn (Empty :> p' :> s')
            fromProjectivePoint sym z

    -- {p} (prime p, p > 3) => ProjectivePoint p -> ProjectivePoint p -> ProjectivePoint p
  , "ec_add_nonzero" ~>
      PFinPoly \p ->
      PFun     \s ->
      PFun     \t ->
      PPrim
         do p' <- integerLit sym p
            s' <- toProjectivePoint sym =<< s
            t' <- toProjectivePoint sym =<< t
            addUninterpWarning sym "Prime ECC"
            fn <- liftIO $ getUninterpFn sym "ec_add_nonzero"
                              (Empty :> W4.BaseIntegerRepr :> projectivePointRepr :> projectivePointRepr) projectivePointRepr
            z  <- liftIO $ W4.applySymFn (w4 sym) fn (Empty :> p' :> s' :> t')
            fromProjectivePoint sym z

    -- {p} (prime p, p > 3) => Z p -> ProjectivePoint p -> ProjectivePoint p
  , "ec_mult" ~>
      PFinPoly \p ->
      PFun     \k ->
      PFun     \s ->
      PPrim
         do p' <- integerLit sym p
            k' <- fromVInteger <$> k
            s' <- toProjectivePoint sym =<< s
            addUninterpWarning sym "Prime ECC"
            fn <- liftIO $ getUninterpFn sym "ec_mult"
                              (Empty :> W4.BaseIntegerRepr :> W4.BaseIntegerRepr :> projectivePointRepr) projectivePointRepr
            z  <- liftIO $ W4.applySymFn (w4 sym) fn (Empty :> p' :> k' :> s')
            fromProjectivePoint sym z

    -- {p} (prime p, p > 3) => Z p -> ProjectivePoint p -> Z p -> ProjectivePoint p -> ProjectivePoint p
  , "ec_twin_mult" ~>
      PFinPoly \p ->
      PFun     \j ->
      PFun     \s ->
      PFun     \k ->
      PFun     \t ->
      PPrim
         do p' <- integerLit sym p
            j' <- fromVInteger <$> j
            s' <- toProjectivePoint sym =<< s
            k' <- fromVInteger <$> k
            t' <- toProjectivePoint sym =<< t
            addUninterpWarning sym "Prime ECC"
            fn <- liftIO $ getUninterpFn sym "ec_twin_mult"
                              (Empty :> W4.BaseIntegerRepr :> W4.BaseIntegerRepr :> projectivePointRepr :>
                                                              W4.BaseIntegerRepr :> projectivePointRepr)
                              projectivePointRepr
            z  <- liftIO $ W4.applySymFn (w4 sym) fn (Empty :> p' :> j' :> s' :> k' :> t')
            fromProjectivePoint sym z
  ]

type ProjectivePoint = W4.BaseStructType (EmptyCtx ::> W4.BaseIntegerType ::> W4.BaseIntegerType ::> W4.BaseIntegerType)

projectivePointRepr :: W4.BaseTypeRepr ProjectivePoint
projectivePointRepr = W4.knownRepr

toProjectivePoint :: W4.IsSymExprBuilder sym =>
  What4 sym -> Value sym -> SEval (What4 sym) (W4.SymExpr sym ProjectivePoint)
toProjectivePoint sym v =
  do x <- fromVInteger <$> lookupRecord "x" v
     y <- fromVInteger <$> lookupRecord "y" v
     z <- fromVInteger <$> lookupRecord "z" v
     liftIO $ W4.mkStruct (w4 sym) (Empty :> x :> y :> z)

fromProjectivePoint :: W4.IsSymExprBuilder sym =>
  What4 sym -> W4.SymExpr sym ProjectivePoint -> SEval (What4 sym) (Value sym)
fromProjectivePoint sym p = liftIO $
  do x <- VInteger <$> W4.structField (w4 sym) p (natIndex @0)
     y <- VInteger <$> W4.structField (w4 sym) p (natIndex @1)
     z <- VInteger <$> W4.structField (w4 sym) p (natIndex @2)
     pure $ VRecord $ recordFromFields [ (packIdent "x",pure x), (packIdent "y",pure y),(packIdent "z",pure z) ]


suiteBPrims :: W4.IsSymExprBuilder sym => What4 sym -> Map.Map PrimIdent (Prim (What4 sym))
suiteBPrims sym = Map.fromList $ [ (suiteBPrim n, v) | (n,v) <- prims ]
 where
 (~>) = (,)

 prims =
  [ "AESEncRound" ~>
       PFun \st ->
       PPrim
         do addUninterpWarning sym "AES encryption"
            applyAESStateFunc sym "AESEncRound" =<< st
  , "AESEncFinalRound" ~>
       PFun \st ->
       PPrim
         do addUninterpWarning sym "AES encryption"
            applyAESStateFunc sym "AESEncFinalRound" =<< st
  , "AESDecRound" ~>
       PFun \st ->
       PPrim
         do addUninterpWarning sym "AES decryption"
            applyAESStateFunc sym "AESDecRound" =<< st
  , "AESDecFinalRound" ~>
       PFun \st ->
       PPrim
         do addUninterpWarning sym "AES decryption"
            applyAESStateFunc sym "AESDecFinalRound" =<< st
  , "AESInvMixColumns" ~>
       PFun \st ->
       PPrim
         do addUninterpWarning sym "AES key expansion"
            applyAESStateFunc sym "AESInvMixColumns" =<< st

    -- {k} (fin k, k >= 4, 8 >= k) => [k][32] -> [4*(k+7)][32]
  , "AESKeyExpand" ~>
       PFinPoly \k ->
       PFun     \st ->
       PPrim
          do ss <- fromVSeq <$> st
             -- pack the arguments into a k-tuple of 32-bit values
             Some ws <- generateSomeM (fromInteger k) (\i -> Some <$> toWord32 sym "AESKeyExpand" ss (toInteger i))
             -- get the types of the arguments
             let args = fmapFC W4.exprType ws
             -- compute the return type which is a tuple of @4*(k+7)@ 32-bit values
             Some ret <- pure $ generateSome (4*(fromInteger k + 7)) (\_ -> Some (W4.BaseBVRepr (W4.knownNat @32)))
             -- retrieve the relevant uninterpreted function and apply it to the arguments
             addUninterpWarning sym "AES key expansion"
             fn <- liftIO $ getUninterpFn sym ("AESKeyExpand" <> Text.pack (show k)) args (W4.BaseStructRepr ret)
             z  <- liftIO $ W4.applySymFn (w4 sym) fn ws
             -- compute a sequence that projects the relevant fields from the outout tuple
             pure $ VSeq (4*(k+7)) $ IndexSeqMap $ \i ->
               case intIndex (fromInteger i) (size ret) of
                 Just (Some idx) | Just W4.Refl <- W4.testEquality (ret!idx) (W4.BaseBVRepr (W4.knownNat @32)) ->
                   fromWord32 =<< liftIO (W4.structField (w4 sym) z idx)
                 _ -> evalPanic "AESKeyExpand" ["Index out of range", show k, show i]

    -- {n} (fin n) => [n][16][32] -> [7][32]
  , "processSHA2_224" ~>
    PFinPoly \n ->
    PFun     \xs ->
    PPrim
       do blks <- enumerateSeqMap n . fromVSeq <$> xs
          addUninterpWarning sym "SHA-224"
          initSt <- liftIO (mkSHA256InitialState sym SHA.initialSHA224State)
          finalSt <- foldM (\st blk -> processSHA256Block sym st =<< blk) initSt blks
          pure $ VSeq 7 $ IndexSeqMap \i ->
            case intIndex (fromInteger i) (knownSize :: Size SHA256State) of
              Just (Some idx) ->
                do z <- liftIO $ W4.structField (w4 sym) finalSt idx
                   case W4.testEquality (W4.exprType z) (W4.BaseBVRepr (W4.knownNat @32)) of
                     Just W4.Refl -> fromWord32 z
                     Nothing -> evalPanic "processSHA2_224" ["Index out of range", show i]
              Nothing -> evalPanic "processSHA2_224" ["Index out of range", show i]

    -- {n} (fin n) => [n][16][32] -> [8][32]
  , "processSHA2_256" ~>
    PFinPoly \n ->
    PFun     \xs ->
    PPrim
       do blks <- enumerateSeqMap n . fromVSeq <$> xs
          addUninterpWarning sym "SHA-256"
          initSt <- liftIO (mkSHA256InitialState sym SHA.initialSHA256State)
          finalSt <- foldM (\st blk -> processSHA256Block sym st =<< blk) initSt blks
          pure $ VSeq 8 $ IndexSeqMap \i ->
            case intIndex (fromInteger i) (knownSize :: Size SHA256State) of
              Just (Some idx) ->
                do z <- liftIO $ W4.structField (w4 sym) finalSt idx
                   case W4.testEquality (W4.exprType z) (W4.BaseBVRepr (W4.knownNat @32)) of
                     Just W4.Refl -> fromWord32 z
                     Nothing -> evalPanic "processSHA2_256" ["Index out of range", show i]
              Nothing -> evalPanic "processSHA2_256" ["Index out of range", show i]

    -- {n} (fin n) => [n][16][64] -> [6][64]
  , "processSHA2_384" ~>
    PFinPoly \n ->
    PFun     \xs ->
    PPrim
       do blks <- enumerateSeqMap n . fromVSeq <$> xs
          addUninterpWarning sym "SHA-384"
          initSt <- liftIO (mkSHA512InitialState sym SHA.initialSHA384State)
          finalSt <- foldM (\st blk -> processSHA512Block sym st =<< blk) initSt blks
          pure $ VSeq 6 $ IndexSeqMap \i ->
            case intIndex (fromInteger i) (knownSize :: Size SHA512State) of
              Just (Some idx) ->
                do z <- liftIO $ W4.structField (w4 sym) finalSt idx
                   case W4.testEquality (W4.exprType z) (W4.BaseBVRepr (W4.knownNat @64)) of
                     Just W4.Refl -> fromWord64 z
                     Nothing -> evalPanic "processSHA2_384" ["Index out of range", show i]
              Nothing -> evalPanic "processSHA2_384" ["Index out of range", show i]

    -- {n} (fin n) => [n][16][64] -> [8][64]
  , "processSHA2_512" ~>
    PFinPoly \n ->
    PFun     \xs ->
    PPrim
       do blks <- enumerateSeqMap n . fromVSeq <$> xs
          addUninterpWarning sym "SHA-512"
          initSt <- liftIO (mkSHA512InitialState sym SHA.initialSHA512State)
          finalSt <- foldM (\st blk -> processSHA512Block sym st =<< blk) initSt blks
          pure $ VSeq 8 $ IndexSeqMap \i ->
            case intIndex (fromInteger i) (knownSize :: Size SHA512State) of
              Just (Some idx) ->
                do z <- liftIO $ W4.structField (w4 sym) finalSt idx
                   case W4.testEquality (W4.exprType z) (W4.BaseBVRepr (W4.knownNat @64)) of
                     Just W4.Refl -> fromWord64 z
                     Nothing -> evalPanic "processSHA2_512" ["Index out of range", show i]
              Nothing -> evalPanic "processSHA2_512" ["Index out of range", show i]
  ]


type SHA256State =
  EmptyCtx ::>
    W4.BaseBVType 32 ::> W4.BaseBVType 32 ::> W4.BaseBVType 32 ::> W4.BaseBVType 32 ::>
    W4.BaseBVType 32 ::> W4.BaseBVType 32 ::> W4.BaseBVType 32 ::> W4.BaseBVType 32

type SHA512State =
  EmptyCtx ::>
    W4.BaseBVType 64 ::> W4.BaseBVType 64 ::> W4.BaseBVType 64 ::> W4.BaseBVType 64 ::>
    W4.BaseBVType 64 ::> W4.BaseBVType 64 ::> W4.BaseBVType 64 ::> W4.BaseBVType 64


mkSHA256InitialState :: W4.IsSymExprBuilder sym =>
  What4 sym ->
  SHA.SHA256State ->
  IO (W4.SymExpr sym (W4.BaseStructType SHA256State))
mkSHA256InitialState sym (SHA.SHA256S s0 s1 s2 s3 s4 s5 s6 s7) =
  do z0 <- lit s0
     z1 <- lit s1
     z2 <- lit s2
     z3 <- lit s3
     z4 <- lit s4
     z5 <- lit s5
     z6 <- lit s6
     z7 <- lit s7
     W4.mkStruct (w4 sym) (Empty :> z0 :> z1 :> z2 :> z3 :> z4 :> z5 :> z6 :> z7)
 where lit w = W4.bvLit (w4 sym) (W4.knownNat @32) (BV.word32 w)

mkSHA512InitialState :: W4.IsSymExprBuilder sym =>
  What4 sym ->
  SHA.SHA512State ->
  IO (W4.SymExpr sym (W4.BaseStructType SHA512State))
mkSHA512InitialState sym (SHA.SHA512S s0 s1 s2 s3 s4 s5 s6 s7) =
  do z0 <- lit s0
     z1 <- lit s1
     z2 <- lit s2
     z3 <- lit s3
     z4 <- lit s4
     z5 <- lit s5
     z6 <- lit s6
     z7 <- lit s7
     W4.mkStruct (w4 sym) (Empty :> z0 :> z1 :> z2 :> z3 :> z4 :> z5 :> z6 :> z7)
 where lit w = W4.bvLit (w4 sym) (W4.knownNat @64) (BV.word64 w)

processSHA256Block :: W4.IsSymExprBuilder sym =>
  What4 sym ->
  W4.SymExpr sym (W4.BaseStructType SHA256State) ->
  Value sym ->
  SEval (What4 sym) (W4.SymExpr sym (W4.BaseStructType SHA256State))
processSHA256Block sym st blk =
  do let ss = fromVSeq blk
     b0  <- toWord32 sym "processSHA256Block" ss 0
     b1  <- toWord32 sym "processSHA256Block" ss 1
     b2  <- toWord32 sym "processSHA256Block" ss 2
     b3  <- toWord32 sym "processSHA256Block" ss 3
     b4  <- toWord32 sym "processSHA256Block" ss 4
     b5  <- toWord32 sym "processSHA256Block" ss 5
     b6  <- toWord32 sym "processSHA256Block" ss 6
     b7  <- toWord32 sym "processSHA256Block" ss 7
     b8  <- toWord32 sym "processSHA256Block" ss 8
     b9  <- toWord32 sym "processSHA256Block" ss 9
     b10 <- toWord32 sym "processSHA256Block" ss 10
     b11 <- toWord32 sym "processSHA256Block" ss 11
     b12 <- toWord32 sym "processSHA256Block" ss 12
     b13 <- toWord32 sym "processSHA256Block" ss 13
     b14 <- toWord32 sym "processSHA256Block" ss 14
     b15 <- toWord32 sym "processSHA256Block" ss 15
     let args = Empty :> st  :>
                  b0  :> b1  :> b2  :> b3 :>
                  b4  :> b5  :> b6  :> b7 :>
                  b8  :> b9  :> b10 :> b11 :>
                  b12 :> b13 :> b14 :> b15
     let ret = W4.exprType st
     fn <- liftIO $ getUninterpFn sym "processSHA256Block" (fmapFC W4.exprType args) ret
     liftIO $ W4.applySymFn (w4 sym) fn args


processSHA512Block :: W4.IsSymExprBuilder sym =>
  What4 sym ->
  W4.SymExpr sym (W4.BaseStructType SHA512State) ->
  Value sym ->
  SEval (What4 sym) (W4.SymExpr sym (W4.BaseStructType SHA512State))
processSHA512Block sym st blk =
  do let ss = fromVSeq blk
     b0  <- toWord64 sym "processSHA512Block" ss 0
     b1  <- toWord64 sym "processSHA512Block" ss 1
     b2  <- toWord64 sym "processSHA512Block" ss 2
     b3  <- toWord64 sym "processSHA512Block" ss 3
     b4  <- toWord64 sym "processSHA512Block" ss 4
     b5  <- toWord64 sym "processSHA512Block" ss 5
     b6  <- toWord64 sym "processSHA512Block" ss 6
     b7  <- toWord64 sym "processSHA512Block" ss 7
     b8  <- toWord64 sym "processSHA512Block" ss 8
     b9  <- toWord64 sym "processSHA512Block" ss 9
     b10 <- toWord64 sym "processSHA512Block" ss 10
     b11 <- toWord64 sym "processSHA512Block" ss 11
     b12 <- toWord64 sym "processSHA512Block" ss 12
     b13 <- toWord64 sym "processSHA512Block" ss 13
     b14 <- toWord64 sym "processSHA512Block" ss 14
     b15 <- toWord64 sym "processSHA512Block" ss 15
     let args = Empty :> st  :>
                  b0  :> b1  :> b2  :> b3 :>
                  b4  :> b5  :> b6  :> b7 :>
                  b8  :> b9  :> b10 :> b11 :>
                  b12 :> b13 :> b14 :> b15
     let ret = W4.exprType st
     fn <- liftIO $ getUninterpFn sym "processSHA512Block" (fmapFC W4.exprType args) ret
     liftIO $ W4.applySymFn (w4 sym) fn args


addUninterpWarning :: MonadIO m => What4 sym -> Text -> m ()
addUninterpWarning sym nm = liftIO (modifyMVar_ (w4uninterpWarns sym) (pure . Set.insert nm))

-- | Retrieve the named uninterpreted function, with the given argument types and
--   return type, from a cache.  Create a fresh function if it has not previously
--   been requested.  A particular named function is required to be used with
--   consistent types every time it is requested; otherwise this function will panic.
getUninterpFn :: W4.IsSymExprBuilder sym =>
  What4 sym ->
  Text {- ^ Function name -} ->
  Assignment W4.BaseTypeRepr args {- ^ function argument types -} ->
  W4.BaseTypeRepr ret {- ^ function return type -} ->
  IO (W4.SymFn sym args ret)
getUninterpFn sym funNm args ret =
  modifyMVar (w4funs sym) $ \m ->
    case Map.lookup funNm m of
      Nothing ->
        do fn <- W4.freshTotalUninterpFn (w4 sym) (W4.safeSymbol (Text.unpack funNm)) args ret
           let m' = Map.insert funNm (SomeSymFn fn) m
           return (m', fn)

      Just (SomeSymFn fn)
        | Just W4.Refl <- W4.testEquality args (W4.fnArgTypes fn)
        , Just W4.Refl <- W4.testEquality ret (W4.fnReturnType fn)
        -> return (m, fn)

        | otherwise -> panic "getUninterpFn"
                           [ "Function" ++ show funNm ++ "used at incompatible types"
                           , "Created with types:"
                           , show (W4.fnArgTypes fn) ++ " -> " ++ show (W4.fnReturnType fn)
                           , "Requested at types:"
                           , show args ++ " -> " ++ show ret
                           ]

toWord32 :: W4.IsSymExprBuilder sym =>
  What4 sym -> String -> SeqMap (What4 sym) (GenValue (What4 sym)) -> Integer -> SEval (What4 sym) (W4.SymBV sym 32)
toWord32 sym nm ss i =
  do x <- fromVWord sym nm =<< lookupSeqMap ss i
     case x of
       SW.DBV x' | Just W4.Refl <- W4.testEquality (W4.bvWidth x') (W4.knownNat @32) -> pure x'
       _ -> panic nm ["Unexpected word size", show (SW.bvWidth x)]

fromWord32 :: W4.IsSymExprBuilder sym => W4.SymBV sym 32 -> SEval (What4 sym) (Value sym)
fromWord32 = pure . VWord 32 . WordVal . SW.DBV

toWord64 :: W4.IsSymExprBuilder sym =>
  What4 sym -> String -> SeqMap (What4 sym) (GenValue (What4 sym)) -> Integer -> SEval (What4 sym) (W4.SymBV sym 64)
toWord64 sym nm ss i =
  do x <- fromVWord sym nm =<< lookupSeqMap ss i
     case x of
       SW.DBV x' | Just W4.Refl <- W4.testEquality (W4.bvWidth x') (W4.knownNat @64) -> pure x'
       _ -> panic nm ["Unexpected word size", show (SW.bvWidth x)]

fromWord64 :: W4.IsSymExprBuilder sym => W4.SymBV sym 64 -> SEval (What4 sym) (Value sym)
fromWord64 = pure . VWord 64 . WordVal . SW.DBV



-- | Apply the named uninterpreted function to a sequence of @[4][32]@ values,
--   and return a sequence of @[4][32]@ values.  This shape of function is used
--   for most of the SuiteB AES primitives.
applyAESStateFunc :: forall sym. W4.IsSymExprBuilder sym =>
  What4 sym -> Text -> Value sym -> SEval (What4 sym) (Value sym)
applyAESStateFunc sym funNm x =
  do let ss = fromVSeq x
     w0 <- toWord32 sym nm ss 0
     w1 <- toWord32 sym nm ss 1
     w2 <- toWord32 sym nm ss 2
     w3 <- toWord32 sym nm ss 3
     fn <- liftIO $ getUninterpFn sym funNm argCtx (W4.BaseStructRepr argCtx)
     z  <- liftIO $ W4.applySymFn (w4 sym) fn (Empty :> w0 :> w1 :> w2 :> w3)
     pure $ VSeq 4 $ IndexSeqMap \i ->
       if | i == 0 -> fromWord32 =<< liftIO (W4.structField (w4 sym) z (natIndex @0))
          | i == 1 -> fromWord32 =<< liftIO (W4.structField (w4 sym) z (natIndex @1))
          | i == 2 -> fromWord32 =<< liftIO (W4.structField (w4 sym) z (natIndex @2))
          | i == 3 -> fromWord32 =<< liftIO (W4.structField (w4 sym) z (natIndex @3))
          | otherwise -> evalPanic "applyAESStateFunc" ["Index out of range", show funNm, show i]

 where
   nm = Text.unpack funNm

   argCtx :: Assignment W4.BaseTypeRepr
                 (EmptyCtx ::> W4.BaseBVType 32 ::> W4.BaseBVType 32 ::> W4.BaseBVType 32 ::> W4.BaseBVType 32)
   argCtx = W4.knownRepr


sshrV :: W4.IsSymExprBuilder sym => What4 sym -> Prim (What4 sym)
sshrV sym =
  PFinPoly \n ->
  PTyPoly  \ix ->
  PWordFun \x ->
  PStrict  \y ->
  PPrim $
    case asIndex sym ">>$" ix y of
       Left i ->
         do pneg <- intLessThan sym i =<< integerLit sym 0
            zneg <- do i' <- shiftShrink sym (Nat n) ix =<< intNegate sym i
                       amt <- wordFromInt sym n i'
                       w4bvShl (w4 sym) x amt
            zpos <- do i' <- shiftShrink sym (Nat n) ix i
                       amt <- wordFromInt sym n i'
                       w4bvAshr (w4 sym) x amt
            VWord (SW.bvWidth x) . WordVal <$> iteWord sym pneg zneg zpos

       Right wv ->
         do amt <- asWordVal sym wv
            VWord (SW.bvWidth x) . WordVal <$> w4bvAshr (w4 sym) x amt

indexFront_int ::
  W4.IsSymExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  SeqMap (What4 sym) (GenValue (What4 sym)) ->
  TValue ->
  SInteger (What4 sym) ->
  SEval (What4 sym) (Value sym)
indexFront_int sym mblen _a xs ix idx
  | Just i <- W4.asInteger idx
  = lookupSeqMap xs i

  | (lo, Just hi) <- bounds
  = foldr f def [lo .. hi]

  | otherwise
  = liftIO (X.throw (UnsupportedSymbolicOp "unbounded integer indexing"))

 where
    w4sym = w4 sym

    def = raiseError sym (InvalidIndex Nothing)

    f n y =
       do p <- liftIO (W4.intEq w4sym idx =<< W4.intLit w4sym n)
          iteValue sym p (lookupSeqMap xs n) y

    bounds =
      (case W4.rangeLowBound (W4.integerBounds idx) of
        W4.Inclusive l -> max l 0
        _ -> 0
      , case (maxIdx, W4.rangeHiBound (W4.integerBounds idx)) of
          (Just n, W4.Inclusive h) -> Just (min n h)
          (Just n, _)              -> Just n
          _                        -> Nothing
      )

    -- Maximum possible in-bounds index given `Z m`
    -- type information and the length
    -- of the sequence. If the sequences is infinite and the
    -- integer is unbounded, there isn't much we can do.
    maxIdx =
      case (mblen, ix) of
        (Nat n, TVIntMod m)  -> Just (min (toInteger n) (toInteger m))
        (Nat n, _)           -> Just n
        (_    , TVIntMod m)  -> Just m
        _                    -> Nothing

indexBack_int ::
  W4.IsSymExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  SeqMap (What4 sym) (GenValue (What4 sym)) ->
  TValue ->
  SInteger (What4 sym) ->
  SEval (What4 sym) (Value sym)
indexBack_int sym (Nat n) a xs ix idx = indexFront_int sym (Nat n) a (reverseSeqMap n xs) ix idx
indexBack_int _ Inf _ _ _ _ = evalPanic "Expected finite sequence" ["indexBack_int"]

indexFront_word ::
  W4.IsSymExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  SeqMap (What4 sym) (GenValue (What4 sym)) ->
  TValue ->
  SWord (What4 sym) ->
  SEval (What4 sym) (Value sym)
indexFront_word sym mblen _a xs _ix idx
  | Just i <- SW.bvAsUnsignedInteger idx
  = lookupSeqMap xs i

  | otherwise
  = foldr f def idxs

 where
    w4sym = w4 sym

    w = SW.bvWidth idx
    def = raiseError sym (InvalidIndex Nothing)

    f n y =
       do p <- liftIO (SW.bvEq w4sym idx =<< SW.bvLit w4sym w n)
          iteValue sym p (lookupSeqMap xs n) y

    -- maximum possible in-bounds index given the bitwidth
    -- of the index value and the length of the sequence
    maxIdx =
      case mblen of
        Nat n | n < 2^w -> n-1
        _ -> 2^w - 1

    -- concrete indices to consider, intersection of the
    -- range of values the index value might take with
    -- the legal values
    idxs =
      case SW.unsignedBVBounds idx of
        Just (lo, hi) -> [lo .. min hi maxIdx]
        _ -> [0 .. maxIdx]

indexBack_word ::
  W4.IsSymExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  SeqMap (What4 sym) (GenValue (What4 sym)) ->
  TValue ->
  SWord (What4 sym) ->
  SEval (What4 sym) (Value sym)
indexBack_word sym (Nat n) a xs ix idx = indexFront_word sym (Nat n) a (reverseSeqMap n xs) ix idx
indexBack_word _ Inf _ _ _ _ = evalPanic "Expected finite sequence" ["indexBack_word"]

indexFront_bits :: forall sym.
  W4.IsSymExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  SeqMap (What4 sym) (GenValue (What4 sym)) ->
  TValue ->
  [SBit (What4 sym)] ->
  SEval (What4 sym) (Value sym)
indexFront_bits sym mblen _a xs _ix bits0 = go 0 (length bits0) bits0
 where
  go :: Integer -> Int -> [W4.Pred sym] -> W4Eval sym (Value sym)
  go i _k []
    -- For indices out of range, fail
    | Nat n <- mblen
    , i >= n
    = raiseError sym (InvalidIndex (Just i))

    | otherwise
    = lookupSeqMap xs i

  go i k (b:bs)
    -- Fail early when all possible indices we could compute from here
    -- are out of bounds
    | Nat n <- mblen
    , (i `shiftL` k) >= n
    = raiseError sym (InvalidIndex Nothing)

    | otherwise
    = iteValue sym b
         (go ((i `shiftL` 1) + 1) (k-1) bs)
         (go  (i `shiftL` 1)      (k-1) bs)

indexBack_bits ::
  W4.IsSymExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  SeqMap (What4 sym) (GenValue (What4 sym)) ->
  TValue ->
  [SBit (What4 sym)] ->
  SEval (What4 sym) (Value sym)
indexBack_bits sym (Nat n) a xs ix idx = indexFront_bits sym (Nat n) a (reverseSeqMap n xs) ix idx
indexBack_bits _ Inf _ _ _ _ = evalPanic "Expected finite sequence" ["indexBack_bits"]


-- | Compare a symbolic word value with a concrete integer.
wordValueEqualsInteger :: forall sym.
  W4.IsSymExprBuilder sym =>
  What4 sym ->
  WordValue (What4 sym) ->
  Integer ->
  W4Eval sym (W4.Pred sym)
wordValueEqualsInteger sym wv i
  | wordValueSize sym wv < widthInteger i = return (W4.falsePred w4sym)
  | otherwise =
    case wv of
      WordVal w -> liftIO (SW.bvEq w4sym w =<< SW.bvLit w4sym (SW.bvWidth w) i)
      _ -> liftIO . bitsAre i =<< enumerateWordValueRev sym wv -- little-endian
  where
    w4sym = w4 sym

    bitsAre :: Integer -> [W4.Pred sym] -> IO (W4.Pred sym)
    bitsAre n [] = pure (W4.backendPred w4sym (n == 0))
    bitsAre n (b : bs) =
      do pb  <- bitIs (testBit n 0) b
         pbs <- bitsAre (n `shiftR` 1) bs
         W4.andPred w4sym pb pbs

    bitIs :: Bool -> W4.Pred sym -> IO (W4.Pred sym)
    bitIs b x = if b then pure x else W4.notPred w4sym x

updateFrontSym ::
  W4.IsSymExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  SeqMap (What4 sym) (GenValue (What4 sym)) ->
  Either (SInteger (What4 sym)) (WordValue (What4 sym)) ->
  SEval (What4 sym) (Value sym) ->
  SEval (What4 sym) (SeqMap (What4 sym) (GenValue (What4 sym)))
updateFrontSym sym _len _eltTy vs (Left idx) val =
  case W4.asInteger idx of
    Just i -> return $ updateSeqMap vs i val
    Nothing -> return $ IndexSeqMap $ \i ->
      do b <- intEq sym idx =<< integerLit sym i
         iteValue sym b val (lookupSeqMap vs i)

updateFrontSym sym _len _eltTy vs (Right wv) val =
  case wv of
    WordVal w | Just j <- SW.bvAsUnsignedInteger w ->
      return $ updateSeqMap vs j val
    _ ->
      memoMap sym $ IndexSeqMap $ \i ->
      do b <- wordValueEqualsInteger sym wv i
         iteValue sym b val (lookupSeqMap vs i)

updateBackSym ::
  W4.IsSymExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  SeqMap (What4 sym) (GenValue (What4 sym)) ->
  Either (SInteger (What4 sym)) (WordValue (What4 sym)) ->
  SEval (What4 sym) (Value sym) ->
  SEval (What4 sym) (SeqMap (What4 sym) (GenValue (What4 sym)))
updateBackSym _ Inf _ _ _ _ = evalPanic "Expected finite sequence" ["updateBackSym"]

updateBackSym sym (Nat n) _eltTy vs (Left idx) val =
  case W4.asInteger idx of
    Just i -> return $ updateSeqMap vs (n - 1 - i) val
    Nothing -> return $ IndexSeqMap $ \i ->
      do b <- intEq sym idx =<< integerLit sym (n - 1 - i)
         iteValue sym b val (lookupSeqMap vs i)

updateBackSym sym (Nat n) _eltTy vs (Right wv) val =
  case wv of
    WordVal w | Just j <- SW.bvAsUnsignedInteger w ->
      return $ updateSeqMap vs (n - 1 - j) val
    _ ->
      memoMap sym $ IndexSeqMap $ \i ->
      do b <- wordValueEqualsInteger sym wv (n - 1 - i)
         iteValue sym b val (lookupSeqMap vs i)


updateFrontSym_word ::
  W4.IsSymExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  WordValue (What4 sym) ->
  Either (SInteger (What4 sym)) (WordValue (What4 sym)) ->
  SEval (What4 sym) (GenValue (What4 sym)) ->
  SEval (What4 sym) (WordValue (What4 sym))
updateFrontSym_word _ Inf _ _ _ _ = evalPanic "Expected finite sequence" ["updateFrontSym_word"]

updateFrontSym_word sym (Nat _) eltTy ls@(LargeBitsVal n _bv) idx val =
  largeBitsVal n <$> updateFrontSym sym (Nat n) eltTy (asBitsMap' sym ls) idx val

updateFrontSym_word sym (Nat n) eltTy (ThunkWordVal _ m) idx val
  | isReady sym m =
       do x <- m
          updateFrontSym_word sym (Nat n) eltTy x idx val
  | otherwise =
       do m' <- sDelay sym $
                  do x <- m
                     updateFrontSym_word sym (Nat n) eltTy x idx val
          pure (ThunkWordVal n m')

updateFrontSym_word sym (Nat n) eltTy (WordVal bv) (Left idx) val =
  do idx' <- wordFromInt sym n idx
     updateFrontSym_word sym (Nat n) eltTy (WordVal bv) (Right (WordVal idx')) val

updateFrontSym_word sym (Nat n) eltTy bv (Right wv) val =
  case wv of
    WordVal idx
      | Just j <- SW.bvAsUnsignedInteger idx ->
          updateWordValue sym bv j (fromVBit <$> val)

      | WordVal bw <- bv ->
        WordVal <$>
          do b <- fromVBit <$> val
             let sz = SW.bvWidth bw
             highbit <- liftIO (SW.bvLit (w4 sym) sz (bit (fromInteger (sz-1))))
             msk <- w4bvLshr (w4 sym) highbit idx
             liftIO $
               case W4.asConstantPred b of
                 Just True  -> SW.bvOr  (w4 sym) bw msk
                 Just False -> SW.bvAnd (w4 sym) bw =<< SW.bvNot (w4 sym) msk
                 Nothing ->
                   do q <- SW.bvFill (w4 sym) sz b
                      bw' <- SW.bvAnd (w4 sym) bw =<< SW.bvNot (w4 sym) msk
                      SW.bvXor (w4 sym) bw' =<< SW.bvAnd (w4 sym) q msk

    _ -> largeBitsVal (wordValueSize sym wv) <$>
           updateFrontSym sym (Nat n) eltTy (asBitsMap' sym bv) (Right wv) val


updateBackSym_word ::
  W4.IsSymExprBuilder sym =>
  What4 sym ->
  Nat' ->
  TValue ->
  WordValue (What4 sym) ->
  Either (SInteger (What4 sym)) (WordValue (What4 sym)) ->
  SEval (What4 sym) (GenValue (What4 sym)) ->
  SEval (What4 sym) (WordValue (What4 sym))
updateBackSym_word _ Inf _ _ _ _ = evalPanic "Expected finite sequence" ["updateBackSym_word"]

updateBackSym_word sym (Nat _) eltTy lb@(LargeBitsVal n _bv) idx val =
  largeBitsVal n <$> updateBackSym sym (Nat n) eltTy (asBitsMap' sym lb) idx val

updateBackSym_word sym (Nat n) eltTy (ThunkWordVal _ m) idx val
  | isReady sym m =
       do x <- m
          updateBackSym_word sym (Nat n) eltTy x idx val
  | otherwise =
       do m' <- sDelay sym $
                  do x <- m
                     updateBackSym_word sym (Nat n) eltTy x idx val
          pure (ThunkWordVal n m')

updateBackSym_word sym (Nat n) eltTy (WordVal bv) (Left idx) val =
  do idx' <- wordFromInt sym n idx
     updateBackSym_word sym (Nat n) eltTy (WordVal bv) (Right (WordVal idx')) val

updateBackSym_word sym (Nat n) eltTy bv (Right wv) val =
  case wv of
    WordVal idx
      | Just j <- SW.bvAsUnsignedInteger idx ->
          updateWordValue sym bv (n - 1 - j) (fromVBit <$> val)

      | WordVal bw <- bv ->
        WordVal <$>
          do b <- fromVBit <$> val
             let sz = SW.bvWidth bw
             lowbit <- liftIO (SW.bvLit (w4 sym) sz 1)
             msk <- w4bvShl (w4 sym) lowbit idx
             liftIO $
               case W4.asConstantPred b of
                 Just True  -> SW.bvOr  (w4 sym) bw msk
                 Just False -> SW.bvAnd (w4 sym) bw =<< SW.bvNot (w4 sym) msk
                 Nothing ->
                   do q <- SW.bvFill (w4 sym) sz b
                      bw' <- SW.bvAnd (w4 sym) bw =<< SW.bvNot (w4 sym) msk
                      SW.bvXor (w4 sym) bw' =<< SW.bvAnd (w4 sym) q msk

    _ -> largeBitsVal (wordValueSize sym wv) <$>
           updateBackSym sym (Nat n) eltTy (asBitsMap' sym bv) (Right wv) val
