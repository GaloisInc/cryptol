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
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
module Cryptol.Eval.Concrete
  ( module Cryptol.Eval.Concrete.Value
  , evalPrim
  , toExpr
  ) where

import Control.Monad (join,guard,zipWithM)
import Data.List(sortBy)
import Data.Ord(comparing)
import Data.Bits (Bits(..))
import MonadLib( ChoiceT, findOne, lift )

import qualified Data.Map.Strict as Map
import qualified Data.Text as T

import Cryptol.TypeCheck.Solver.InfNat (Nat'(..))
import Cryptol.Eval.Backend
import Cryptol.Eval.Concrete.Value
import Cryptol.Eval.Generic hiding (logicShift)
import Cryptol.Eval.Monad
import Cryptol.Eval.Type
import Cryptol.Eval.Value
import Cryptol.ModuleSystem.Name
import Cryptol.Testing.Random (randomV)
import Cryptol.TypeCheck.AST as AST
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.Ident (Ident,mkIdent)
import Cryptol.Utils.PP
import Cryptol.Utils.Logger(logPrint)



-- Value to Expression conversion ----------------------------------------------

-- | Given an expected type, returns an expression that evaluates to
-- this value, if we can determine it.
--
-- XXX: View patterns would probably clean up this definition a lot.
toExpr :: PrimMap -> AST.Type -> Value -> Eval (Maybe AST.Expr)
toExpr prims t0 v0 = findOne (go t0 v0)
  where

  prim n = ePrim prims (mkIdent (T.pack n))

  go :: AST.Type -> Value -> ChoiceT Eval Expr
  go ty val = case (tNoUser ty, val) of
    (TRec (sortBy (comparing fst) -> tfs), VRecord vfs) -> do
      let fns = Map.keys vfs
      guard (map fst tfs == fns)
      fes <- zipWithM go (map snd tfs) =<< lift (sequence (Map.elems vfs))
      return $ ERec (zip fns fes)
    (TCon (TC (TCTuple tl)) ts, VTuple tvs) -> do
      guard (tl == (length tvs))
      ETuple `fmap` (zipWithM go ts =<< lift (sequence tvs))
    (TCon (TC TCBit) [], VBit True ) -> return (prim "True")
    (TCon (TC TCBit) [], VBit False) -> return (prim "False")
    (TCon (TC TCInteger) [], VInteger i) ->
      return $ ETApp (ETApp (prim "number") (tNum i)) ty
    (TCon (TC TCIntMod) [_n], VInteger i) ->
      return $ ETApp (ETApp (prim "number") (tNum i)) ty
    (TCon (TC TCSeq) [a,b], VSeq 0 _) -> do
      guard (a == tZero)
      return $ EList [] b
    (TCon (TC TCSeq) [a,b], VSeq n svs) -> do
      guard (a == tNum n)
      ses <- mapM (go b) =<< lift (sequence (enumerateSeqMap n svs))
      return $ EList ses b
    (TCon (TC TCSeq) [a,(TCon (TC TCBit) [])], VWord _ wval) -> do
      BV w v <- lift (asWordVal Concrete =<< wval)
      guard (a == tNum w)
      return $ ETApp (ETApp (prim "number") (tNum v)) ty
    (_, VStream _) -> fail "cannot construct infinite expressions"
    (_, VFun    _) -> fail "cannot convert function values to expressions"
    (_, VPoly   _) -> fail "cannot convert polymorphic values to expressions"
    _ -> do doc <- lift (ppValue Concrete defaultPPOpts val)
            panic "Cryptol.Eval.Value.toExpr"
             ["type mismatch:"
             , pretty ty
             , render doc
             ]


-- Primitives ------------------------------------------------------------------

evalPrim :: Ident -> Maybe Value
evalPrim prim = Map.lookup prim primTable

primTable :: Map.Map Ident Value
primTable = let sym = Concrete in
  Map.fromList $ map (\(n, v) -> (mkIdent (T.pack n), v))
  [ -- Literals
    ("True"       , VBit (bitLit sym True))
  , ("False"      , VBit (bitLit sym False))
  , ("number"     , {-# SCC "Prelude::number" #-}
                    ecNumberV sym)

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
  , ("infFrom"    , {-# SCC "Prelude::infFrom" #-}
                    infFromV sym)
  , ("infFromThen", {-# SCC "Prelude::infFromThen" #-}
                    infFromThenV sym)

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
                         EvalOpts { evalPPOpts, evalLogger } <- getEvalOpts
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
  wlam Concrete $ \(BV i x) -> return $
  lam $ \y ->
   do idx <- y >>= asIndex Concrete ">>$" ix >>= \case
                 Left idx -> pure idx
                 Right wv -> bvVal <$> asWordVal Concrete wv
      let amt   = fromInteger (min i idx)
      let x'    = signedValue i x
      return . VWord i . pure . WordVal . mkBv i $! x' `shiftR` amt

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
  | by >= w   = 0
  | otherwise = mask w (shiftL ival (fromInteger by))

shiftLS :: Nat' -> TValue -> SeqMap Concrete -> Integer -> SeqMap Concrete
shiftLS w ety vs by = IndexSeqMap $ \i ->
  case w of
    Nat len
      | i+by < len -> lookupSeqMap vs (i+by)
      | i    < len -> zeroV Concrete ety
      | otherwise  -> evalPanic "shiftLS" ["Index out of bounds"]
    Inf            -> lookupSeqMap vs (i+by)

shiftRW :: Integer -> Integer -> Integer -> Integer
shiftRW w i by
  | by >= w   = 0
  | otherwise = shiftR i (fromInteger by)

shiftRS :: Nat' -> TValue -> SeqMap Concrete -> Integer -> SeqMap Concrete
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
  WordValue Concrete {- ^ index -} ->
  Eval Value         {- ^ new value at index -} ->
  Eval (SeqMap Concrete)
updateFront _len _eltTy vs w val = do
  idx <- bvVal <$> asWordVal Concrete w
  return $ updateSeqMap vs idx val

updateFront_word ::
  Nat'               {- ^ length of the sequence -} ->
  TValue             {- ^ type of values in the sequence -} ->
  WordValue Concrete {- ^ bit sequence to update -} ->
  WordValue Concrete {- ^ index -} ->
  Eval Value         {- ^ new value at index -} ->
  Eval (WordValue Concrete)
updateFront_word _len _eltTy bs w val = do
  idx <- bvVal <$> asWordVal Concrete w
  updateWordValue Concrete bs idx (fromVBit <$> val)

updateBack ::
  Nat'               {- ^ length of the sequence -} ->
  TValue             {- ^ type of values in the sequence -} ->
  SeqMap Concrete    {- ^ sequence to update -} ->
  WordValue Concrete {- ^ index -} ->
  Eval Value         {- ^ new value at index -} ->
  Eval (SeqMap Concrete)
updateBack Inf _eltTy _vs _w _val =
  evalPanic "Unexpected infinite sequence in updateEnd" []
updateBack (Nat n) _eltTy vs w val = do
  idx <- bvVal <$> asWordVal Concrete w
  return $ updateSeqMap vs (n - idx - 1) val

updateBack_word ::
  Nat'               {- ^ length of the sequence -} ->
  TValue             {- ^ type of values in the sequence -} ->
  WordValue Concrete {- ^ bit sequence to update -} ->
  WordValue Concrete {- ^ index -} ->
  Eval Value         {- ^ new value at index -} ->
  Eval (WordValue Concrete)
updateBack_word Inf _eltTy _bs _w _val =
  evalPanic "Unexpected infinite sequence in updateEnd" []
updateBack_word (Nat n) _eltTy bs w val = do
  idx <- bvVal <$> asWordVal Concrete w
  updateWordValue Concrete bs (n - idx - 1) (fromVBit <$> val)
