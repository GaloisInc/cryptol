-- |
-- Module      :  Cryptol.Eval.What4
-- Copyright   :  (c) 2020 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com

{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
module Cryptol.Eval.What4
  ( What4(..)
  , W4Result(..)
  , W4Defs(..)
  , W4Eval
  , w4Eval
  , Value
  , primTable
  ) where


import qualified Data.Map as Map

import qualified What4.Interface as W4

import Cryptol.Eval.Backend
import Cryptol.Eval.Generic
import Cryptol.Eval.Value
import Cryptol.Eval.What4.Value
import Cryptol.Eval.What4.Float(floatPrims)
import Cryptol.Testing.Random( randomV )
import Cryptol.Utils.Ident

-- See also Cryptol.Prims.Eval.primTable
primTable :: W4.IsSymExprBuilder sym => sym -> Map.Map PrimIdent (Value sym)
primTable w4sym = let sym = What4 w4sym in
  Map.union (floatPrims sym) $
  Map.fromList $ map (\(n, v) -> (prelPrim n, v))

  [ -- Literals
    ("True"        , VBit (bitLit sym True))
  , ("False"       , VBit (bitLit sym False))
  , ("number"      , ecNumberV sym) -- Converts a numeric type into its corresponding value.
                                    -- { val, rep } (Literal val rep) => rep
  , ("fraction"    , ecFractionV sym)
  , ("ratio"       , ratioV sym)

    -- Zero
  , ("zero"        , VPoly (zeroV sym))

    -- Logic
  , ("&&"          , binary (andV sym))
  , ("||"          , binary (orV sym))
  , ("^"           , binary (xorV sym))
  , ("complement"  , unary  (complementV sym))

    -- Ring
  , ("fromInteger" , fromIntegerV sym)
  , ("+"           , binary (addV sym))
  , ("-"           , binary (subV sym))
  , ("negate"      , unary (negateV sym))
  , ("*"           , binary (mulV sym))

    -- Integral
  , ("toInteger"   , toIntegerV sym)
  , ("/"           , binary (divV sym))
  , ("%"           , binary (modV sym))
  , ("^^"          , expV sym)
  , ("infFrom"     , infFromV sym)
  , ("infFromThen" , infFromThenV sym)

    -- Field
  , ("recip"       , recipV sym)
  , ("/."          , fieldDivideV sym)

    -- Round
  , ("floor"       , unary (floorV sym))
  , ("ceiling"     , unary (ceilingV sym))
  , ("trunc"       , unary (truncV sym))
  , ("roundAway"   , unary (roundAwayV sym))
  , ("roundToEven" , unary (roundToEvenV sym))

    -- Word operations
  , ("/$"          , sdivV sym)
  , ("%$"          , smodV sym)
  , ("lg2"         , lg2V sym)
  , (">>$"         , sshrV sym)

    -- Cmp
  , ("<"           , binary (lessThanV sym))
  , (">"           , binary (greaterThanV sym))
  , ("<="          , binary (lessThanEqV sym))
  , (">="          , binary (greaterThanEqV sym))
  , ("=="          , binary (eqV sym))
  , ("!="          , binary (distinctV sym))

    -- SignedCmp
  , ("<$"          , binary (signedLessThanV sym))

    -- Finite enumerations
  , ("fromTo"      , fromToV sym)
  , ("fromThenTo"  , fromThenToV sym)

    -- Sequence manipulations
  , ("#"          , -- {a,b,d} (fin a) => [a] d -> [b] d -> [a + b] d
     ilam $ \ front ->
     nlam $ \ back  ->
     tlam $ \ elty  ->
     lam  $ \ l     -> return $
     lam  $ \ r     -> ccatV sym front back elty l r)

  , ("join"       ,
     nlam $ \ parts ->
     ilam $ \ each  ->
     tlam $ \ a     ->
     lam  $ \ x     -> joinV sym parts each a x)

  , ("split"      ,
     nlam $ \ parts ->
     ilam $ \ each  ->
     tlam $ \ a     ->
     lam  $ \ x     -> splitV sym parts each a x)

  , ("splitAt"    ,
     ilam $ \ front ->
     nlam $ \ back  ->
     tlam $ \ a     ->
     lam  $ \ x     -> splitAtV sym front back a x)

  , ("take"       ,
     nlam $ \ front ->
     nlam $ \ _back ->
     tlam $ \ a     ->
      lam $ \ xs    -> takeV sym front a xs)

    -- Shifts and rotates
  , ("<<"          , logicShift sym "<<"  shiftIntShrink shiftWordShrink
                        leftShiftSeqMap rightShiftSeqMap)
  , (">>"          , logicShift sym ">>"  shiftIntShrink shiftWordShrink
                        rightShiftSeqMap leftShiftSeqMap)
  , ("<<<"         , logicShift sym "<<<" rotateIntShrink rotateWordShrink
                        leftRotateSeqMap rightRotateSeqMap)
  , (">>>"         , logicShift sym ">>>" rotateIntShrink rotateWordShrink
                        rightRotateSeqMap leftRotateSeqMap)

    -- Indexing and updates
  , ("@"           , indexPrim sym (indexFront_int sym) (indexFront_word sym))
  , ("!"           , indexPrim sym (indexBack_int sym)  (indexBack_word sym))

  , ("update"      , updatePrim sym (updateFrontSym sym))
  , ("updateEnd"   , updatePrim sym (updateBackSym sym))

    -- Misc

  , ("foldl"       , foldlV sym)
  , ("foldl'"      , foldl'V sym)

  , ("seq"         ,
     tlam $ \_a ->
     tlam $ \_b ->
      lam $ \x -> pure $
      lam $ \y ->
        do _ <- x
           y)

  , ("deepseq"     ,
      tlam $ \_a ->
      tlam $ \_b ->
       lam $ \x -> pure $
       lam $ \y ->
         do _ <- forceValue =<< x
            y)

  , ("parmap"      , parmapV sym)

  , ("fromZ"       , fromZV sym)

    -- {at,len} (fin len) => [len][8] -> at
  , ("error"       ,
      tlam $ \a ->
      nlam $ \_ ->
      VFun $ \s -> errorV sym a =<< (valueToString sym =<< s))

  , ("random"      ,
      tlam $ \a ->
      wlam sym $ \x ->
         case wordAsLit sym x of
           Just (_,i)  -> randomV sym a i
           Nothing -> cryUserError sym "cannot evaluate 'random' with symbolic inputs")

     -- The trace function simply forces its first two
     -- values before returing the third in the symbolic
     -- evaluator.
  , ("trace",
      nlam $ \_n ->
      tlam $ \_a ->
      tlam $ \_b ->
       lam $ \s -> return $
       lam $ \x -> return $
       lam $ \y -> do
         _ <- s
         _ <- x
         y)
  ]
