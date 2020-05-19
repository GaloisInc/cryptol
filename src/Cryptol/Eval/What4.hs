-- |
-- Module      :  Cryptol.Eval.What4
-- Copyright   :  (c) 2020 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com

{-# LANGUAGE ViewPatterns #-}
module Cryptol.Eval.What4
  ( What4(..)
  , W4Result(..)
  , W4Eval(..)
  , Value
  , evalPrim
  ) where


import           Control.Monad (join)
import qualified Data.Map as Map
import qualified Data.Text as T

import qualified What4.Interface as W4

import Cryptol.Eval.Backend
import Cryptol.Eval.Generic
import Cryptol.Eval.Type (finNat')
import Cryptol.Eval.Value
import Cryptol.Eval.What4.Value
import Cryptol.Eval.What4.FloatPrims(floatPrims)
import Cryptol.Testing.Random( randomV )
import Cryptol.Utils.Ident


evalPrim :: W4.IsExprBuilder sym => sym -> Ident -> Maybe (Value sym)
evalPrim sym prim = Map.lookup prim (primTable sym)

-- See also Cryptol.Prims.Eval.primTable
primTable :: W4.IsExprBuilder sym => sym -> Map.Map Ident (Value sym)
primTable w4sym = let sym = What4 w4sym in
  Map.union (floatPrims sym) $
  Map.fromList $ map (\(n, v) -> (mkIdent (T.pack n), v))
  [ -- Literals
    ("True"        , VBit (bitLit sym True))
  , ("False"       , VBit (bitLit sym False))
  , ("number"      , ecNumberV sym) -- Converts a numeric type into its corresponding value.
                                    -- { val, rep } (Literal val rep) => rep

    -- Arith
  , ("fromInteger" , ecFromIntegerV sym)
  , ("+"           , binary (addV sym)) -- {a} (Arith a) => a -> a -> a
  , ("-"           , binary (subV sym)) -- {a} (Arith a) => a -> a -> a
  , ("*"           , binary (mulV sym)) -- {a} (Arith a) => a -> a -> a
  , ("/"           , binary (divV sym)) -- {a} (Arith a) => a -> a -> a
  , ("%"           , binary (modV sym)) -- {a} (Arith a) => a -> a -> a
  , ("/$"          , binary (sdivV sym))
  , ("%$"          , binary (smodV sym))
  , ("^^"          , binary (expV sym))
  , ("lg2"         , unary (lg2V sym))
  , ("negate"      , unary (negateV sym))
  , ("infFrom"     , infFromV sym)
  , ("infFromThen" , infFromThenV sym)

    -- Cmp
  , ("<"           , binary (lessThanV sym))
  , (">"           , binary (greaterThanV sym))
  , ("<="          , binary (lessThanEqV sym))
  , (">="          , binary (greaterThanEqV sym))
  , ("=="          , binary (eqV sym))
  , ("!="          , binary (distinctV sym))

    -- SignedCmp
  , ("<$"          , binary (signedLessThanV sym))

    -- Logic
  , ("&&"          , binary (andV sym))
  , ("||"          , binary (orV sym))
  , ("^"           , binary (xorV sym))
  , ("complement"  , unary  (complementV sym))

    -- Zero
  , ("zero"        , VPoly (zeroV sym))

    -- Finite enumerations
  , ("fromTo"      , fromToV sym)
  , ("fromThenTo"  , fromThenToV sym)

    -- Conversions to Integer
  , ("toInteger"   , ecToIntegerV sym)
  , ("fromZ"       , ecFromZ sym)

    -- Sequence manipulations
  , ("#"          , -- {a,b,d} (fin a) => [a] d -> [b] d -> [a + b] d
     nlam $ \ front ->
     nlam $ \ back  ->
     tlam $ \ elty  ->
     lam  $ \ l     -> return $
     lam  $ \ r     -> join (ccatV sym front back elty <$> l <*> r))

  , ("join"       ,
     nlam $ \ parts ->
     nlam $ \ (finNat' -> each)  ->
     tlam $ \ a     ->
     lam  $ \ x     ->
       joinV sym parts each a =<< x)

  , ("split"       , ecSplitV sym)

  , ("splitAt"    ,
     nlam $ \ front ->
     nlam $ \ back  ->
     tlam $ \ a     ->
     lam  $ \ x     ->
       splitAtV sym front back a =<< x)

  , ("reverse"    , nlam $ \_a ->
                    tlam $ \_b ->
                     lam $ \xs -> reverseV sym =<< xs)

  , ("transpose"  , nlam $ \a ->
                    nlam $ \b ->
                    tlam $ \c ->
                     lam $ \xs -> transposeV sym a b c =<< xs)

    -- Shifts and rotates
  , ("<<"          , logicShift sym "<<"  (w4bvShl w4sym) shiftLeftReindex)
  , (">>"          , logicShift sym ">>"  (w4bvLshr w4sym) shiftRightReindex)
  , ("<<<"         , logicShift sym "<<<" (w4bvRol w4sym) rotateLeftReindex)
  , (">>>"         , logicShift sym ">>>" (w4bvRor w4sym) rotateRightReindex)
  , (">>$"         , sshrV w4sym)

    -- Indexing and updates
  , ("@"           , indexPrim sym (indexFront_bits w4sym) (indexFront w4sym))
  , ("!"           , indexPrim sym (indexBack_bits w4sym) (indexBack w4sym))

  , ("update"      , updatePrim sym (updateFrontSym_word w4sym) (updateFrontSym w4sym))
  , ("updateEnd"   , updatePrim sym (updateBackSym_word w4sym)  (updateBackSym w4sym))

    -- Misc

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



