-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

module Cryptol.Prims.Types (typeOf) where

import Cryptol.Prims.Syntax
import Cryptol.TypeCheck.AST
import Cryptol.Utils.Panic(panic)

-- | Types of built-in constants.
typeOf :: ECon -> Schema
typeOf econ =
  case econ of

    ECTrue  -> Forall [] [] tBit
    ECFalse -> Forall [] [] tBit

    -- {at,len} (fin len) => [len][8] -> at
    ECError ->
      let aT  = var 0 KType
          len = var 1 KNum
      in forAllNamed [ (Just "at", aT), (Just "len",len) ]
                     [ pFin len ]
                     (tSeq len (tWord (tNum (8::Int))) `tFun` aT)

    -- Infinite word sequences
    -- {a} (fin a) => [a] -> [inf][a]
    ECInfFrom ->
      let bits = var 0 KNum
      in forAllNamed [ (Just "bits", bits) ]
                     [ pFin bits ]
                     (tWord bits `tFun` tSeq tInf (tWord bits))

    -- {a} (fin a) => [a] -> [a] -> [inf][a]
    ECInfFromThen ->
      let bits = var 0 KNum
      in forAllNamed [ (Just "bits", bits) ]
                     [ pFin bits ]
                    (tWord bits `tFun` tWord bits `tFun` tSeq tInf (tWord bits))

    -- Static word sequences
    -- fromThen : {first,next,bits}
    --             ( fin first, fin next, fin bits
    --             , bits >= width first, bits >= width next
    --             , lengthFromThen first next bits == len
    --             )
    --          => [len] [bits]
    ECFromThen ->
      let first = var 0 KNum
          next  = var 1 KNum
          bits  = var 3 KNum
          len   = var 4 KNum
      in forAllNamed [ (Just "first", first)
                     , (Just "next", next)
                     , (Just "bits", bits)
                     , (Just "len", len)
                     ]
        [ pFin first, pFin next, pFin bits
        , bits >== tWidth first, bits >== tWidth next
        , tLenFromThen first next bits =#= len
        ]
        (tSeq len (tWord bits))

    {- { first, last, bits }
          (fin last, fin bits, last >= first, bits >= width last)
        => [1 + (last - first)] [bits]
    -}
    ECFromTo ->
      let first = var 0 KNum
          lst   = var 1 KNum
          bits  = var 3 KNum
      in forAllNamed [ (Just "first", first)
                     , (Just "last", lst)
                     , (Just "bits", bits)
                     ]
        [ pFin lst, pFin bits, lst >== first, bits >== tWidth lst ]
        (tSeq (tNum (1 :: Int) .+. (lst .-. first)) (tWord bits))

    ECFromThenTo ->
      let first = var 0 KNum
          next  = var 1 KNum
          lst   = var 2 KNum
          bits  = var 4 KNum
          len   = var 5 KNum
      in forAllNamed [ (Just "first", first)
                     , (Just "next", next)
                     , (Just "last", lst)
                     , (Just "bits", bits)
                     , (Just "len", len)
                     ]
        [ pFin first, pFin next, pFin lst, pFin bits
        , bits >== tWidth first, bits >== tWidth next, bits >== tWidth lst
        , tLenFromThenTo first next lst =#= len
        ]
        (tSeq len (tWord bits))



    -- { val, bits } (fin val, fin bits, bits >= width val) => [bits]
    ECDemote ->
      let val  = var 0 KNum
          bits = var 1 KNum
      in forAllNamed [ (Just "val", val), (Just "bits", bits) ]
                     [ pFin val, pFin bits, bits >== tWidth val ] (tWord bits)

    -- Polynomials

    -- {a,b} (fin a, fin b) => [a] -> [b] -> [max 1 (a + b) - 1]
    ECPMul ->
      let a = var 0 KNum
          b = var 1 KNum
      in forAllNamed [ (Nothing, a), (Nothing, b) ]
                     [ pFin a, pFin b ]
                     $ tWord a `tFun` tWord b `tFun`
                       tWord (tMax (tNum (1::Int)) (a .+. b) .-. tNum (1::Int))

    -- {a,b} (fin a, fin b) => [a] -> [b] -> [a]
    ECPDiv ->
      let a = var 0 KNum
          b = var 1 KNum
      in forAllNamed [ (Nothing, a), (Nothing, b) ]
                     [ pFin a, pFin b ]
                     $ tWord a `tFun` tWord b `tFun` tWord a

    -- {a,b} (fin a, fin b) => [a] -> [b+1] -> [b]
    ECPMod ->
      let a = var 0 KNum
          b = var 1 KNum
      in forAllNamed [ (Nothing, a), (Nothing, b) ]
                     [ pFin a, pFin b ]
                     $ tWord a `tFun` tWord (tNum (1::Int) .+. b) `tFun` tWord b



    -- Arith
    ECPlus        -> arith2
    ECMinus       -> arith2
    ECMul         -> arith2
    ECDiv         -> arith2
    ECMod         -> arith2
    ECExp         -> arith2
    ECLg2         -> arith1
    ECNeg         -> arith1

    -- Cmp
    ECLt          -> rel2
    ECGt          -> rel2
    ECLtEq        -> rel2
    ECGtEq        -> rel2
    ECEq          -> rel2
    ECNotEq       -> rel2
    ECFunEq       -> cmpFun
    ECFunNotEq    -> cmpFun
    ECMin         -> cmp2
    ECMax         -> cmp2

    -- Logic
    ECAnd         -> logic2
    ECOr          -> logic2
    ECXor         -> logic2
    ECCompl       -> logic1
    ECZero        -> logic0

    ECShiftL      -> logicShift
    ECShiftR      -> logicShift
    ECRotL        -> logicRot
    ECRotR        -> logicRot

    -- {a,b,c} (fin b) => [a][b]c -> [a * b]c
    ECJoin        ->
      let parts = var 0 KNum
          each  = var 1 KNum
          a     = var 2 KType
       in forAllNamed
          [ (Just "parts", parts)
          , (Just "each", each)
          , (Nothing, a)
          ]
          [ pFin each ]
        $ tSeq parts (tSeq each a) `tFun` tSeq (parts .*. each) a

    -- {a,b,c} (fin b) => [a * b] c -> [a][b] c
    ECSplit       ->
      let parts = var 0 KNum
          each  = var 1 KNum
          a     = var 2 KType
       in forAllNamed
          [ (Just "parts", parts)
          , (Just "each", each)
          , (Nothing, a)
          ]
          [ pFin each ]
        $ tSeq (parts .*. each) a `tFun` tSeq parts (tSeq each a)

    -- {a,b} (fin a) => [a] b -> [a] b
    ECReverse ->
      let a = var 0 KNum
          b = var 1 KType
      in forAllNamed [ (Nothing, a), (Nothing, b) ]
                     [ pFin a ]
                     (tSeq a b `tFun` tSeq a b)

    -- {a,b,c} [a][b]c -> [b][a]c
    ECTranspose ->
      let a = var 0 KNum
          b = var 1 KNum
          c = var 2 KType
      in forAllNamed [ (Nothing, a), (Nothing, b), (Nothing, c) ]
                     []
                     (tSeq a (tSeq b c) `tFun` tSeq b (tSeq a c))

    -- Sequence selectors
    ECAt ->
      let n = var 0 KNum
          a = var 1 KType
          i = var 2 KNum
      in forAll [n,a,i] [ pFin i ] (tSeq n a `tFun` tWord i `tFun` a)

    ECAtRange ->
      let n = var 0 KNum
          a = var 1 KType
          m = var 2 KNum
          i = var 3 KNum
      in forAll [n,a,m,i] [ pFin i ]
         (tSeq n a `tFun` tSeq m (tWord i) `tFun` tSeq m a)

    ECAtBack ->
      let n = var 0 KNum
          a = var 1 KType
          i = var 2 KNum
      in forAll [n,a,i] [ pFin n, pFin i ] (tSeq n a `tFun` tWord i `tFun` a)

    ECAtRangeBack ->
      let n = var 0 KNum
          a = var 1 KType
          m = var 2 KNum
          i = var 3 KNum
      in forAll [n,a,m,i] [ pFin n, pFin i ]
          (tSeq n a `tFun` tSeq m (tWord i) `tFun` tSeq m a)

    -- {a,b,c} (fin a) => [a+b] c -> ([a]c,[b]c)
    ECSplitAt ->
      let front = var 0 KNum
          back  = var 1 KNum
          a     = var 2 KType
       in forAllNamed
          [ (Just "front", front)
          , (Just "back", back)
          , (Nothing, a)
          ] [ pFin front ]
        $ tSeq (front .+. back) a `tFun` tTuple [tSeq front a, tSeq back a]

    -- {a,b,d} (fin a) => [a] d -> [b] d -> [a + b] d
    ECCat ->
      let a = var 0 KNum
          b = var 1 KNum
          d = var 3 KType
      in forAllNamed [ (Just "front", a)
                     , (Just "back" , b)
                     , (Nothing,d)
                     ] [ pFin a ]
                     $ tSeq a d `tFun` tSeq b d `tFun` tSeq (a .+. b) d

    -- {a} => [32] -> a
    ECRandom ->
      let a = var 0 KType
      in forAll [a] [] (tWord (tNum (32 :: Int)) `tFun` a)
  where
  var x k         = TVar (TVBound x k)

  toTP (mb,TVar (TVBound x k)) = TParam { tpName = fmap (mkUnqual . Name) mb
                                          , tpUnique = x, tpKind = k }
  toTP (_,x)         = panic "Cryptol.Prims.Types.typeOf"
                            [ "Not TBound", show x ]


  forAllNamed xs ys p  = Forall (map toTP xs) ys p

  forAll xs = forAllNamed (zip (repeat Nothing) xs)


  -- {a} (Arith a) => a -> a -> a
  arith2 = let a = var 0 KType
           in forAll [a] [ pArith a ] $ a `tFun` a `tFun` a


  -- {a} (Arith a) => a -> a
  arith1 = let a = var 0 KType
           in forAll [a] [ pArith a ] $ a `tFun` a

  -- {a} (Cmp a) => a -> a -> Bit
  rel2 = let a = var 0 KType
         in forAll [a] [ pCmp a ] $ a `tFun` a `tFun` tBit

  -- {a} (Cmp a) => a -> a -> a
  cmp2 = let a = var 0 KType
         in forAll [a] [ pCmp a ] $ a `tFun` a `tFun` a

  -- {a b} (Cmp b) => (a -> b) -> (a -> b) -> a -> Bit
  cmpFun = let a = var 0 KType
               b = var 1 KType
           in forAll [a,b] [ pCmp b ]
            $ (a `tFun` b) `tFun` (a `tFun` b) `tFun` a `tFun` tBit

  -- {a} a
  logic0 = let a = var 0 KType
           in forAll [a] [] a

  -- {a} a -> a
  logic1 = let a = var 0 KType
           in forAll [a] [] (a `tFun` a)

  -- {a} a -> a -> a
  logic2 = let a = var 0 KType
           in forAll [a] [] (a `tFun` a `tFun` a)


  -- {m,n,a} (fin n) => [m] a -> [n] -> [m] a
  logicShift = let m = var 0 KNum
                   n = var 1 KNum
                   a = var 2 KType
               in forAll [m,n,a] [pFin n]
                $ tSeq m a `tFun` tWord n `tFun` tSeq m a

  -- {m,n,a} (fin n, fin m) => [m] a -> [n] -> [m] a
  logicRot = let m = var 0 KNum
                 n = var 1 KNum
                 a = var 2 KType
             in forAll [m,n,a] [pFin m, pFin n]
              $ tSeq m a `tFun` tWord n `tFun` tSeq m a
