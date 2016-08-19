-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Cryptol.Prims.Eval where

import Control.Monad (join, unless)

import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Solver.InfNat (Nat'(..),fromNat,genLog, nMul)
import qualified Cryptol.Eval.Arch as Arch
import Cryptol.Eval.Monad
import Cryptol.Eval.Type
import Cryptol.Eval.Value
import Cryptol.Testing.Random (randomValue)
import Cryptol.Utils.Panic (panic)
import Cryptol.ModuleSystem.Name (asPrim)
import Cryptol.Utils.Ident (Ident,mkIdent)
import Cryptol.Utils.PP

import qualified Data.Foldable as Fold
import Data.List (sortBy)
import qualified Data.Sequence as Seq
import Data.Ord (comparing)
import Data.Bits (Bits(..))

import qualified Data.Map.Strict as Map
import qualified Data.Text as T

import System.Random.TF.Gen (seedTFGen)

-- Primitives ------------------------------------------------------------------

instance EvalPrims Bool BV Integer where
  evalPrim Decl { dName = n, .. }
    | Just prim <- asPrim n, Just val <- Map.lookup prim primTable = val

  evalPrim Decl { .. } =
      panic "Eval" [ "Unimplemented primitive", show dName ]

  iteValue b t f = if b then t else f


primTable :: Map.Map Ident Value
primTable = Map.fromList $ map (\(n, v) -> (mkIdent (T.pack n), v))
  [ ("+"          , {-# SCC "Prelude::(+)" #-}
                    binary (arithBinary (liftBinArith (+)) (+)))
  , ("-"          , {-# SCC "Prelude::(-)" #-}
                    binary (arithBinary (liftBinArith (-)) (-)))
  , ("*"          , {-# SCC "Prelude::(*)" #-}
                    binary (arithBinary (liftBinArith (*)) (*)))
  , ("/"          , {-# SCC "Prelude::(/)" #-}
                    binary (arithBinary (liftBinArith divWrap) divWrap))
  , ("%"          , {-# SCC "Prelude::(%)" #-}
                    binary (arithBinary (liftBinArith modWrap) modWrap))
  , ("^^"         , {-# SCC "Prelude::(^^)" #-}
                    binary (arithBinary modExp integerExp))
  , ("lg2"        , {-# SCC "Prelude::lg2" #-}
                    unary  (arithUnary (liftUnaryArith lg2) lg2))
  , ("negate"     , {-# SCC "Prelude::negate" #-}
                    unary  (arithUnary (liftUnaryArith negate) negate))
  , ("<"          , {-# SCC "Prelude::(<)" #-}
                    binary (cmpOrder "<"  (\o -> o == LT           )))
  , (">"          , {-# SCC "Prelude::(>)" #-}
                    binary (cmpOrder ">"  (\o -> o == GT           )))
  , ("<="         , {-# SCC "Prelude::(<=)" #-}
                    binary (cmpOrder "<=" (\o -> o == LT || o == EQ)))
  , (">="         , {-# SCC "Prelude::(>=)" #-}
                    binary (cmpOrder ">=" (\o -> o == GT || o == EQ)))
  , ("=="         , {-# SCC "Prelude::(==)" #-}
                    binary (cmpOrder "==" (\o ->            o == EQ)))
  , ("!="         , {-# SCC "Prelude::(!=)" #-}
                    binary (cmpOrder "!=" (\o ->            o /= EQ)))
  , ("&&"         , {-# SCC "Prelude::(&&)" #-}
                    binary (logicBinary (.&.) (binBV (.&.)) (.&.)))
  , ("||"         , {-# SCC "Prelude::(||)" #-}
                    binary (logicBinary (.|.) (binBV (.|.)) (.|.)))
  , ("^"          , {-# SCC "Prelude::(^)" #-}
                    binary (logicBinary xor (binBV xor) xor))
  , ("complement" , {-# SCC "Prelude::complement" #-}
                    unary  (logicUnary complement (unaryBV complement) complement))
  , ("toInteger"  , ecToIntegerV)
  , ("fromInteger", ecFromIntegerV)
  , ("<<"         , {-# SCC "Prelude::(<<)" #-}
                    logicShift shiftLW shiftLB shiftLS)
  , (">>"         , {-# SCC "Prelude::(>>)" #-}
                    logicShift shiftRW shiftLB shiftRS)
  , ("<<<"        , {-# SCC "Prelude::(<<<)" #-}
                    logicShift rotateLW rotateLB rotateLS)
  , (">>>"        , {-# SCC "Prelude::(>>>)" #-}
                    logicShift rotateRW rotateRB rotateRS)
  , ("True"       , VBit True)
  , ("False"      , VBit False)

  , ("demote"     , {-# SCC "Prelude::demote" #-}
                    ecDemoteV)
  , ("integer"    , {-# SCC "Prelude::integer" #-}
                    ecIntegerV)

  , ("#"          , {-# SCC "Prelude::(#)" #-}
                    nlam $ \ front ->
                    nlam $ \ back  ->
                    tlam $ \ elty  ->
                    lam  $ \ l     -> return $
                    lam  $ \ r     -> join (ccatV front back elty <$> l <*> r))

  , ("@"          , {-# SCC "Prelude::(@)" #-}
                    indexPrimOne  indexFront_bits indexFront)
  , ("@@"         , {-# SCC "Prelude::(@@)" #-}
                    indexPrimMany indexFront_bits indexFront)
  , ("!"          , {-# SCC "Prelude::(!)" #-}
                    indexPrimOne  indexBack_bits indexBack)
  , ("!!"         , {-# SCC "Prelude::(!!)" #-}
                    indexPrimMany indexBack_bits indexBack)

  , ("update"     , {-# SCC "Prelude::update" #-}
                    updatePrim updateFront_bits updateFront)

  , ("updateEnd"  , {-# SCC "Prelude::updateEnd" #-}
                    updatePrim updateBack_bits updateBack)

  , ("zero"       , {-# SCC "Prelude::zero" #-}
                    tlam zeroV)

  , ("join"       , {-# SCC "Prelude::join" #-}
                    nlam $ \ parts ->
                    nlam $ \ (finNat' -> each)  ->
                    tlam $ \ a     ->
                    lam  $ \ x     ->
                      joinV parts each a =<< x)

  , ("split"      , {-# SCC "Prelude::split" #-}
                    ecSplitV)

  , ("splitAt"    , {-# SCC "Prelude::splitAt" #-}
                    nlam $ \ front ->
                    nlam $ \ back  ->
                    tlam $ \ a     ->
                    lam  $ \ x     ->
                       splitAtV front back a =<< x)

  , ("fromThen"   , {-# SCC "Prelude::fromThen" #-}
                    fromThenV)
  , ("fromTo"     , {-# SCC "Prelude::fromTo" #-}
                    fromToV)
  , ("fromThenTo" , {-# SCC "Prelude::fromThenTo" #-}
                    fromThenToV)
  , ("infFrom"    , {-# SCC "Prelude::infFrom" #-}
                    infFromV)
  , ("infFromThen", {-# SCC "Prelude::infFromThen" #-}
                    infFromThenV)

  , ("error"      , {-# SCC "Prelude::error" #-}
                      tlam $ \a ->
                      nlam $ \_ ->
                       lam $ \s -> errorV a =<< (fromStr =<< s))

  , ("reverse"    , {-# SCC "Prelude::reverse" #-}
                    nlam $ \_a ->
                    tlam $ \_b ->
                     lam $ \xs -> reverseV =<< xs)

  , ("transpose"  , {-# SCC "Prelude::transpose" #-}
                    nlam $ \a ->
                    nlam $ \b ->
                    tlam $ \c ->
                     lam $ \xs -> transposeV a b c =<< xs)

  , ("pmult"       , {-# SCC "Prelude::pmult" #-}
    let mul !res !_ !_ 0 = res
        mul  res bs as n = mul (if even as then res else xor res bs)
                               (bs `shiftL` 1) (as `shiftR` 1) (n-1)
     in nlam $ \(finNat' -> a) ->
        nlam $ \(finNat' -> b) ->
        wlam $ \(bvVal -> x) -> return $
        wlam $ \(bvVal -> y) -> return $ word (max 1 (a + b) - 1) (mul 0 x y b))

  , ("pdiv"        , {-# SCC "Prelude::pdiv" #-}
                     nlam $ \(fromInteger . finNat' -> a) ->
                     nlam $ \(fromInteger . finNat' -> b) ->
                     wlam $ \(bvVal -> x) -> return $
                     wlam $ \(bvVal -> y) -> return $ word (toInteger a)
                                                (fst (divModPoly x a y b)))

  , ("pmod"        , {-# SCC "Prelude::pmod" #-}
                     nlam $ \(fromInteger . finNat' -> a) ->
                     nlam $ \(fromInteger . finNat' -> b) ->
                     wlam $ \(bvVal -> x) -> return $
                     wlam $ \(bvVal -> y) -> return $ word (toInteger b)
                                                (snd (divModPoly x a y (b+1))))
  , ("random"      , {-# SCC "Prelude::random" #-}
                     tlam $ \a ->
                     wlam $ \(bvVal -> x) -> return $ randomV a x)
  , ("trace"       , {-# SCC "Prelude::trace" #-}
                     nlam $ \_n ->
                     tlam $ \_a ->
                     tlam $ \_b ->
                      lam $ \s -> return $
                      lam $ \x -> return $
                      lam $ \y -> do
                         msg <- fromStr =<< s
                         -- FIXME? get PPOPts from elsewhere?
                         doc <- ppValue defaultPPOpts =<< x
                         yv <- y
                         io $ putStrLn $ show $ if null msg then
                                                  doc
                                                else
                                                  text msg <+> doc
                         return yv)
  ]


-- | Make a numeric constant.
ecDemoteV :: BitWord b w i => GenValue b w i
ecDemoteV = nlam $ \valT ->
            nlam $ \bitT ->
            case (valT, bitT) of
              (Nat v, Nat bs) -> word bs v
              _ -> evalPanic "Cryptol.Eval.Prim.evalConst"
                       ["Unexpected Inf in constant."
                       , show valT
                       , show bitT
                       ]

-- | Make an integer constant.
ecIntegerV :: BitWord b w i => GenValue b w i
ecIntegerV = nlam $ \valT ->
             case valT of
               Nat v -> VInteger (integerLit v)
               _ -> evalPanic "Cryptol.Eval.Prim.evalConst"
                        [ "Unexpected Inf in constant."
                        , show valT
                        ]

-- | Convert a word to a non-negative integer.
ecToIntegerV :: BitWord b w i => GenValue b w i
ecToIntegerV =
  nlam $ \ _ ->
  wlam $ \ w -> return $ VInteger (wordToInt w)

-- | Convert an unbounded integer to a packed bitvector.
ecFromIntegerV :: BitWord b w i => GenValue b w i
ecFromIntegerV =
  nlam $ \ a ->
  lam  $ \ x -> do
    val <- x
    case (a, val) of
      (Nat n, VInteger i) -> return $ VWord n $ ready $ WordVal $ wordFromInt n i
      _                   -> evalPanic "fromInteger" ["Invalid arguments"]

--------------------------------------------------------------------------------
divModPoly :: Integer -> Int -> Integer -> Int -> (Integer, Integer)
divModPoly xs xsLen ys ysLen
  | ys == 0   = divideByZero
  | otherwise = go 0 initR (xsLen - degree) todoBits

  where
  downIxes n  = [ n - 1, n - 2 .. 0 ]

  degree      = head [ n | n <- downIxes ysLen, testBit ys n ]

  initR       = xs `shiftR` (xsLen - degree)
  nextR r b   = (r `shiftL` 1) .|. (if b then 1 else 0)

  go !res !r !bitN todo =
     let x = xor r ys
         (res',r') | testBit x degree = (res,             r)
                   | otherwise        = (setBit res bitN, x)
     in case todo of
          b : bs -> go res' (nextR r' b) (bitN-1) bs
          []     -> (res',r')

  todoBits  = map (testBit xs) (downIxes (xsLen - degree))


-- | Create a packed word
modExp :: Integer -- ^ bit size of the resulting word
       -> BV      -- ^ base
       -> BV      -- ^ exponent
       -> BV
modExp bits (BV _ base) (BV _ e)
  | bits == 0            = BV bits 0
  | base < 0 || bits < 0 = evalPanic "modExp"
                             [ "bad args: "
                             , "  base = " ++ show base
                             , "  e    = " ++ show e
                             , "  bits = " ++ show modulus
                             ]
  | otherwise            = mkBv bits $ doubleAndAdd base e modulus
  where
  modulus = 0 `setBit` fromInteger bits

integerExp :: Integer -> Integer -> Integer
integerExp x y
  | y < 0     = negativeExponent
  | otherwise = x ^ y

doubleAndAdd :: Integer -- ^ base
             -> Integer -- ^ exponent mask
             -> Integer -- ^ modulus
             -> Integer
doubleAndAdd base0 expMask modulus = go 1 base0 expMask
  where
  go acc base k
    | k > 0     = acc' `seq` base' `seq` go acc' base' (k `shiftR` 1)
    | otherwise = acc
    where
    acc' | k `testBit` 0 = acc `modMul` base
         | otherwise     = acc

    base' = base `modMul` base

    modMul x y = (x * y) `mod` modulus



-- Operation Lifting -----------------------------------------------------------

type Binary b w i = TValue -> GenValue b w i -> GenValue b w i -> Eval (GenValue b w i)

binary :: Binary b w i -> GenValue b w i
binary f = tlam $ \ ty ->
            lam $ \ a  -> return $
            lam $ \ b  -> do
               --io $ putStrLn "Entering a binary function"
               join (f ty <$> a <*> b)

type Unary b w i = TValue -> GenValue b w i -> Eval (GenValue b w i)

unary :: Unary b w i -> GenValue b w i
unary f = tlam $ \ ty ->
           lam $ \ a  -> f ty =<< a


-- Arith -----------------------------------------------------------------------

-- | Turn a normal binop on Integers into one that can also deal with a bitsize.
liftBinArith :: (Integer -> Integer -> Integer) -> BinArith BV
liftBinArith op w (BV _ x) (BV _ y) = mkBv w $ op x y

type BinArith w = Integer -> w -> w -> w

arithBinary :: forall b w i
             . BitWord b w i
            => BinArith w
            -> (i -> i -> i)
            -> Binary b w i
arithBinary opw opi = loop
  where
  loop' :: TValue
        -> Eval (GenValue b w i)
        -> Eval (GenValue b w i)
        -> Eval (GenValue b w i)
  loop' ty l r = join (loop ty <$> l <*> r)

  loop :: TValue
       -> GenValue b w i
       -> GenValue b w i
       -> Eval (GenValue b w i)
  loop ty l r = case ty of
    TVBit ->
      evalPanic "arithBinary" ["Bit not in class Arith"]

    TVInteger ->
      return $ VInteger $ opi (fromVInteger l) (fromVInteger r)

    TVSeq w a
      -- words and finite sequences
      | isTBit a -> do
                  lw <- fromVWord "arithLeft" l
                  rw <- fromVWord "arithRight" r
                  return $ VWord w $ ready $ WordVal $ opw w lw rw
      | otherwise -> VSeq w <$> (join (zipSeqMap (loop a) <$>
                                      (fromSeq "arithBinary left" l) <*>
                                      (fromSeq "arithBinary right" r)))

    TVStream a ->
      -- streams
      VStream <$> (join (zipSeqMap (loop a) <$>
                             (fromSeq "arithBinary left" l) <*>
                             (fromSeq "arithBinary right" r)))

    -- functions
    TVFun _ ety ->
      return $ lam $ \ x -> loop' ety (fromVFun l x) (fromVFun r x)

    -- tuples
    TVTuple tys ->
      let ls = fromVTuple l
          rs = fromVTuple r
       in return $ VTuple (zipWith3 loop' tys ls rs)

    -- records
    TVRec fs ->
      return $ VRecord [ (f, loop' fty (lookupRecord f l) (lookupRecord f r))
                       | (f,fty) <- fs ]

type UnaryArith w = Integer -> w -> w

liftUnaryArith :: (Integer -> Integer) -> UnaryArith BV
liftUnaryArith op w (BV _ x) = mkBv w $ op x

arithUnary :: forall b w i
            . BitWord b w i
           => UnaryArith w
           -> (i -> i)
           -> Unary b w i
arithUnary opw opi = loop
  where
  loop' :: TValue -> Eval (GenValue b w i) -> Eval (GenValue b w i)
  loop' ty x = loop ty =<< x

  loop :: TValue -> GenValue b w i -> Eval (GenValue b w i)
  loop ty x = case ty of

    TVBit ->
      evalPanic "arithUnary" ["Bit not in class Arith"]

    TVInteger ->
      return $ VInteger $ opi (fromVInteger x)

    TVSeq w a
      -- words and finite sequences
      | isTBit a -> do
              wx <- fromVWord "arithUnary" x
              return $ VWord w $ ready $ WordVal $ opw w wx
      | otherwise -> VSeq w <$> (mapSeqMap (loop a) =<< fromSeq "arithUnary" x)

    TVStream a ->
      VStream <$> (mapSeqMap (loop a) =<< fromSeq "arithUnary" x)

    -- functions
    TVFun _ ety ->
      return $ lam $ \ y -> loop' ety (fromVFun x y)

    -- tuples
    TVTuple tys ->
      let as = fromVTuple x
       in return $ VTuple (zipWith loop' tys as)

    -- records
    TVRec fs ->
      return $ VRecord [ (f, loop' fty (lookupRecord f x)) | (f,fty) <- fs ]

--    | otherwise = evalPanic "arithUnary" ["Invalid arguments"]


lg2 :: Integer -> Integer
lg2 i = case genLog i 2 of
  Just (i',isExact) | isExact   -> i'
                    | otherwise -> i' + 1
  Nothing                       -> 0

divWrap :: Integral a => a -> a -> a
divWrap _ 0 = divideByZero
divWrap x y = x `div` y

modWrap :: Integral a => a -> a -> a
modWrap _ 0 = divideByZero
modWrap x y = x `mod` y

-- Cmp -------------------------------------------------------------------------

-- | Lexicographic ordering on two values.
lexCompare :: String -> TValue -> Value -> Value -> Eval Ordering
lexCompare nm ty l r = case ty of

  TVBit ->
    return $ compare (fromVBit l) (fromVBit r)

  TVSeq _ TVBit ->
    compare <$> (fromWord "compareLeft" l) <*> (fromWord "compareRight" r)

  TVSeq w e ->
      join (zipLexCompare nm (repeat e) <$>
               (enumerateSeqMap w <$> fromSeq "lexCompare left" l) <*>
               (enumerateSeqMap w <$> fromSeq "lexCompare right" r))

  -- tuples
  TVTuple etys ->
    zipLexCompare nm etys (fromVTuple l) (fromVTuple r)

  -- records
  TVRec fields ->
    let tys    = map snd (sortBy (comparing fst) fields)
        ls     = map snd (sortBy (comparing fst) (fromVRecord l))
        rs     = map snd (sortBy (comparing fst) (fromVRecord r))
     in zipLexCompare nm tys ls rs

  TVInteger ->
    return $ compare (fromVInteger l) (fromVInteger r)

  _ -> evalPanic "lexCompare" ["invalid type"]


-- XXX the lists are expected to be of the same length, as this should only be
-- used with values that come from type-correct expressions.
zipLexCompare :: String -> [TValue] -> [Eval Value] -> [Eval Value] -> Eval Ordering
zipLexCompare nm tys ls rs = foldr choose (return EQ) (zipWith3 lexCompare' tys ls rs)
  where
  lexCompare' t l r = join (lexCompare nm t <$> l <*> r)

  choose c acc = c >>= \c' -> case c' of
    EQ -> acc
    _  -> return c'

-- | Process two elements based on their lexicographic ordering.
cmpOrder :: String -> (Ordering -> Bool) -> Binary Bool BV Integer
cmpOrder nm op ty l r = VBit . op <$> lexCompare nm ty l r

withOrder :: String -> (Ordering -> TValue -> Value -> Value -> Value) -> Binary Bool BV Integer
withOrder nm choose ty l r =
  do ord <- lexCompare nm ty l r
     return $ choose ord ty l r

maxV :: Ordering -> TValue -> Value -> Value -> Value
maxV o _ l r = case o of
  LT -> r
  _  -> l

minV :: Ordering -> TValue -> Value -> Value -> Value
minV o _ l r = case o of
  GT -> r
  _  -> l


funCmp :: (Ordering -> Bool) -> Value
funCmp op =
  tlam $ \ _a ->
  tlam $ \  b ->
   lam $ \  l -> return $
   lam $ \  r -> return $
   lam $ \  x -> do
      l' <- l
      r' <- r
      x' <- x
      fl <- fromVFun l' (ready x')
      fr <- fromVFun r' (ready x')
      cmpOrder "funCmp" op b fl fr


-- Logic -----------------------------------------------------------------------

zeroV :: forall b w i
       . BitWord b w i
      => TValue
      -> GenValue b w i
zeroV ty = case ty of

  -- bits
  TVBit ->
    VBit (bitLit False)

  -- integers
  TVInteger ->
    VInteger (integerLit 0)

  -- sequences
  TVSeq w ety
      | isTBit ety -> word w 0
      | otherwise  -> VSeq w (IndexSeqMap $ \_ -> ready $ zeroV ety)

  TVStream ety ->
    VStream (IndexSeqMap $ \_ -> ready $ zeroV ety)

  -- functions
  TVFun _ bty ->
    lam (\ _ -> ready (zeroV bty))

  -- tuples
  TVTuple tys ->
    VTuple (map (ready . zeroV) tys)

  -- records
  TVRec fields ->
    VRecord [ (f,ready $ zeroV fty) | (f,fty) <- fields ]

--  | otherwise = evalPanic "zeroV" ["invalid type for zero"]


joinWordVal :: BitWord b w i =>
            WordValue b w -> WordValue b w -> WordValue b w
joinWordVal (WordVal w1) (WordVal w2) = WordVal $ joinWord w1 w2
joinWordVal w1 w2 = BitsVal $ (asBitsVal w1) Seq.>< (asBitsVal w2)

joinWords :: forall b w i
           . BitWord b w i
          => Integer
          -> Integer
          -> SeqMap b w i
          -> Eval (GenValue b w i)
joinWords nParts nEach xs =
  loop (ready $ WordVal (wordLit 0 0)) (enumerateSeqMap nParts xs)

 where
 loop :: Eval (WordValue b w) -> [Eval (GenValue b w i)] -> Eval (GenValue b w i)
 loop !wv [] = return $ VWord (nParts * nEach) wv
 loop !wv (w : ws) = do
    w >>= \case
      VWord _ w' -> loop (joinWordVal <$> wv <*> w') ws
      _ -> evalPanic "joinWords: expected word value" []


joinSeq :: BitWord b w i
        => Nat'
        -> Integer
        -> TValue
        -> SeqMap b w i
        -> Eval (GenValue b w i)

-- finite sequence of words
joinSeq (Nat parts) each TVBit xs
  = joinWords parts each xs

-- infinite sequence of words
joinSeq Inf each TVBit xs
  = return $ VStream $ IndexSeqMap $ \i -> do
      let (q,r) = divMod i each
      ys <- fromWordVal "join seq" =<< lookupSeqMap xs q
      VBit <$> (asBitsVal ys `Seq.index` fromInteger r)

-- finite or infinite sequence of non-words
joinSeq parts each _a xs
  = return $ vSeq $ IndexSeqMap $ \i -> do
      let (q,r) = divMod i each
      ys <- fromSeq "join seq" =<< lookupSeqMap xs q
      lookupSeqMap ys r
  where
  len = parts `nMul` (Nat each)
  vSeq = case len of
           Inf    -> VStream
           Nat n  -> VSeq n


-- | Join a sequence of sequences into a single sequence.
joinV :: BitWord b w i
      => Nat'
      -> Integer
      -> TValue
      -> GenValue b w i
      -> Eval (GenValue b w i)
joinV parts each a val = joinSeq parts each a =<< fromSeq "joinV" val


splitWordVal :: BitWord b w i
             => Integer
             -> Integer
             -> WordValue b w
             -> (WordValue b w, WordValue b w)
splitWordVal leftWidth rightWidth (WordVal w) =
  let (lw, rw) = splitWord leftWidth rightWidth w
   in (WordVal lw, WordVal rw)
splitWordVal leftWidth _rightWidth (BitsVal bs) =
  let (lbs, rbs) = Seq.splitAt (fromInteger leftWidth) bs
   in (BitsVal lbs, BitsVal rbs)

splitAtV :: BitWord b w i
         => Nat'
         -> Nat'
         -> TValue
         -> GenValue b w i
         -> Eval (GenValue b w i)
splitAtV front back a val =
  case back of

    Nat rightWidth | aBit -> do
          ws <- delay Nothing (splitWordVal leftWidth rightWidth <$> fromWordVal "splitAtV" val)
          return $ VTuple
                   [ VWord leftWidth  . ready . fst <$> ws
                   , VWord rightWidth . ready . snd <$> ws
                   ]

    Inf | aBit -> do
       vs <- delay Nothing (fromSeq "splitAtV" val)
       ls <- delay Nothing (do m <- fst . splitSeqMap leftWidth <$> vs
                               let ms = map (fromVBit <$>) (enumerateSeqMap leftWidth m)
                               return $ Seq.fromList $ ms)
       rs <- delay Nothing (snd . splitSeqMap leftWidth <$> vs)
       return $ VTuple [ return $ VWord leftWidth (BitsVal <$> ls)
                       , VStream <$> rs
                       ]

    _ -> do
       vs <- delay Nothing (fromSeq "splitAtV" val)
       ls <- delay Nothing (fst . splitSeqMap leftWidth <$> vs)
       rs <- delay Nothing (snd . splitSeqMap leftWidth <$> vs)
       return $ VTuple [ VSeq leftWidth <$> ls
                       , mkSeq back a <$> rs
                       ]

  where
  aBit = isTBit a

  leftWidth = case front of
    Nat n -> n
    _     -> evalPanic "splitAtV" ["invalid `front` len"]


extractWordVal :: BitWord b w i
               => Integer
               -> Integer
               -> WordValue b w
               -> WordValue b w
extractWordVal len start (WordVal w) =
   WordVal $ extractWord len start w
extractWordVal len start (BitsVal bs) =
   BitsVal $ Seq.take (fromInteger len) $
     Seq.drop (Seq.length bs - fromInteger start - fromInteger len) bs


-- | Split implementation.
ecSplitV :: BitWord b w i
         => GenValue b w i
ecSplitV =
  nlam $ \ parts ->
  nlam $ \ each  ->
  tlam $ \ a     ->
  lam  $ \ val ->
    case (parts, each) of
       (Nat p, Nat e) | isTBit a -> do
          VWord _ val' <- val
          return $ VSeq p $ IndexSeqMap $ \i -> do
            return $ VWord e (extractWordVal e ((p-i-1)*e) <$> val')
       (Inf, Nat e) | isTBit a -> do
          val' <- delay Nothing (fromSeq "ecSplitV" =<< val)
          return $ VStream $ IndexSeqMap $ \i ->
            return $ VWord e $ return $ BitsVal $ Seq.fromFunction (fromInteger e) $ \j ->
              let idx = i*e + toInteger j
               in idx `seq` do
                      xs <- val'
                      fromVBit <$> lookupSeqMap xs idx
       (Nat p, Nat e) -> do
          val' <- delay Nothing (fromSeq "ecSplitV" =<< val)
          return $ VSeq p $ IndexSeqMap $ \i ->
            return $ VSeq e $ IndexSeqMap $ \j -> do
              xs <- val'
              lookupSeqMap xs (e * i + j)
       (Inf  , Nat e) -> do
          val' <- delay Nothing (fromSeq "ecSplitV" =<< val)
          return $ VStream $ IndexSeqMap $ \i ->
            return $ VSeq e $ IndexSeqMap $ \j -> do
              xs <- val'
              lookupSeqMap xs (e * i + j)
       _              -> evalPanic "splitV" ["invalid type arguments to split"]


reverseV :: forall b w i
          . BitWord b w i
         => GenValue b w i
         -> Eval (GenValue b w i)
reverseV (VSeq n xs) =
  return $ VSeq n $ reverseSeqMap n xs
reverseV (VWord n wv) = return (VWord n (revword <$> wv))
 where
 revword (WordVal w)  = BitsVal $ Seq.reverse $ Seq.fromList $ map ready $ unpackWord w
 revword (BitsVal bs) = BitsVal $ Seq.reverse bs
reverseV _ =
  evalPanic "reverseV" ["Not a finite sequence"]


transposeV :: BitWord b w i
           => Nat'
           -> Nat'
           -> TValue
           -> GenValue b w i
           -> Eval (GenValue b w i)
transposeV a b c xs
  | isTBit c, Nat na <- a =
      return $ bseq $ IndexSeqMap $ \bi ->
        return $ VWord na $ return $ BitsVal $
          Seq.fromFunction (fromInteger na) $ \ai -> do
            ys <- flip lookupSeqMap (toInteger ai) =<< fromSeq "transposeV" xs
            case ys of
              VStream ys' -> fromVBit <$> lookupSeqMap ys' bi
              VWord _ wv  -> flip bitsSeq bi =<< wv
              _ -> evalPanic "transpose" ["expected sequence of bits"]

  | otherwise = do
      return $ bseq $ IndexSeqMap $ \bi ->
        return $ aseq $ IndexSeqMap $ \ai -> do
          ys  <- flip lookupSeqMap ai =<< fromSeq "transposeV 1" xs
          z   <- flip lookupSeqMap bi =<< fromSeq "transposeV 2" ys
          return z

 where
  bseq =
        case b of
          Nat nb -> VSeq nb
          Inf    -> VStream
  aseq =
        case a of
          Nat na -> VSeq na
          Inf    -> VStream




ccatV :: (Show b, Show w, BitWord b w i)
      => Nat'
      -> Nat'
      -> TValue
      -> (GenValue b w i)
      -> (GenValue b w i)
      -> Eval (GenValue b w i)

ccatV _front _back _elty (VWord m l) (VWord n r) =
  return $ VWord (m+n) (joinWordVal <$> l <*> r)

ccatV _front _back _elty (VWord m l) (VStream r) = do
  l' <- delay Nothing l
  return $ VStream $ IndexSeqMap $ \i ->
    if i < m then
      VBit <$> (flip indexWordValue i =<< l')
    else
      lookupSeqMap r (i-m)

ccatV front back elty l r = do
       l'' <- delay Nothing (fromSeq "ccatV left" l)
       r'' <- delay Nothing (fromSeq "ccatV right" r)
       let Nat n = front
       mkSeq (evalTF TCAdd [front,back]) elty <$> return (IndexSeqMap $ \i ->
        if i < n then do
         ls <- l''
         lookupSeqMap ls i
        else do
         rs <- r''
         lookupSeqMap rs (i-n))

wordValLogicOp :: BitWord b w i
               => (b -> b -> b)
               -> (w -> w -> w)
               -> WordValue b w
               -> WordValue b w
               -> WordValue b w
wordValLogicOp _ wop (WordVal w1) (WordVal w2) = WordVal (wop w1 w2)
wordValLogicOp bop _ w1 w2 =
  BitsVal $ Seq.zipWith (\x y -> bop <$> x <*> y) (asBitsVal w1) (asBitsVal w2)

-- | Merge two values given a binop.  This is used for and, or and xor.
logicBinary :: forall b w i
             . BitWord b w i
            => (b -> b -> b)
            -> (w -> w -> w)
            -> (i -> i -> i)
            -> Binary b w i
logicBinary opb opw opi = loop
  where
  loop' :: TValue
        -> Eval (GenValue b w i)
        -> Eval (GenValue b w i)
        -> Eval (GenValue b w i)
  loop' ty l r = join (loop ty <$> l <*> r)

  loop :: TValue
        -> GenValue b w i
        -> GenValue b w i
        -> Eval (GenValue b w i)

  loop ty l r = case ty of
    TVBit -> return $ VBit (opb (fromVBit l) (fromVBit r))
    TVInteger -> return $ VInteger (opi (fromVInteger l) (fromVInteger r))
    TVSeq w aty
         -- words
         | isTBit aty
              -> return $ VWord w (wordValLogicOp opb opw <$>
                                    fromWordVal "logicBinary l" l <*>
                                    fromWordVal "logicBinary r" r)

         -- finite sequences
         | otherwise -> VSeq w <$>
                           (join (zipSeqMap (loop aty) <$>
                                    (fromSeq "logicBinary left" l)
                                    <*> (fromSeq "logicBinary right" r)))

    TVStream aty ->
        VStream <$> (join (zipSeqMap (loop aty) <$>
                          (fromSeq "logicBinary left" l) <*>
                          (fromSeq "logicBinary right" r)))

    TVTuple etys -> do
        let ls = fromVTuple l
        let rs = fromVTuple r
        return $ VTuple $ (zipWith3 loop' etys ls rs)

    TVFun _ bty ->
        return $ lam $ \ a -> loop' bty (fromVFun l a) (fromVFun r a)

    TVRec fields ->
        return $ VRecord [ (f,loop' fty a b)
                         | (f,fty) <- fields
                         , let a = lookupRecord f l
                               b = lookupRecord f r
                         ]


wordValUnaryOp :: BitWord b w i
               => (b -> b)
               -> (w -> w)
               -> WordValue b w
               -> WordValue b w
wordValUnaryOp _ wop (WordVal w)  = WordVal (wop w)
wordValUnaryOp bop _ (BitsVal bs) = BitsVal (fmap (bop <$>) bs)

logicUnary :: forall b w i
            . BitWord b w i
           => (b -> b)
           -> (w -> w)
           -> (i -> i)
           -> Unary b w i
logicUnary opb opw opi = loop
  where
  loop' :: TValue -> Eval (GenValue b w i) -> Eval (GenValue b w i)
  loop' ty val = loop ty =<< val

  loop :: TValue -> GenValue b w i -> Eval (GenValue b w i)
  loop ty val = case ty of
    TVBit -> return . VBit . opb $ fromVBit val

    TVInteger -> return . VInteger . opi $ fromVInteger val

    TVSeq w ety
         -- words
         | isTBit ety
              -> do return $ VWord w (wordValUnaryOp opb opw <$> fromWordVal "logicUnary" val)

         -- finite sequences
         | otherwise
              -> VSeq w <$> (mapSeqMap (loop ety) =<< fromSeq "logicUnary" val)

         -- streams
    TVStream ety ->
         VStream <$> (mapSeqMap (loop ety) =<< fromSeq "logicUnary" val)

    TVTuple etys ->
      let as = fromVTuple val
       in return $ VTuple (zipWith loop' etys as)

    TVFun _ bty ->
      return $ lam $ \ a -> loop' bty (fromVFun val a)

    TVRec fields ->
      return $ VRecord [ (f,loop' fty a) | (f,fty) <- fields, let a = lookupRecord f val ]


logicShift :: (Integer -> Integer -> Integer -> Integer)
              -- ^ The function may assume its arguments are masked.
              -- It is responsible for masking its result if needed.
           -> (Integer -> Seq.Seq (Eval Bool) -> Integer -> Seq.Seq (Eval Bool))
           -> (Nat' -> TValue -> SeqValMap -> Integer -> SeqValMap)
           -> Value
logicShift opW obB opS
  = nlam $ \ a ->
    nlam $ \ _ ->
    tlam $ \ c ->
     lam  $ \ l -> return $
     lam  $ \ r -> do
        BV _ i <- fromVWord "logicShift amount" =<< r
        l >>= \case
          VWord w wv -> return $ VWord w $ wv >>= \case
                          BitsVal bs -> return $ BitsVal (obB w bs i)
                          WordVal (BV _ x) -> return $ WordVal (BV w (opW w x i))

          _ -> mkSeq a c <$> (opS a c <$> (fromSeq "logicShift" =<< l) <*> return i)

-- Left shift for words.
shiftLW :: Integer -> Integer -> Integer -> Integer
shiftLW w ival by
  | by >= w   = 0
  | otherwise = mask w (shiftL ival (fromInteger by))

shiftLB :: Integer -> Seq.Seq (Eval Bool) -> Integer -> Seq.Seq (Eval Bool)
shiftLB w bs by =
  Seq.drop (fromInteger (min w by)) bs
  Seq.><
  Seq.replicate (fromInteger (min w by)) (ready False)

shiftLS :: Nat' -> TValue -> SeqValMap -> Integer -> SeqValMap
shiftLS w ety vs by = IndexSeqMap $ \i ->
  case w of
    Nat len
      | i+by < len -> lookupSeqMap vs (i+by)
      | i    < len -> return $ zeroV ety
      | otherwise  -> evalPanic "shiftLS" ["Index out of bounds"]
    Inf            -> lookupSeqMap vs (i+by)

shiftRW :: Integer -> Integer -> Integer -> Integer
shiftRW w i by
  | by >= w   = 0
  | otherwise = shiftR i (fromInteger by)

shiftRB :: Integer -> Seq.Seq (Eval Bool) -> Integer -> Seq.Seq (Eval Bool)
shiftRB w bs by =
  Seq.replicate (fromInteger (min w by)) (ready False)
  Seq.><
  Seq.take (fromInteger (w - min w by)) bs

shiftRS :: Nat' -> TValue -> SeqValMap -> Integer -> SeqValMap
shiftRS w ety vs by = IndexSeqMap $ \i ->
  case w of
    Nat len
      | i >= by   -> lookupSeqMap vs (i-by)
      | i < len   -> return $ zeroV ety
      | otherwise -> evalPanic "shiftLS" ["Index out of bounds"]
    Inf
      | i >= by   -> lookupSeqMap vs (i-by)
      | otherwise -> return $ zeroV ety


-- XXX integer doesn't implement rotateL, as there's no bit bound
rotateLW :: Integer -> Integer -> Integer -> Integer
rotateLW 0 i _  = i
rotateLW w i by = mask w $ (i `shiftL` b) .|. (i `shiftR` (fromInteger w - b))
  where b = fromInteger (by `mod` w)

rotateLB :: Integer -> Seq.Seq (Eval Bool) -> Integer -> Seq.Seq (Eval Bool)
rotateLB w bs by =
  let (hd,tl) = Seq.splitAt (fromInteger (by `mod` w)) bs
   in tl Seq.>< hd

rotateLS :: Nat' -> TValue -> SeqValMap -> Integer -> SeqValMap
rotateLS w _ vs by = IndexSeqMap $ \i ->
  case w of
    Nat len -> lookupSeqMap vs ((by + i) `mod` len)
    _ -> panic "Cryptol.Eval.Prim.rotateLS" [ "unexpected infinite sequence" ]

-- XXX integer doesn't implement rotateR, as there's no bit bound
rotateRW :: Integer -> Integer -> Integer -> Integer
rotateRW 0 i _  = i
rotateRW w i by = mask w $ (i `shiftR` b) .|. (i `shiftL` (fromInteger w - b))
  where b = fromInteger (by `mod` w)

rotateRB :: Integer -> Seq.Seq (Eval Bool) -> Integer -> Seq.Seq (Eval Bool)
rotateRB w bs by =
  let (hd,tl) = Seq.splitAt (fromInteger (w - (by `mod` w))) bs
   in tl Seq.>< hd

rotateRS :: Nat' -> TValue -> SeqValMap -> Integer -> SeqValMap
rotateRS w _ vs by = IndexSeqMap $ \i ->
  case w of
    Nat len -> lookupSeqMap vs ((len - by + i) `mod` len)
    _ -> panic "Cryptol.Eval.Prim.rotateRS" [ "unexpected infinite sequence" ]


-- Sequence Primitives ---------------------------------------------------------

-- | Indexing operations that return one element.
indexPrimOne :: BitWord b w i
             => (Maybe Integer -> TValue -> SeqMap b w i -> Seq.Seq b -> Eval (GenValue b w i))
             -> (Maybe Integer -> TValue -> SeqMap b w i -> w -> Eval (GenValue b w i))
             -> GenValue b w i
indexPrimOne bits_op word_op =
  nlam $ \ n  ->
  tlam $ \ a ->
  nlam $ \ _i ->
   lam $ \ l  -> return $
   lam $ \ r  -> do
      vs <- l >>= \case
               VWord _ w  -> w >>= \w' -> return $ IndexSeqMap (\i -> VBit <$> indexWordValue w' i)
               VSeq _ vs  -> return vs
               VStream vs -> return vs
               _ -> evalPanic "Expected sequence value" ["indexPrimOne"]
      r >>= \case
         VWord _ w -> w >>= \case
           WordVal w' -> word_op (fromNat n) a vs w'
           BitsVal bs -> bits_op (fromNat n) a vs =<< sequence bs
         _ -> evalPanic "Expected word value" ["indexPrimOne"]

indexFront :: Maybe Integer -> TValue -> SeqValMap -> BV -> Eval Value
indexFront mblen _a vs (bvVal -> ix) =
  case mblen of
    Just len | len <= ix -> invalidIndex ix
    _                    -> lookupSeqMap vs ix

indexFront_bits :: Maybe Integer -> TValue -> SeqValMap -> Seq.Seq Bool -> Eval Value
indexFront_bits mblen a vs = indexFront mblen a vs . packWord . Fold.toList

indexBack :: Maybe Integer -> TValue -> SeqValMap -> BV -> Eval Value
indexBack mblen _a vs (bvVal -> ix) =
  case mblen of
    Just len | len > ix  -> lookupSeqMap vs (len - ix - 1)
             | otherwise -> invalidIndex ix
    Nothing              -> evalPanic "indexBack"
                            ["unexpected infinite sequence"]

indexBack_bits :: Maybe Integer -> TValue -> SeqValMap -> Seq.Seq Bool -> Eval Value
indexBack_bits mblen a vs = indexBack mblen a vs . packWord . Fold.toList

-- | Indexing operations that return many elements.
indexPrimMany :: BitWord b w i
              => (Maybe Integer -> TValue -> SeqMap b w i -> Seq.Seq b -> Eval (GenValue b w i))
              -> (Maybe Integer -> TValue -> SeqMap b w i -> w -> Eval (GenValue b w i))
              -> GenValue b w i
indexPrimMany bits_op word_op =
  nlam $ \ n  ->
  tlam $ \ a  ->
  nlam $ \ m  ->
  nlam $ \ _i ->
   lam $ \ l  -> return $
   lam $ \ r  -> do
     vs <- (l >>= \case
               VWord _ w  -> w >>= \w' -> return $ IndexSeqMap (\i -> VBit <$> indexWordValue w' i)
               VSeq _ vs  -> return vs
               VStream vs -> return vs
               _ -> evalPanic "Expected sequence value" ["indexPrimMany"])
     ixs <- fromSeq "indexPrimMany idx" =<< r
     mkSeq m a <$> memoMap (IndexSeqMap $ \i -> do
       lookupSeqMap ixs i >>= \case
         VWord _ w -> w >>= \case
            WordVal w' -> word_op (fromNat n) a vs w'
            BitsVal bs -> bits_op (fromNat n) a vs =<< sequence bs
         _ -> evalPanic "Expected word value" ["indexPrimMany"])


updateFront
  :: Nat'
  -> TValue
  -> SeqMap Bool BV Integer
  -> WordValue Bool BV
  -> Eval (GenValue Bool BV Integer)
  -> Eval (SeqMap Bool BV Integer)
updateFront len _eltTy vs w val = do
  idx <- bvVal <$> asWordVal w
  case len of
    Inf -> return ()
    Nat n -> unless (idx < n) (invalidIndex idx)
  return $ updateSeqMap vs idx val

updateFront_bits
 :: Nat'
 -> TValue
 -> Seq.Seq (Eval Bool)
 -> WordValue Bool BV
 -> Eval (GenValue Bool BV Integer)
 -> Eval (Seq.Seq (Eval Bool))
updateFront_bits len _eltTy bs w val = do
  idx <- bvVal <$> asWordVal w
  case len of
    Inf -> return ()
    Nat n -> unless (idx < n) (invalidIndex idx)
  return $! Seq.update (fromInteger idx) (fromVBit <$> val) bs


updateBack
  :: Nat'
  -> TValue
  -> SeqMap Bool BV Integer
  -> WordValue Bool BV
  -> Eval (GenValue Bool BV Integer)
  -> Eval (SeqMap Bool BV Integer)
updateBack Inf _eltTy _vs _w _val =
  evalPanic "Unexpected infinite sequence in updateEnd" []
updateBack (Nat n) _eltTy vs w val = do
  idx <- bvVal <$> asWordVal w
  unless (idx < n) (invalidIndex idx)
  return $ updateSeqMap vs (n - idx - 1) val

updateBack_bits
 :: Nat'
 -> TValue
 -> Seq.Seq (Eval Bool)
 -> WordValue Bool BV
 -> Eval (GenValue Bool BV Integer)
 -> Eval (Seq.Seq (Eval Bool))
updateBack_bits Inf _eltTy _bs _w _val =
  evalPanic "Unexpected infinite sequence in updateEnd" []
updateBack_bits (Nat n) _eltTy bs w val = do
  idx <- bvVal <$> asWordVal w
  unless (idx < n) (invalidIndex idx)
  let idx' = n - idx - 1
  return $! Seq.update (fromInteger idx') (fromVBit <$> val) bs


updatePrim
     :: BitWord b w i
     => (Nat' -> TValue -> Seq.Seq (Eval b) -> WordValue b w -> Eval (GenValue b w i) -> Eval (Seq.Seq (Eval b)))
     -> (Nat' -> TValue -> SeqMap b w i -> WordValue b w -> Eval (GenValue b w i) -> Eval (SeqMap b w i))
     -> GenValue b w i
updatePrim updateBits updateWord =
  nlam $ \len ->
  tlam $ \eltTy ->
  nlam $ \_idxLen ->
  lam $ \xs  -> return $
  lam $ \idx -> return $
  lam $ \val -> do
    idx' <- fromWordVal "update" =<< idx
    xs >>= \case
      VWord l w -> do
         w' <- asBitsVal <$> w
         return $ VWord l (BitsVal <$> updateBits len eltTy w' idx' val)
      VSeq l vs -> VSeq l <$> updateWord len eltTy vs idx' val
      VStream vs -> VStream <$> updateWord len eltTy vs idx' val
      _ -> evalPanic "Expected sequence value" ["updatePrim"]



-- @[ 0, 1 .. ]@
fromThenV :: BitWord b w i
          => GenValue b w i
fromThenV  =
  nlam $ \ first ->
  nlam $ \ next  ->
  nlam $ \ bits  ->
  nlam $ \ len   ->
    case (first, next, len, bits) of
      (_         , _        , _       , Nat bits')
        | bits' >= Arch.maxBigIntWidth -> wordTooWide bits'
      (Nat first', Nat next', Nat len', Nat bits') ->
        let diff = next' - first'
         in VSeq len' $ IndexSeqMap $ \i ->
                ready $ VWord bits' $ return $
                  WordVal $ wordLit bits' (first' + i*diff)
      _ -> evalPanic "fromThenV" ["invalid arguments"]

-- @[ 0 .. 10 ]@
fromToV :: BitWord b w i
        => GenValue b w i
fromToV  =
  nlam $ \ first ->
  nlam $ \ lst   ->
  nlam $ \ bits  ->
    case (first, lst, bits) of
      (_         , _       , Nat bits')
        | bits' >= Arch.maxBigIntWidth -> wordTooWide bits'
      (Nat first', Nat lst', Nat bits') ->
        let len = 1 + (lst' - first')
         in VSeq len $ IndexSeqMap $ \i ->
               ready $ VWord bits' $ return $
                 WordVal $ wordLit bits' (first' + i)
      _ -> evalPanic "fromToV" ["invalid arguments"]

-- @[ 0, 1 .. 10 ]@
fromThenToV :: BitWord b w i
            => GenValue b w i
fromThenToV  =
  nlam $ \ first ->
  nlam $ \ next  ->
  nlam $ \ lst   ->
  nlam $ \ bits  ->
  nlam $ \ len   ->
    case (first, next, lst, len, bits) of
      (_         , _        , _       , _       , Nat bits')
        | bits' >= Arch.maxBigIntWidth -> wordTooWide bits'
      (Nat first', Nat next', Nat _lst', Nat len', Nat bits') ->
        let diff = next' - first'
         in VSeq len' $ IndexSeqMap $ \i ->
               ready $ VWord bits' $ return $
                 WordVal $ wordLit bits' (first' + i*diff)
      _ -> evalPanic "fromThenToV" ["invalid arguments"]


infFromV :: BitWord b w i
         => GenValue b w i
infFromV =
     nlam $ \(finNat' -> bits)  ->
     wlam $ \first ->
     return $ VStream $ IndexSeqMap $ \i ->
       ready $ VWord bits $ return $
         WordVal $ wordPlus first (wordLit bits i)

infFromThenV :: BitWord b w i
             => GenValue b w i
infFromThenV =
     nlam $ \(finNat' -> bits)  ->
     wlam $ \first -> return $
     wlam $ \next  -> do
       let diff = wordMinus next first
       return $ VStream $ IndexSeqMap $ \i ->
         ready $ VWord bits $ return $
           WordVal $ wordPlus first (wordMult diff (wordLit bits i))

-- Random Values ---------------------------------------------------------------

-- | Produce a random value with the given seed. If we do not support
-- making values of the given type, return zero of that type.
-- TODO: do better than returning zero
randomV :: TValue -> Integer -> Value
randomV ty seed =
  case randomValue (tValTy ty) of
    Nothing -> zeroV ty
    Just gen ->
      -- unpack the seed into four Word64s
      let mask64 = 0xFFFFFFFFFFFFFFFF
          unpack s = fromIntegral (s .&. mask64) : unpack (s `shiftR` 64)
          [a, b, c, d] = take 4 (unpack seed)
      in fst $ gen 100 $ seedTFGen (a, b, c, d)

-- Miscellaneous ---------------------------------------------------------------

errorV :: forall b w i
       . BitWord b w i
      => TValue
      -> String
      -> Eval (GenValue b w i)
errorV ty msg = case ty of
  -- bits
  TVBit -> cryUserError msg
  TVInteger -> cryUserError msg

  -- sequences
  TVSeq w ety
     | isTBit ety -> return $ VWord w $ return $ BitsVal $
                         Seq.replicate (fromInteger w) (cryUserError msg)
     | otherwise  -> return $ VSeq w (IndexSeqMap $ \_ -> errorV ety msg)

  TVStream ety ->
    return $ VStream (IndexSeqMap $ \_ -> errorV ety msg)

  -- functions
  TVFun _ bty ->
    return $ lam (\ _ -> errorV bty msg)

  -- tuples
  TVTuple tys ->
    return $ VTuple (map (flip errorV msg) tys)

  -- records
  TVRec fields ->
    return $ VRecord [ (f,errorV fty msg) | (f,fty) <- fields ]
