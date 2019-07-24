-- |
-- Module      :  Cryptol.Prims.Eval
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
{-# LANGUAGE NamedFieldPuns #-}
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
import Cryptol.Eval.Monad
import Cryptol.Eval.Type
import Cryptol.Eval.Value
import Cryptol.Testing.Random (randomValue)
import Cryptol.Utils.Panic (panic)
import Cryptol.ModuleSystem.Name (asPrim)
import Cryptol.Utils.Ident (Ident,mkIdent)
import Cryptol.Utils.PP
import Cryptol.Utils.Logger(logPrint)

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
  evalPrim Decl { dName = n, .. } =
    do prim <- asPrim n
       Map.lookup prim primTable

  iteValue b t f = if b then t else f


primTable :: Map.Map Ident Value
primTable = Map.fromList $ map (\(n, v) -> (mkIdent (T.pack n), v))
  [ ("+"          , {-# SCC "Prelude::(+)" #-}
                    binary (arithBinary (liftBinArith (+)) (liftBinInteger (+))
                            (liftBinIntMod (+))))
  , ("-"          , {-# SCC "Prelude::(-)" #-}
                    binary (arithBinary (liftBinArith (-)) (liftBinInteger (-))
                            (liftBinIntMod (-))))
  , ("*"          , {-# SCC "Prelude::(*)" #-}
                    binary (arithBinary (liftBinArith (*)) (liftBinInteger (*))
                            (liftBinIntMod (*))))
  , ("/"          , {-# SCC "Prelude::(/)" #-}
                    binary (arithBinary (liftDivArith div) (liftDivInteger div)
                            (const (liftDivInteger div))))
  , ("%"          , {-# SCC "Prelude::(%)" #-}
                    binary (arithBinary (liftDivArith mod) (liftDivInteger mod)
                            (const (liftDivInteger mod))))
  , ("^^"         , {-# SCC "Prelude::(^^)" #-}
                    binary (arithBinary modExp integerExp intModExp))
  , ("lg2"        , {-# SCC "Prelude::lg2" #-}
                    unary  (arithUnary (liftUnaryArith lg2) integerLg2 (const integerLg2)))
  , ("negate"     , {-# SCC "Prelude::negate" #-}
                    unary  (arithUnary (liftUnaryArith negate) integerNeg intModNeg))
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
  , ("<$"         , {-# SCC "Prelude::(<$)" #-}
                    binary (signedCmpOrder "<$" (\o -> o == LT)))
  , ("/$"         , {-# SCC "Prelude::(/$)" #-}
                    binary (arithBinary (liftSigned bvSdiv) (liftDivInteger div)
                            (const (liftDivInteger div))))
  , ("%$"         , {-# SCC "Prelude::(%$)" #-}
                    binary (arithBinary (liftSigned bvSrem) (liftDivInteger mod)
                            (const (liftDivInteger mod))))
  , (">>$"        , {-# SCC "Prelude::(>>$)" #-}
                    sshrV)
  , ("&&"         , {-# SCC "Prelude::(&&)" #-}
                    binary (logicBinary (.&.) (binBV (.&.))))
  , ("||"         , {-# SCC "Prelude::(||)" #-}
                    binary (logicBinary (.|.) (binBV (.|.))))
  , ("^"          , {-# SCC "Prelude::(^)" #-}
                    binary (logicBinary xor (binBV xor)))
  , ("complement" , {-# SCC "Prelude::complement" #-}
                    unary  (logicUnary complement (unaryBV complement)))
  , ("toInteger"  , ecToIntegerV)
  , ("fromInteger", ecFromIntegerV (flip mod))
  , ("fromZ"      , {-# SCC "Prelude::fromZ" #-}
                    nlam $ \ _modulus ->
                    lam  $ \ x -> x)
  , ("<<"         , {-# SCC "Prelude::(<<)" #-}
                    logicShift shiftLW shiftLB shiftLS)
  , (">>"         , {-# SCC "Prelude::(>>)" #-}
                    logicShift shiftRW shiftRB shiftRS)
  , ("<<<"        , {-# SCC "Prelude::(<<<)" #-}
                    logicShift rotateLW rotateLB rotateLS)
  , (">>>"        , {-# SCC "Prelude::(>>>)" #-}
                    logicShift rotateRW rotateRB rotateRS)
  , ("True"       , VBit True)
  , ("False"      , VBit False)

  , ("carry"      , {-# SCC "Prelude::carry" #-}
                    carryV)
  , ("scarry"     , {-# SCC "Prelude::scarry" #-}
                    scarryV)
  , ("number"     , {-# SCC "Prelude::number" #-}
                    ecNumberV)

  , ("#"          , {-# SCC "Prelude::(#)" #-}
                    nlam $ \ front ->
                    nlam $ \ back  ->
                    tlam $ \ elty  ->
                    lam  $ \ l     -> return $
                    lam  $ \ r     -> join (ccatV front back elty <$> l <*> r))

  , ("@"          , {-# SCC "Prelude::(@)" #-}
                    indexPrim indexFront_bits indexFront)
  , ("!"          , {-# SCC "Prelude::(!)" #-}
                    indexPrim indexBack_bits indexBack)

  , ("update"     , {-# SCC "Prelude::update" #-}
                    updatePrim updateFront_word updateFront)

  , ("updateEnd"  , {-# SCC "Prelude::updateEnd" #-}
                    updatePrim updateBack_word updateBack)

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
                         EvalOpts { evalPPOpts, evalLogger } <- getEvalOpts
                         doc <- ppValue evalPPOpts =<< x
                         yv <- y
                         io $ logPrint evalLogger
                             $ if null msg then doc else text msg <+> doc
                         return yv)
  ]

-- | Make a numeric literal value at the given type.
mkLit :: BitWord b w i => TValue -> Integer -> GenValue b w i
mkLit ty =
  case ty of
    TVInteger                    -> VInteger . integerLit
    TVIntMod _                   -> VInteger . integerLit
    TVSeq w TVBit                -> word w
    _                            -> evalPanic "Cryptol.Eval.Prim.evalConst"
                                    [ "Invalid type for number" ]

-- | Make a numeric constant.
ecNumberV :: BitWord b w i => GenValue b w i
ecNumberV = nlam $ \valT ->
            tlam $ \ty ->
            case valT of
              Nat v -> mkLit ty v
              _ -> evalPanic "Cryptol.Eval.Prim.evalConst"
                       ["Unexpected Inf in constant."
                       , show valT
                       , show ty
                       ]

-- | Convert a word to a non-negative integer.
ecToIntegerV :: BitWord b w i => GenValue b w i
ecToIntegerV =
  nlam $ \ _ ->
  wlam $ \ w -> return $ VInteger (wordToInt w)

-- | Convert an unbounded integer to a packed bitvector.
ecFromIntegerV :: BitWord b w i => (Integer -> i -> i) -> GenValue b w i
ecFromIntegerV opz =
  tlam $ \ a ->
  lam  $ \ x ->
  do i <- fromVInteger <$> x
     return $ arithNullary (flip wordFromInt i) i (flip opz i) a


--------------------------------------------------------------------------------

-- | Create a packed word
modExp :: Integer -- ^ bit size of the resulting word
       -> BV      -- ^ base
       -> BV      -- ^ exponent
       -> Eval BV
modExp bits (BV _ base) (BV _ e)
  | bits == 0            = ready $ BV bits 0
  | base < 0 || bits < 0 = evalPanic "modExp"
                             [ "bad args: "
                             , "  base = " ++ show base
                             , "  e    = " ++ show e
                             , "  bits = " ++ show modulus
                             ]
  | otherwise            = ready $ mkBv bits $ doubleAndAdd base e modulus
  where
  modulus = 0 `setBit` fromInteger bits

intModExp :: Integer -> Integer -> Integer -> Eval Integer
intModExp modulus base e
  | modulus > 0  = ready $ doubleAndAdd base e modulus
  | modulus == 0 = integerExp base e
  | otherwise    = evalPanic "intModExp" [ "negative modulus: " ++ show modulus ]

integerExp :: Integer -> Integer -> Eval Integer
integerExp x y
  | y < 0     = negativeExponent
  | otherwise = ready $ x ^ y

integerLg2 :: Integer -> Eval Integer
integerLg2 x
  | x < 0     = logNegative
  | otherwise = ready $ lg2 x

integerNeg :: Integer -> Eval Integer
integerNeg x = ready $ negate x

intModNeg :: Integer -> Integer -> Eval Integer
intModNeg modulus x = ready $ negate x `mod` modulus

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
--   However, if the bitvector size is 0, always return the 0
--   bitvector.
liftBinArith :: (Integer -> Integer -> Integer) -> BinArith BV
liftBinArith _  0 _        _        = ready $ mkBv 0 0
liftBinArith op w (BV _ x) (BV _ y) = ready $ mkBv w $ op x y

-- | Turn a normal binop on Integers into one that can also deal with a bitsize.
--   Generate a thunk that throws a divide by 0 error when forced if the second
--   argument is 0.  However, if the bitvector size is 0, always return the 0
--   bitvector.
liftDivArith :: (Integer -> Integer -> Integer) -> BinArith BV
liftDivArith _  0 _        _        = ready $ mkBv 0 0
liftDivArith _  _ _        (BV _ 0) = divideByZero
liftDivArith op w (BV _ x) (BV _ y) = ready $ mkBv w $ op x y

type BinArith w = Integer -> w -> w -> Eval w

liftBinInteger :: (Integer -> Integer -> Integer) -> Integer -> Integer -> Eval Integer
liftBinInteger op x y = ready $ op x y

liftBinIntMod ::
  (Integer -> Integer -> Integer) -> Integer -> Integer -> Integer -> Eval Integer
liftBinIntMod op m x y
  | m == 0    = ready $ op x y
  | otherwise = ready $ (op x y) `mod` m

liftDivInteger :: (Integer -> Integer -> Integer) -> Integer -> Integer -> Eval Integer
liftDivInteger _  _ 0 = divideByZero
liftDivInteger op x y = ready $ op x y

modWrap :: Integral a => a -> a -> Eval a
modWrap _ 0 = divideByZero
modWrap x y = return (x `mod` y)

arithBinary :: forall b w i
             . BitWord b w i
            => BinArith w
            -> (i -> i -> Eval i)
            -> (Integer -> i -> i -> Eval i)
            -> Binary b w i
arithBinary opw opi opz = loop
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
      VInteger <$> opi (fromVInteger l) (fromVInteger r)

    TVIntMod n ->
      VInteger <$> opz n (fromVInteger l) (fromVInteger r)

    TVSeq w a
      -- words and finite sequences
      | isTBit a -> do
                  lw <- fromVWord "arithLeft" l
                  rw <- fromVWord "arithRight" r
                  return $ VWord w (WordVal <$> opw w lw rw)
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
      do ls <- mapM (delay Nothing) (fromVTuple l)
         rs <- mapM (delay Nothing) (fromVTuple r)
         return $ VTuple (zipWith3 loop' tys ls rs)

    -- records
    TVRec fs ->
      do fs' <- sequence
                 [ (f,) <$> delay Nothing (loop' fty (lookupRecord f l) (lookupRecord f r))
                 | (f,fty) <- fs
                 ]
         return $ VRecord fs'

    TVAbstract {} ->
      evalPanic "arithBinary" ["Abstract type not in `Arith`"]

type UnaryArith w = Integer -> w -> Eval w

liftUnaryArith :: (Integer -> Integer) -> UnaryArith BV
liftUnaryArith op w (BV _ x) = ready $ mkBv w $ op x

arithUnary :: forall b w i
            . BitWord b w i
           => UnaryArith w
           -> (i -> Eval i)
           -> (Integer -> i -> Eval i)
           -> Unary b w i
arithUnary opw opi opz = loop
  where
  loop' :: TValue -> Eval (GenValue b w i) -> Eval (GenValue b w i)
  loop' ty x = loop ty =<< x

  loop :: TValue -> GenValue b w i -> Eval (GenValue b w i)
  loop ty x = case ty of

    TVBit ->
      evalPanic "arithUnary" ["Bit not in class Arith"]

    TVInteger ->
      VInteger <$> opi (fromVInteger x)

    TVIntMod n ->
      VInteger <$> opz n (fromVInteger x)

    TVSeq w a
      -- words and finite sequences
      | isTBit a -> do
              wx <- fromVWord "arithUnary" x
              return $ VWord w (WordVal <$> opw w wx)
      | otherwise -> VSeq w <$> (mapSeqMap (loop a) =<< fromSeq "arithUnary" x)

    TVStream a ->
      VStream <$> (mapSeqMap (loop a) =<< fromSeq "arithUnary" x)

    -- functions
    TVFun _ ety ->
      return $ lam $ \ y -> loop' ety (fromVFun x y)

    -- tuples
    TVTuple tys ->
      do as <- mapM (delay Nothing) (fromVTuple x)
         return $ VTuple (zipWith loop' tys as)

    -- records
    TVRec fs ->
      do fs' <- sequence
                 [ (f,) <$> delay Nothing (loop' fty (lookupRecord f x))
                 | (f,fty) <- fs
                 ]
         return $ VRecord fs'

    TVAbstract {} -> evalPanic "arithUnary" ["Abstract type not in `Arith`"]

arithNullary ::
  forall b w i.
  BitWord b w i =>
  (Integer -> w) ->
  i ->
  (Integer -> i) ->
  TValue -> GenValue b w i
arithNullary opw opi opz = loop
  where
    loop :: TValue -> GenValue b w i
    loop ty =
      case ty of
        TVBit -> evalPanic "arithNullary" ["Bit not in class Arith"]

        TVInteger -> VInteger opi

        TVIntMod n -> VInteger (opz n)

        TVSeq w a
          -- words and finite sequences
          | isTBit a -> VWord w $ ready $ WordVal $ opw w
          | otherwise -> VSeq w $ IndexSeqMap $ const $ ready $ loop a

        TVStream a -> VStream $ IndexSeqMap $ const $ ready $ loop a

        TVFun _ b -> lam $ const $ ready $ loop b

        TVTuple tys -> VTuple $ map (ready . loop) tys

        TVRec fs -> VRecord [ (f, ready (loop a)) | (f, a) <- fs ]

        TVAbstract {} ->
          evalPanic "arithNullary" ["Abstract type not in `Arith`"]

lg2 :: Integer -> Integer
lg2 i = case genLog i 2 of
  Just (i',isExact) | isExact   -> i'
                    | otherwise -> i' + 1
  Nothing                       -> 0

addV :: BitWord b w i => Binary b w i
addV = arithBinary opw opi opz
  where
    opw _w x y = ready $ wordPlus x y
    opi x y = ready $ intPlus x y
    opz m x y = ready $ intModPlus m x y

subV :: BitWord b w i => Binary b w i
subV = arithBinary opw opi opz
  where
    opw _w x y = ready $ wordMinus x y
    opi x y = ready $ intMinus x y
    opz m x y = ready $ intModMinus m x y

mulV :: BitWord b w i => Binary b w i
mulV = arithBinary opw opi opz
  where
    opw _w x y = ready $ wordMult x y
    opi x y = ready $ intMult x y
    opz m x y = ready $ intModMult m x y

intV :: BitWord b w i => i -> TValue -> GenValue b w i
intV i = arithNullary (flip wordFromInt i) i (const i)

-- Cmp -------------------------------------------------------------------------

cmpValue :: BitWord b w i
         => (b -> b -> Eval a -> Eval a)
         -> (w -> w -> Eval a -> Eval a)
         -> (i -> i -> Eval a -> Eval a)
         -> (Integer -> i -> i -> Eval a -> Eval a)
         -> (TValue -> GenValue b w i -> GenValue b w i -> Eval a -> Eval a)
cmpValue fb fw fi fz = cmp
  where
    cmp ty v1 v2 k =
      case ty of
        TVBit         -> fb (fromVBit v1) (fromVBit v2) k
        TVInteger     -> fi (fromVInteger v1) (fromVInteger v2) k
        TVIntMod n    -> fz n (fromVInteger v1) (fromVInteger v2) k
        TVSeq n t
          | isTBit t  -> do w1 <- fromVWord "cmpValue" v1
                            w2 <- fromVWord "cmpValue" v2
                            fw w1 w2 k
          | otherwise -> cmpValues (repeat t)
                         (enumerateSeqMap n (fromVSeq v1))
                         (enumerateSeqMap n (fromVSeq v2)) k
        TVStream _    -> panic "Cryptol.Prims.Value.cmpValue"
                         [ "Infinite streams are not comparable" ]
        TVFun _ _     -> panic "Cryptol.Prims.Value.cmpValue"
                         [ "Functions are not comparable" ]
        TVTuple tys   -> cmpValues tys (fromVTuple v1) (fromVTuple v2) k
        TVRec fields  -> do let vals = map snd . sortBy (comparing fst)
                            let tys = vals fields
                            cmpValues tys
                              (vals (fromVRecord v1))
                              (vals (fromVRecord v2)) k
        TVAbstract {} -> evalPanic "cmpValue"
                          [ "Abstract type not in `Cmp`" ]

    cmpValues (t : ts) (x1 : xs1) (x2 : xs2) k =
      do x1' <- x1
         x2' <- x2
         cmp t x1' x2' (cmpValues ts xs1 xs2 k)
    cmpValues _ _ _ k = k


lexCompare :: TValue -> Value -> Value -> Eval Ordering
lexCompare ty a b = cmpValue op opw op (const op) ty a b (return EQ)
 where
   opw :: BV -> BV -> Eval Ordering -> Eval Ordering
   opw x y k = op (bvVal x) (bvVal y) k

   op :: Ord a => a -> a -> Eval Ordering -> Eval Ordering
   op x y k = case compare x y of
                     EQ  -> k
                     cmp -> return cmp

signedLexCompare :: TValue -> Value -> Value -> Eval Ordering
signedLexCompare ty a b = cmpValue opb opw opi (const opi) ty a b (return EQ)
 where
   opb :: Bool -> Bool -> Eval Ordering -> Eval Ordering
   opb _x _y _k = panic "signedLexCompare"
                    ["Attempted to perform signed comparisons on bare Bit type"]

   opw :: BV -> BV -> Eval Ordering -> Eval Ordering
   opw x y k = case compare (signedBV x) (signedBV y) of
                     EQ  -> k
                     cmp -> return cmp

   opi :: Integer -> Integer -> Eval Ordering -> Eval Ordering
   opi _x _y _k = panic "signedLexCompare"
                    ["Attempted to perform signed comparisons on Integer type"]

-- | Process two elements based on their lexicographic ordering.
cmpOrder :: String -> (Ordering -> Bool) -> Binary Bool BV Integer
cmpOrder _nm op ty l r = VBit . op <$> lexCompare ty l r

-- | Process two elements based on their lexicographic ordering, using signed comparisons
signedCmpOrder :: String -> (Ordering -> Bool) -> Binary Bool BV Integer
signedCmpOrder _nm op ty l r = VBit . op <$> signedLexCompare ty l r


-- Signed arithmetic -----------------------------------------------------------

-- | Lifted operation on finite bitsequences.  Used
--   for signed comparisons and arithemtic.
liftWord :: BitWord b w i
         => (w -> w -> Eval (GenValue b w i))
         -> GenValue b w i
liftWord op =
  nlam $ \_n ->
  wlam $ \w1 -> return $
  wlam $ \w2 -> op w1 w2


liftSigned :: (Integer -> Integer -> Integer -> Eval BV)
           -> BinArith BV
liftSigned _  0    = \_ _ -> return $ mkBv 0 0
liftSigned op size = f
 where
 f (BV i x) (BV j y)
   | i == j && size == i = op size sx sy
   | otherwise = evalPanic "liftSigned" ["Attempt to compute with words of different sizes"]
   where sx = signedValue i x
         sy = signedValue j y

signedBV :: BV -> Integer
signedBV (BV i x) = signedValue i x

signedValue :: Integer -> Integer -> Integer
signedValue i x = if testBit x (fromInteger (i-1)) then x - (1 `shiftL` (fromInteger i)) else x

bvSlt :: Integer -> Integer -> Integer -> Eval Value
bvSlt _sz x y = return . VBit $! (x < y)

bvSdiv :: Integer -> Integer -> Integer -> Eval BV
bvSdiv  _ _ 0 = divideByZero
bvSdiv sz x y = return $! mkBv sz (x `quot` y)

bvSrem :: Integer -> Integer -> Integer -> Eval BV
bvSrem  _ _ 0 = divideByZero
bvSrem sz x y = return $! mkBv sz (x `rem` y)

sshrV :: Value
sshrV =
  nlam $ \_n ->
  nlam $ \_k ->
  wlam $ \(BV i x) -> return $
  wlam $ \y ->
   let signx = testBit x (fromInteger (i-1))
       amt   = fromInteger (bvVal y)
       negv  = (((-1) `shiftL` amt) .|. x) `shiftR` amt
       posv  = x `shiftR` amt
    in return . VWord i . ready . WordVal . mkBv i $! if signx then negv else posv

-- | Signed carry bit.
scarryV :: Value
scarryV =
  nlam $ \_n ->
  wlam $ \(BV i x) -> return $
  wlam $ \(BV j y) ->
    if i == j
      then let z     = x + y
               xsign = testBit x (fromInteger i - 1)
               ysign = testBit y (fromInteger i - 1)
               zsign = testBit z (fromInteger i - 1)
               sc    = (xsign == ysign) && (xsign /= zsign)
            in return $ VBit sc
      else evalPanic "scarryV" ["Attempted to compute with words of different sizes"]

-- | Unsigned carry bit.
carryV :: Value
carryV =
  nlam $ \_n ->
  wlam $ \(BV i x) -> return $
  wlam $ \(BV j y) ->
    if i == j
      then return . VBit $! testBit (x + y) (fromInteger i)
      else evalPanic "carryV" ["Attempted to compute with words of different sizes"]

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

  -- integers mod n
  TVIntMod _ ->
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

  TVAbstract {} -> evalPanic "zeroV" [ "Abstract type not in `Zero`" ]

--  | otherwise = evalPanic "zeroV" ["invalid type for zero"]


joinWordVal :: BitWord b w i =>
            WordValue b w i -> WordValue b w i -> WordValue b w i
joinWordVal (WordVal w1) (WordVal w2)
  | wordLen w1 + wordLen w2 < largeBitSize
  = WordVal $ joinWord w1 w2
joinWordVal (BitsVal xs) (WordVal w2)
  | toInteger (Seq.length xs) + wordLen w2 < largeBitSize
  = BitsVal (xs Seq.>< Seq.fromList (map ready $ unpackWord w2))
joinWordVal (WordVal w1) (BitsVal ys)
  | wordLen w1 + toInteger (Seq.length ys) < largeBitSize
  = BitsVal (Seq.fromList (map ready $ unpackWord w1) Seq.>< ys)
joinWordVal (BitsVal xs) (BitsVal ys)
  | toInteger (Seq.length xs) + toInteger (Seq.length ys) < largeBitSize
  = BitsVal (xs Seq.>< ys)
joinWordVal w1 w2
  = LargeBitsVal (n1+n2) (concatSeqMap n1 (asBitsMap w1) (asBitsMap w2))
 where n1 = wordValueSize w1
       n2 = wordValueSize w2


joinWords :: forall b w i
           . BitWord b w i
          => Integer
          -> Integer
          -> SeqMap b w i
          -> Eval (GenValue b w i)
joinWords nParts nEach xs =
  loop (ready $ WordVal (wordLit 0 0)) (enumerateSeqMap nParts xs)

 where
 loop :: Eval (WordValue b w i) -> [Eval (GenValue b w i)] -> Eval (GenValue b w i)
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

-- Special case for 0 length inner sequences.
joinSeq _parts 0 a _xs
  = return $ zeroV (TVSeq 0 a)

-- finite sequence of words
joinSeq (Nat parts) each TVBit xs
  | parts * each < largeBitSize
  = joinWords parts each xs
  | otherwise
  = do let zs = IndexSeqMap $ \i ->
                  do let (q,r) = divMod i each
                     ys <- fromWordVal "join seq" =<< lookupSeqMap xs q
                     VBit <$> indexWordValue ys (fromInteger r)
       return $ VWord (parts * each) $ ready $ LargeBitsVal (parts * each) zs

-- infinite sequence of words
joinSeq Inf each TVBit xs
  = return $ VStream $ IndexSeqMap $ \i ->
      do let (q,r) = divMod i each
         ys <- fromWordVal "join seq" =<< lookupSeqMap xs q
         VBit <$> indexWordValue ys (fromInteger r)

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
             -> WordValue b w i
             -> (WordValue b w i, WordValue b w i)
splitWordVal leftWidth rightWidth (WordVal w) =
  let (lw, rw) = splitWord leftWidth rightWidth w
   in (WordVal lw, WordVal rw)
splitWordVal leftWidth _rightWidth (BitsVal bs) =
  let (lbs, rbs) = Seq.splitAt (fromInteger leftWidth) bs
   in (BitsVal lbs, BitsVal rbs)
splitWordVal leftWidth rightWidth (LargeBitsVal _n xs) =
  let (lxs, rxs) = splitSeqMap leftWidth xs
   in (LargeBitsVal leftWidth lxs, LargeBitsVal rightWidth rxs)

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


  -- | Extract a subsequence of bits from a @WordValue@.
  --   The first integer argument is the number of bits in the
  --   resulting word.  The second integer argument is the
  --   number of less-significant digits to discard.  Stated another
  --   way, the operation `extractWordVal n i w` is equivalent to
  --   first shifting `w` right by `i` bits, and then truncating to
  --   `n` bits.
extractWordVal :: BitWord b w i
               => Integer
               -> Integer
               -> WordValue b w i
               -> WordValue b w i
extractWordVal len start (WordVal w) =
   WordVal $ extractWord len start w
extractWordVal len start (BitsVal bs) =
   BitsVal $ Seq.take (fromInteger len) $
     Seq.drop (Seq.length bs - fromInteger start - fromInteger len) bs
extractWordVal len start (LargeBitsVal n xs) =
   let xs' = dropSeqMap (n - start - len) xs
    in LargeBitsVal len xs'


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
          ~(VWord _ val') <- val
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
 revword (WordVal w)         = BitsVal $ Seq.reverse $ Seq.fromList $ map ready $ unpackWord w
 revword (BitsVal bs)        = BitsVal $ Seq.reverse bs
 revword (LargeBitsVal m xs) = LargeBitsVal m $ reverseSeqMap m xs
reverseV _ =
  evalPanic "reverseV" ["Not a finite sequence"]


transposeV :: BitWord b w i
           => Nat'
           -> Nat'
           -> TValue
           -> GenValue b w i
           -> Eval (GenValue b w i)
transposeV a b c xs
  | isTBit c, Nat na <- a = -- Fin a => [a][b]Bit -> [b][a]Bit
      return $ bseq $ IndexSeqMap $ \bi ->
        return $ VWord na $ return $ BitsVal $
          Seq.fromFunction (fromInteger na) $ \ai -> do
            ys <- flip lookupSeqMap (toInteger ai) =<< fromSeq "transposeV" xs
            case ys of
              VStream ys' -> fromVBit <$> lookupSeqMap ys' bi
              VWord _ wv  -> flip indexWordValue bi =<< wv
              _ -> evalPanic "transpose" ["expected sequence of bits"]

  | isTBit c, Inf <- a = -- [inf][b]Bit -> [b][inf]Bit
      return $ bseq $ IndexSeqMap $ \bi ->
        return $ VStream $ IndexSeqMap $ \ai ->
         do ys <- flip lookupSeqMap ai =<< fromSeq "transposeV" xs
            case ys of
              VStream ys' -> VBit . fromVBit <$> lookupSeqMap ys' bi
              VWord _ wv  -> VBit <$> (flip indexWordValue bi =<< wv)
              _ -> evalPanic "transpose" ["expected sequence of bits"]

  | otherwise = -- [a][b]c -> [b][a]c
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
               -> WordValue b w i
               -> WordValue b w i
               -> Eval (WordValue b w i)
wordValLogicOp _ wop (WordVal w1) (WordVal w2) = return $ WordVal (wop w1 w2)
wordValLogicOp bop _ (BitsVal xs) (BitsVal ys) =
  BitsVal <$> sequence (Seq.zipWith (\x y -> delay Nothing (bop <$> x <*> y)) xs ys)
wordValLogicOp bop _ (WordVal w1) (BitsVal ys) =
  ready $ BitsVal $ Seq.zipWith (\x y -> bop <$> x <*> y) (Seq.fromList $ map ready $ unpackWord w1) ys
wordValLogicOp bop _ (BitsVal xs) (WordVal w2) =
  ready $ BitsVal $ Seq.zipWith (\x y -> bop <$> x <*> y) xs (Seq.fromList $ map ready $ unpackWord w2)
wordValLogicOp bop _ w1 w2 = LargeBitsVal (wordValueSize w1) <$> zs
     where zs = memoMap $ IndexSeqMap $ \i -> op <$> (lookupSeqMap xs i) <*> (lookupSeqMap ys i)
           xs = asBitsMap w1
           ys = asBitsMap w2
           op x y = VBit (bop (fromVBit x) (fromVBit y))

-- | Merge two values given a binop.  This is used for and, or and xor.
logicBinary :: forall b w i
             . BitWord b w i
            => (b -> b -> b)
            -> (w -> w -> w)
            -> Binary b w i
logicBinary opb opw = loop
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
    TVInteger -> evalPanic "logicBinary" ["Integer not in class Logic"]
    TVIntMod _ -> evalPanic "logicBinary" ["Z not in class Logic"]
    TVSeq w aty
         -- words
         | isTBit aty
              -> do v <- delay Nothing $ join
                            (wordValLogicOp opb opw <$>
                                    fromWordVal "logicBinary l" l <*>
                                    fromWordVal "logicBinary r" r)
                    return $ VWord w v

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
        ls <- mapM (delay Nothing) (fromVTuple l)
        rs <- mapM (delay Nothing) (fromVTuple r)
        return $ VTuple $ zipWith3 loop' etys ls rs

    TVFun _ bty ->
        return $ lam $ \ a -> loop' bty (fromVFun l a) (fromVFun r a)

    TVRec fields ->
        do fs <- sequence
                   [ (f,) <$> delay Nothing (loop' fty a b)
                   | (f,fty) <- fields
                   , let a = lookupRecord f l
                         b = lookupRecord f r
                   ]
           return $ VRecord fs

    TVAbstract {} -> evalPanic "logicBinary"
                        [ "Abstract type not in `Logic`" ]


wordValUnaryOp :: BitWord b w i
               => (b -> b)
               -> (w -> w)
               -> WordValue b w i
               -> Eval (WordValue b w i)
wordValUnaryOp _ wop (WordVal w)  = return $ WordVal (wop w)
wordValUnaryOp bop _ (BitsVal bs) = return $ BitsVal (fmap (bop <$>) bs)
wordValUnaryOp bop _ (LargeBitsVal n xs) = LargeBitsVal n <$> mapSeqMap f xs
  where f x = VBit . bop <$> fromBit x

logicUnary :: forall b w i
            . BitWord b w i
           => (b -> b)
           -> (w -> w)
           -> Unary b w i
logicUnary opb opw = loop
  where
  loop' :: TValue -> Eval (GenValue b w i) -> Eval (GenValue b w i)
  loop' ty val = loop ty =<< val

  loop :: TValue -> GenValue b w i -> Eval (GenValue b w i)
  loop ty val = case ty of
    TVBit -> return . VBit . opb $ fromVBit val

    TVInteger -> evalPanic "logicUnary" ["Integer not in class Logic"]
    TVIntMod _ -> evalPanic "logicUnary" ["Z not in class Logic"]

    TVSeq w ety
         -- words
         | isTBit ety
              -> do v <- delay Nothing (wordValUnaryOp opb opw =<< fromWordVal "logicUnary" val)
                    return $ VWord w v

         -- finite sequences
         | otherwise
              -> VSeq w <$> (mapSeqMap (loop ety) =<< fromSeq "logicUnary" val)

         -- streams
    TVStream ety ->
         VStream <$> (mapSeqMap (loop ety) =<< fromSeq "logicUnary" val)

    TVTuple etys ->
      do as <- mapM (delay Nothing) (fromVTuple val)
         return $ VTuple (zipWith loop' etys as)

    TVFun _ bty ->
      return $ lam $ \ a -> loop' bty (fromVFun val a)

    TVRec fields ->
      do fs <- sequence
                 [ (f,) <$> delay Nothing (loop' fty a)
                 | (f,fty) <- fields, let a = lookupRecord f val
                 ]
         return $ VRecord fs

    TVAbstract {} -> evalPanic "logicUnary" [ "Abstract type not in `Logic`" ]


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
                          WordVal (BV _ x) -> return $ WordVal (BV w (opW w x i))
                          BitsVal bs -> return $ BitsVal (obB w bs i)
                          LargeBitsVal n xs -> return $ LargeBitsVal n $ opS (Nat n) c xs i

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

-- | Indexing operations.
indexPrim :: BitWord b w i
          => (Maybe Integer -> TValue -> SeqMap b w i -> Seq.Seq b -> Eval (GenValue b w i))
          -> (Maybe Integer -> TValue -> SeqMap b w i -> w -> Eval (GenValue b w i))
          -> GenValue b w i
indexPrim bits_op word_op =
  nlam $ \ n  ->
  tlam $ \ a ->
  nlam $ \ _i ->
   lam $ \ l  -> return $
   lam $ \ r  -> do
      vs <- l >>= \case
               VWord _ w  -> w >>= \w' -> return $ IndexSeqMap (\i -> VBit <$> indexWordValue w' i)
               VSeq _ vs  -> return vs
               VStream vs -> return vs
               _ -> evalPanic "Expected sequence value" ["indexPrim"]
      r >>= \case
         VWord _ w -> w >>= \case
           WordVal w' -> word_op (fromNat n) a vs w'
           BitsVal bs -> bits_op (fromNat n) a vs =<< sequence bs
           LargeBitsVal m xs -> bits_op (fromNat n) a vs . Seq.fromList =<< traverse (fromBit =<<) (enumerateSeqMap m xs)
         _ -> evalPanic "Expected word value" ["indexPrim"]

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


updateFront
  :: Nat'
  -> TValue
  -> SeqMap Bool BV Integer
  -> WordValue Bool BV Integer
  -> Eval (GenValue Bool BV Integer)
  -> Eval (SeqMap Bool BV Integer)
updateFront len _eltTy vs w val = do
  idx <- bvVal <$> asWordVal w
  case len of
    Inf -> return ()
    Nat n -> unless (idx < n) (invalidIndex idx)
  return $ updateSeqMap vs idx val

updateFront_word
 :: Nat'
 -> TValue
 -> WordValue Bool BV Integer
 -> WordValue Bool BV Integer
 -> Eval (GenValue Bool BV Integer)
 -> Eval (WordValue Bool BV Integer)
updateFront_word _len _eltTy bs w val = do
  idx <- bvVal <$> asWordVal w
  updateWordValue bs idx (fromBit =<< val)

updateBack
  :: Nat'
  -> TValue
  -> SeqMap Bool BV Integer
  -> WordValue Bool BV Integer
  -> Eval (GenValue Bool BV Integer)
  -> Eval (SeqMap Bool BV Integer)
updateBack Inf _eltTy _vs _w _val =
  evalPanic "Unexpected infinite sequence in updateEnd" []
updateBack (Nat n) _eltTy vs w val = do
  idx <- bvVal <$> asWordVal w
  unless (idx < n) (invalidIndex idx)
  return $ updateSeqMap vs (n - idx - 1) val

updateBack_word
 :: Nat'
 -> TValue
 -> WordValue Bool BV Integer
 -> WordValue Bool BV Integer
 -> Eval (GenValue Bool BV Integer)
 -> Eval (WordValue Bool BV Integer)
updateBack_word Inf _eltTy _bs _w _val =
  evalPanic "Unexpected infinite sequence in updateEnd" []
updateBack_word (Nat n) _eltTy bs w val = do
  idx <- bvVal <$> asWordVal w
  updateWordValue bs (n - idx - 1) (fromBit =<< val)

{-
  idx <- bvVal <$> asWordVal w
  unless (idx < n) (invalidIndex idx)
  let idx' = n - idx - 1
  return $! Seq.update (fromInteger idx') (fromVBit <$> val) bs
-}


updatePrim
     :: BitWord b w i
     => (Nat' -> TValue -> WordValue b w i -> WordValue b w i -> Eval (GenValue b w i) -> Eval (WordValue b w i))
     -> (Nat' -> TValue -> SeqMap b w i    -> WordValue b w i -> Eval (GenValue b w i) -> Eval (SeqMap b w i))
     -> GenValue b w i
updatePrim updateWord updateSeq =
  nlam $ \len ->
  tlam $ \eltTy ->
  nlam $ \_idxLen ->
  lam $ \xs  -> return $
  lam $ \idx -> return $
  lam $ \val -> do
    idx' <- fromWordVal "update" =<< idx
    xs >>= \case
      VWord l w  -> do w' <- delay Nothing w
                       return $ VWord l (w' >>= \w'' -> updateWord len eltTy w'' idx' val)
      VSeq l vs  -> VSeq l  <$> updateSeq len eltTy vs idx' val
      VStream vs -> VStream <$> updateSeq len eltTy vs idx' val
      _ -> evalPanic "Expected sequence value" ["updatePrim"]

-- @[ 0 .. 10 ]@
fromToV :: BitWord b w i
        => GenValue b w i
fromToV  =
  nlam $ \ first ->
  nlam $ \ lst   ->
  tlam $ \ ty    ->
    let !f = mkLit ty in
    case (first, lst) of
      (Nat first', Nat lst') ->
        let len = 1 + (lst' - first')
        in VSeq len $ IndexSeqMap $ \i -> ready $ f (first' + i)
      _ -> evalPanic "fromToV" ["invalid arguments"]

-- @[ 0, 1 .. 10 ]@
fromThenToV :: BitWord b w i
            => GenValue b w i
fromThenToV  =
  nlam $ \ first ->
  nlam $ \ next  ->
  nlam $ \ lst   ->
  tlam $ \ ty    ->
  nlam $ \ len   ->
    let !f = mkLit ty in
    case (first, next, lst, len) of
      (Nat first', Nat next', Nat _lst', Nat len') ->
        let diff = next' - first'
        in VSeq len' $ IndexSeqMap $ \i -> ready $ f (first' + i*diff)
      _ -> evalPanic "fromThenToV" ["invalid arguments"]


infFromV :: BitWord b w i => GenValue b w i
infFromV =
  tlam $ \ ty ->
  lam  $ \ x' ->
  return $ VStream $ IndexSeqMap $ \i ->
  do x <- x'
     addV ty x (intV (integerLit i) ty)

infFromThenV :: BitWord b w i => GenValue b w i
infFromThenV =
  tlam $ \ ty ->
  lam $ \ first -> return $
  lam $ \ next ->
  do x <- first
     y <- next
     d <- subV ty y x
     return $ VStream $ IndexSeqMap $ \i ->
       addV ty x =<< mulV ty d (intV (integerLit i) ty)

-- Random Values ---------------------------------------------------------------

-- | Produce a random value with the given seed. If we do not support
-- making values of the given type, return zero of that type.
-- TODO: do better than returning zero
randomV :: BitWord b w i => TValue -> Integer -> GenValue b w i
randomV ty seed =
  case randomValue (tValTy ty) of
    Nothing -> zeroV ty
    Just gen ->
      -- unpack the seed into four Word64s
      let mask64 = 0xFFFFFFFFFFFFFFFF
          unpack s = fromInteger (s .&. mask64) : unpack (s `shiftR` 64)
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
  TVIntMod _ -> cryUserError msg

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

  TVAbstract {} -> cryUserError msg
