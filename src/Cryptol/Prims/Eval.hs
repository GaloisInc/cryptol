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

import Data.List (sortBy)
import Data.Ord (comparing)
import Data.Bits (Bits(..))

import qualified Data.Map.Strict as Map
import qualified Data.Text as T

import System.Random.TF.Gen (seedTFGen)

-- Primitives ------------------------------------------------------------------

instance EvalPrims Bool BV where
  evalPrim Decl { dName = n, .. }
    | Just prim <- asPrim n, Just val <- Map.lookup prim primTable = val

  evalPrim Decl { .. } =
      panic "Eval" [ "Unimplemented primitive", show dName ]

  iteValue b t f = if b then t else f


primTable :: Map.Map Ident Value
primTable = Map.fromList $ map (\(n, v) -> (mkIdent (T.pack n), v))
  [ ("+"          , {-# SCC "Prelude::(+)" #-}
                    binary (arithBinary (liftBinArith (+))))
  , ("-"          , {-# SCC "Prelude::(-)" #-}
                    binary (arithBinary (liftBinArith (-))))
  , ("*"          , {-# SCC "Prelude::(*)" #-}
                    binary (arithBinary (liftBinArith (*))))
  , ("/"          , {-# SCC "Prelude::(/)" #-}
                    binary (arithBinary (liftDivArith div)))
  , ("%"          , {-# SCC "Prelude::(%)" #-}
                    binary (arithBinary (liftDivArith mod)))
  , ("^^"         , {-# SCC "Prelude::(^^)" #-}
                    binary (arithBinary modExp))
  , ("lg2"        , {-# SCC "Prelude::lg2" #-}
                    unary  (arithUnary (liftUnaryArith lg2)))
  , ("negate"     , {-# SCC "Prelude::negate" #-}
                    unary  (arithUnary (liftUnaryArith negate)))
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
                    liftSigned bvSdiv)
  , ("%$"         , {-# SCC "Prelude::(%$)" #-}
                    liftSigned bvSrem)
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
  , ("<<"         , {-# SCC "Prelude::(<<)" #-}
                    logicShift shiftLW shiftLS)
  , (">>"         , {-# SCC "Prelude::(>>)" #-}
                    logicShift shiftRW shiftRS)
  , ("<<<"        , {-# SCC "Prelude::(<<<)" #-}
                    logicShift rotateLW rotateLS)
  , (">>>"        , {-# SCC "Prelude::(>>>)" #-}
                    logicShift rotateRW rotateRS)
  , ("True"       , VBit True)
  , ("False"      , VBit False)

  , ("carry"      , {-# SCC "Prelude::carry" #-}
                    carryV)
  , ("scarry"     , {-# SCC "Prelude::scarry" #-}
                    scarryV)
  , ("demote"     , {-# SCC "Prelude::demote" #-}
                    ecDemoteV)

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
        wlam $ \(bvVal -> y) -> return $ word (1 + a + b) (mul 0 x y (1+b)))

  , ("pdiv"        , {-# SCC "Prelude::pdiv" #-}
                     nlam $ \(fromInteger . finNat' -> a) ->
                     nlam $ \(fromInteger . finNat' -> b) ->
                     wlam $ \(bvVal -> x) -> return $
                     wlam $ \(bvVal -> y) ->
                       if y == 0
                        then divideByZero
                        else return . word (toInteger a) . fst
                               $ divModPoly x a y b)

  , ("pmod"        , {-# SCC "Prelude::pmod" #-}
                     nlam $ \(fromInteger . finNat' -> a) ->
                     nlam $ \(fromInteger . finNat' -> b) ->
                     wlam $ \(bvVal -> x) -> return $
                     wlam $ \(bvVal -> y) ->
                       if y == 0
                         then divideByZero
                         else return . word (toInteger b) . snd
                                $ divModPoly x a y (b+1))

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
ecDemoteV :: BitWord b w => GenValue b w
ecDemoteV = nlam $ \valT ->
            nlam $ \bitT ->
            case (valT, bitT) of
              (Nat v, Nat bs) -> word bs v
              _ -> evalPanic "Cryptol.Eval.Prim.evalConst"
                       ["Unexpected Inf in constant."
                       , show valT
                       , show bitT
                       ]

--------------------------------------------------------------------------------
divModPoly :: Integer -> Int -> Integer -> Int -> (Integer, Integer)
divModPoly xs xsLen ys ysLen
  | ys == 0         = panic "divModPoly"
                             [ "Uncaught divide-by-zero condition" ]
  | degree <= xsLen = go 0 initR (xsLen - degree) todoBits
  | otherwise       = (0, xs) -- xs is already a residue, just return it

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

type Binary b w = TValue -> GenValue b w -> GenValue b w -> Eval (GenValue b w)

binary :: Binary b w -> GenValue b w
binary f = tlam $ \ ty ->
            lam $ \ a  -> return $
            lam $ \ b  -> do
               --io $ putStrLn "Entering a binary function"
               join (f ty <$> a <*> b)

type Unary b w = TValue -> GenValue b w -> Eval (GenValue b w)

unary :: Unary b w -> GenValue b w
unary f = tlam $ \ ty ->
           lam $ \ a  -> f ty =<< a


-- Arith -----------------------------------------------------------------------

-- | Turn a normal binop on Integers into one that can also deal with a bitsize.
liftBinArith :: (Integer -> Integer -> Integer) -> BinArith BV
liftBinArith op w (BV _ x) (BV _ y) = ready $ mkBv w $ op x y

-- | Turn a normal binop on Integers into one that can also deal with a bitsize.
--   Generate a thunk that throws a divide by 0 error when forced if the second
--   argument is 0.
liftDivArith :: (Integer -> Integer -> Integer) -> BinArith BV
liftDivArith _  _ _        (BV _ 0) = divideByZero
liftDivArith op w (BV _ x) (BV _ y) = ready $ mkBv w $ op x y

type BinArith w = Integer -> w -> w -> Eval w

arithBinary :: forall b w
             . BitWord b w
            => BinArith w
            -> Binary b w
arithBinary op = loop
  where
  loop' :: TValue
        -> Eval (GenValue b w)
        -> Eval (GenValue b w)
        -> Eval (GenValue b w)
  loop' ty l r = join (loop ty <$> l <*> r)

  loop :: TValue
       -> GenValue b w
       -> GenValue b w
       -> Eval (GenValue b w)
  loop ty l r = case ty of
    TVBit ->
      evalPanic "arithBinary" ["Bit not in class Arith"]

    TVSeq w a
      -- words and finite sequences
      | isTBit a -> do
                  lw <- fromVWord "arithLeft" l
                  rw <- fromVWord "arithRight" r
                  return $ VWord w (WordVal <$> op w lw rw)
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

type UnaryArith w = Integer -> w -> Eval w

liftUnaryArith :: (Integer -> Integer) -> UnaryArith BV
liftUnaryArith op w (BV _ x) = ready $ mkBv w $ op x

arithUnary :: forall b w
            . BitWord b w
           => UnaryArith w
           -> Unary b w
arithUnary op = loop
  where
  loop' :: TValue -> Eval (GenValue b w) -> Eval (GenValue b w)
  loop' ty x = loop ty =<< x

  loop :: TValue -> GenValue b w -> Eval (GenValue b w)
  loop ty x = case ty of

    TVBit ->
      evalPanic "arithUnary" ["Bit not in class Arith"]

    TVSeq w a
      -- words and finite sequences
      | isTBit a -> do
              wx <- fromVWord "arithUnary" x
              return $ VWord w (WordVal <$> op w wx)
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

--    | otherwise = evalPanic "arithUnary" ["Invalid arguments"]


lg2 :: Integer -> Integer
lg2 i = case genLog i 2 of
  Just (i',isExact) | isExact   -> i'
                    | otherwise -> i' + 1
  Nothing                       -> 0

-- Cmp -------------------------------------------------------------------------

cmpValue :: BitWord b w
         => (b -> b -> Eval a -> Eval a)
         -> (w -> w -> Eval a -> Eval a)
         -> (GenValue b w -> GenValue b w -> Eval a -> Eval a)
cmpValue fb fw = cmp
  where
    cmp v1 v2 k =
      case (v1, v2) of
        (VRecord fs1, VRecord fs2) -> let vals = map snd . sortBy (comparing fst)
                                      in  cmpValues (vals fs1) (vals fs2) k
        (VTuple vs1 , VTuple vs2 ) -> cmpValues vs1 vs2 k
        (VBit b1    , VBit b2    ) -> fb b1 b2 k
        (VWord _ w1 , VWord _ w2 ) -> join (fw <$> (asWordVal =<< w1)
                                               <*> (asWordVal =<< w2)
                                               <*> return k)
        (VSeq n vs1 , VSeq _ vs2 ) -> cmpValues (enumerateSeqMap n vs1)
                                                (enumerateSeqMap n vs2) k
        (VStream {} , VStream {} ) -> panic "Cryptol.Prims.Value.cmpValue"
                                        [ "Infinite streams are not comparable" ]
        (VFun {}    , VFun {}    ) -> panic "Cryptol.Prims.Value.cmpValue"
                                        [ "Functions are not comparable" ]
        (VPoly {}   , VPoly {}   ) -> panic "Cryptol.Prims.Value.cmpValue"
                                        [ "Polymorphic values are not comparable" ]
        (_          , _          ) -> panic "Cryptol.Prims.Value.cmpValue"
                                        [ "type mismatch" ]

    cmpValues (x1 : xs1) (x2 : xs2) k = do
          x1' <- x1
          x2' <- x2
          cmp x1' x2' (cmpValues xs1 xs2 k)
    cmpValues _ _ k = k


lexCompare :: Value -> Value -> Eval Ordering
lexCompare a b = cmpValue op opw a b (return EQ)
 where
   opw :: BV -> BV -> Eval Ordering -> Eval Ordering
   opw x y k = op (bvVal x) (bvVal y) k

   op :: Ord a => a -> a -> Eval Ordering -> Eval Ordering
   op x y k = case compare x y of
                     EQ  -> k
                     cmp -> return cmp

signedLexCompare :: Value -> Value -> Eval Ordering
signedLexCompare a b = cmpValue opb opw a b (return EQ)
 where
   opb :: Bool -> Bool -> Eval Ordering -> Eval Ordering
   opb _x _y _k = panic "signedLexCompare"
                    ["Attempted to perform signed comparisons on bare Bit type"]

   opw :: BV -> BV -> Eval Ordering -> Eval Ordering
   opw x y k = case compare (signedBV x) (signedBV y) of
                     EQ  -> k
                     cmp -> return cmp

-- | Process two elements based on their lexicographic ordering.
cmpOrder :: String -> (Ordering -> Bool) -> Binary Bool BV
cmpOrder _nm op _ty l r = VBit . op <$> lexCompare l r

-- | Process two elements based on their lexicographic ordering, using signed comparisons
signedCmpOrder :: String -> (Ordering -> Bool) -> Binary Bool BV
signedCmpOrder _nm op _ty l r = VBit . op <$> signedLexCompare l r


-- Signed arithmetic -----------------------------------------------------------

-- | Lifted operation on finite bitsequences.  Used
--   for signed comparisons and arithemtic.
liftWord :: BitWord b w
         => (w -> w -> Eval (GenValue b w))
         -> GenValue b w
liftWord op =
  nlam $ \_n ->
  wlam $ \w1 -> return $
  wlam $ \w2 -> op w1 w2

liftSigned :: (Integer -> Integer -> Integer -> Eval Value)
           -> Value
liftSigned op = liftWord f
 where
 f (BV i x) (BV j y)
   | i == j = op i sx sy
   | otherwise = evalPanic "liftSigned" ["Attempt to compute with words of different sizes"]
   where sx = signedValue i x
         sy = signedValue j y

signedBV :: BV -> Integer
signedBV (BV i x) = signedValue i x

signedValue :: Integer -> Integer -> Integer
signedValue i x = if testBit x (fromIntegral (i-1)) then x - (1 `shiftL` (fromIntegral i)) else x

bvSlt :: Integer -> Integer -> Integer -> Eval Value
bvSlt _sz x y = return . VBit $! (x < y)

bvSdiv :: Integer -> Integer -> Integer -> Eval Value
bvSdiv  _ _ 0 = divideByZero
bvSdiv sz x y = return . VWord sz . ready . WordVal $ mkBv sz (x `quot` y)

bvSrem :: Integer -> Integer -> Integer -> Eval Value
bvSrem  _ _ 0 = divideByZero
bvSrem sz x y = return . VWord sz . ready . WordVal $ mkBv sz (x `rem` y)

sshrV :: Value
sshrV =
  nlam $ \_n ->
  nlam $ \_k ->
  wlam $ \(BV i x) -> return $
  wlam $ \y ->
   let signx = testBit x (fromIntegral (i-1))
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

zeroV :: forall b w
       . BitWord b w
      => TValue
      -> GenValue b w
zeroV ty = case ty of

  -- bits
  TVBit ->
    VBit (bitLit False)

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


joinWordVal :: BitWord b w =>
            WordValue b w -> WordValue b w -> WordValue b w
joinWordVal (WordVal w1) (WordVal w2)
  | wordLen w1 + wordLen w2 < largeBitSize
  = WordVal $ joinWord w1 w2
joinWordVal w1 w2
  = BitsVal (n1+n2) (concatSeqMap n1 (asBitsMap w1) (asBitsMap w2))
 where n1 = wordValueSize w1
       n2 = wordValueSize w2


joinWords :: forall b w
           . BitWord b w
          => Integer
          -> Integer
          -> SeqMap b w
          -> Eval (GenValue b w)
joinWords nParts nEach xs =
  loop (ready $ WordVal (wordLit 0 0)) (enumerateSeqMap nParts xs)

 where
 loop :: Eval (WordValue b w) -> [Eval (GenValue b w)] -> Eval (GenValue b w)
 loop !wv [] = return $ VWord (nParts * nEach) wv
 loop !wv (w : ws) = do
    w >>= \case
      VWord _ w' -> loop (joinWordVal <$> wv <*> w') ws
      _ -> evalPanic "joinWords: expected word value" []


joinSeq :: BitWord b w
        => Nat'
        -> Integer
        -> TValue
        -> SeqMap b w
        -> Eval (GenValue b w)

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
       return $ VWord (parts * each) $ ready $ BitsVal (parts * each) zs

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
joinV :: BitWord b w
      => Nat'
      -> Integer
      -> TValue
      -> GenValue b w
      -> Eval (GenValue b w)
joinV parts each a val = joinSeq parts each a =<< fromSeq "joinV" val


splitWordVal :: BitWord b w
             => Integer
             -> Integer
             -> WordValue b w
             -> (WordValue b w, WordValue b w)
splitWordVal leftWidth rightWidth (WordVal w) =
  let (lw, rw) = splitWord leftWidth rightWidth w
   in (WordVal lw, WordVal rw)
splitWordVal leftWidth rightWidth (BitsVal _n xs) =
  let (lxs, rxs) = splitSeqMap leftWidth xs
   in (BitsVal leftWidth lxs, BitsVal rightWidth rxs)

splitAtV :: BitWord b w
         => Nat'
         -> Nat'
         -> TValue
         -> GenValue b w
         -> Eval (GenValue b w)
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
       ls <- delay Nothing (fst . splitSeqMap leftWidth <$> vs)
       rs <- delay Nothing (snd . splitSeqMap leftWidth <$> vs)
       return $ VTuple [ return $ VWord leftWidth (BitsVal leftWidth <$> ls)
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
  --   way, the operation `extractWordVal n i w` is equivelant to
  --   first shifting `w` right by `i` bits, and then truncating to
  --   `n` bits.
extractWordVal :: BitWord b w
               => Integer
               -> Integer
               -> WordValue b w
               -> WordValue b w
extractWordVal len start (WordVal w) =
   WordVal $ extractWord len start w
extractWordVal len start (BitsVal n xs) =
   let xs' = dropSeqMap (n - start - len) xs
    in BitsVal len xs'


-- | Split implementation.
ecSplitV :: BitWord b w
         => GenValue b w
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
            return $ VWord e $ return $ BitsVal e $ IndexSeqMap $ \j ->
              let idx = i*e + toInteger j
               in idx `seq` do
                      xs <- val'
                      lookupSeqMap xs idx
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


reverseV :: forall b w
          . BitWord b w
         => GenValue b w
         -> Eval (GenValue b w)
reverseV (VSeq n xs) =
  return $ VSeq n $ reverseSeqMap n xs
reverseV (VWord n wv) = return (VWord n (revword <$> wv))
 where
 revword w = BitsVal m (reverseSeqMap m (asBitsMap w))
   where m = wordValueSize w
reverseV _ =
  evalPanic "reverseV" ["Not a finite sequence"]


transposeV :: BitWord b w
           => Nat'
           -> Nat'
           -> TValue
           -> GenValue b w
           -> Eval (GenValue b w)
transposeV a b c xs
  | isTBit c, Nat na <- a = -- Fin a => [a][b]Bit -> [b][a]Bit
      return $ bseq $ IndexSeqMap $ \bi ->
        return $ VWord na $ return $ BitsVal na $
          IndexSeqMap $ \ai -> do
            ys <- flip lookupSeqMap (toInteger ai) =<< fromSeq "transposeV" xs
            case ys of
              VStream ys' -> lookupSeqMap ys' bi
              VWord _ wv  -> VBit <$> (flip indexWordValue bi =<< wv)
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




ccatV :: (Show b, Show w, BitWord b w)
      => Nat'
      -> Nat'
      -> TValue
      -> (GenValue b w)
      -> (GenValue b w)
      -> Eval (GenValue b w)

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

wordValLogicOp :: BitWord b w
               => (b -> b -> b)
               -> (w -> w -> w)
               -> WordValue b w
               -> WordValue b w
               -> WordValue b w
wordValLogicOp _ wop (WordVal w1) (WordVal w2) = WordVal (wop w1 w2)
wordValLogicOp bop _ w1 w2 = BitsVal (wordValueSize w1) zs
     where zs = IndexSeqMap $ \i -> VBit <$> (bop <$> (fromBit =<< lookupSeqMap xs i) <*> (fromBit =<< lookupSeqMap ys i))
           xs = asBitsMap w1
           ys = asBitsMap w2

-- | Merge two values given a binop.  This is used for and, or and xor.
logicBinary :: forall b w
             . BitWord b w
            => (b -> b -> b)
            -> (w -> w -> w)
            -> Binary b w
logicBinary opb opw  = loop
  where
  loop' :: TValue
        -> Eval (GenValue b w)
        -> Eval (GenValue b w)
        -> Eval (GenValue b w)
  loop' ty l r = join (loop ty <$> l <*> r)

  loop :: TValue
        -> GenValue b w
        -> GenValue b w
        -> Eval (GenValue b w)

  loop ty l r = case ty of
    TVBit -> return $ VBit (opb (fromVBit l) (fromVBit r))
    TVSeq w aty
         -- words
         | isTBit aty
              -> do v <- delay Nothing
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


wordValUnaryOp :: BitWord b w
               => (b -> b)
               -> (w -> w)
               -> WordValue b w
               -> Eval (WordValue b w)
wordValUnaryOp _ wop (WordVal w)  = return $ WordVal (wop w)
wordValUnaryOp bop _ (BitsVal n xs) = BitsVal n <$> mapSeqMap f xs
  where f x = VBit . bop <$> fromBit x

logicUnary :: forall b w
            . BitWord b w
           => (b -> b)
           -> (w -> w)
           -> Unary b w
logicUnary opb opw = loop
  where
  loop' :: TValue -> Eval (GenValue b w) -> Eval (GenValue b w)
  loop' ty val = loop ty =<< val

  loop :: TValue -> GenValue b w -> Eval (GenValue b w)
  loop ty val = case ty of
    TVBit -> return . VBit . opb $ fromVBit val

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


logicShift :: (Integer -> Integer -> Integer -> Integer)
              -- ^ The function may assume its arguments are masked.
              -- It is responsible for masking its result if needed.
           -> (Nat' -> TValue -> SeqValMap -> Integer -> SeqValMap)
           -> Value
logicShift opW opS
  = nlam $ \ a ->
    nlam $ \ _ ->
    tlam $ \ c ->
     lam  $ \ l -> return $
     lam  $ \ r -> do
        BV _ i <- fromVWord "logicShift amount" =<< r
        l >>= \case
          VWord w wv -> return $ VWord w $ wv >>= \case
                          WordVal (BV _ x) -> return $ WordVal (BV w (opW w x i))
                          BitsVal n xs -> return $ BitsVal n $ opS (Nat n) c xs i

          _ -> mkSeq a c <$> (opS a c <$> (fromSeq "logicShift" =<< l) <*> return i)

-- Left shift for words.
shiftLW :: Integer -> Integer -> Integer -> Integer
shiftLW w ival by
  | by >= w   = 0
  | otherwise = mask w (shiftL ival (fromInteger by))

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

rotateRS :: Nat' -> TValue -> SeqValMap -> Integer -> SeqValMap
rotateRS w _ vs by = IndexSeqMap $ \i ->
  case w of
    Nat len -> lookupSeqMap vs ((len - by + i) `mod` len)
    _ -> panic "Cryptol.Eval.Prim.rotateRS" [ "unexpected infinite sequence" ]


-- Sequence Primitives ---------------------------------------------------------

-- | Indexing operations that return one element.
indexPrimOne :: BitWord b w
             => (Maybe Integer -> TValue -> SeqMap b w -> [b] -> Eval (GenValue b w))
             -> (Maybe Integer -> TValue -> SeqMap b w -> w -> Eval (GenValue b w))
             -> GenValue b w
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
           BitsVal m xs -> bits_op (fromNat n) a vs =<< traverse (fromBit =<<) (enumerateSeqMap m xs)
         _ -> evalPanic "Expected word value" ["indexPrimOne"]

indexFront :: Maybe Integer -> TValue -> SeqValMap -> BV -> Eval Value
indexFront mblen _a vs (bvVal -> ix) =
  case mblen of
    Just len | len <= ix -> invalidIndex ix
    _                    -> lookupSeqMap vs ix

indexFront_bits :: Maybe Integer -> TValue -> SeqValMap -> [Bool] -> Eval Value
indexFront_bits mblen a vs = indexFront mblen a vs . packWord

indexBack :: Maybe Integer -> TValue -> SeqValMap -> BV -> Eval Value
indexBack mblen _a vs (bvVal -> ix) =
  case mblen of
    Just len | len > ix  -> lookupSeqMap vs (len - ix - 1)
             | otherwise -> invalidIndex ix
    Nothing              -> evalPanic "indexBack"
                            ["unexpected infinite sequence"]

indexBack_bits :: Maybe Integer -> TValue -> SeqValMap -> [Bool] -> Eval Value
indexBack_bits mblen a vs = indexBack mblen a vs . packWord

-- | Indexing operations that return many elements.
indexPrimMany :: BitWord b w
              => (Maybe Integer -> TValue -> SeqMap b w -> [b] -> Eval (GenValue b w))
              -> (Maybe Integer -> TValue -> SeqMap b w -> w -> Eval (GenValue b w))
              -> GenValue b w
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
            BitsVal o xs -> bits_op (fromNat n) a vs =<< traverse (fromBit =<<) (enumerateSeqMap o xs)
         _ -> evalPanic "Expected word value" ["indexPrimMany"])


updateFront
  :: Nat'
  -> TValue
  -> SeqMap Bool BV
  -> WordValue Bool BV
  -> Eval (GenValue Bool BV)
  -> Eval (SeqMap Bool BV)
updateFront len _eltTy vs w val = do
  idx <- bvVal <$> asWordVal w
  case len of
    Inf -> return ()
    Nat n -> unless (idx < n) (invalidIndex idx)
  return $ updateSeqMap vs idx val

updateFront_word
 :: Nat'
 -> TValue
 -> WordValue Bool BV
 -> WordValue Bool BV
 -> Eval (GenValue Bool BV)
 -> Eval (WordValue Bool BV)
updateFront_word _len _eltTy bs w val = do
  idx <- bvVal <$> asWordVal w
  updateWordValue bs idx (fromBit =<< val)

updateBack
  :: Nat'
  -> TValue
  -> SeqMap Bool BV
  -> WordValue Bool BV
  -> Eval (GenValue Bool BV)
  -> Eval (SeqMap Bool BV)
updateBack Inf _eltTy _vs _w _val =
  evalPanic "Unexpected infinite sequence in updateEnd" []
updateBack (Nat n) _eltTy vs w val = do
  idx <- bvVal <$> asWordVal w
  unless (idx < n) (invalidIndex idx)
  return $ updateSeqMap vs (n - idx - 1) val

updateBack_word
 :: Nat'
 -> TValue
 -> WordValue Bool BV
 -> WordValue Bool BV
 -> Eval (GenValue Bool BV)
 -> Eval (WordValue Bool BV)
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
     :: BitWord b w
     => (Nat' -> TValue -> WordValue b w -> WordValue b w -> Eval (GenValue b w) -> Eval (WordValue b w))
     -> (Nat' -> TValue -> SeqMap b w    -> WordValue b w -> Eval (GenValue b w) -> Eval (SeqMap b w))
     -> GenValue b w
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

-- @[ 0, 1 .. ]@
fromThenV :: BitWord b w
          => GenValue b w
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
fromToV :: BitWord b w
        => GenValue b w
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
fromThenToV :: BitWord b w
            => GenValue b w
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


infFromV :: BitWord b w
         => GenValue b w
infFromV =
     nlam $ \(finNat' -> bits)  ->
     wlam $ \first ->
     return $ VStream $ IndexSeqMap $ \i ->
       ready $ VWord bits $ return $
         WordVal $ wordPlus first (wordLit bits i)

infFromThenV :: BitWord b w
             => GenValue b w
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
randomV :: BitWord b w => TValue -> Integer -> GenValue b w
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

errorV :: forall b w
       . BitWord b w
      => TValue
      -> String
      -> Eval (GenValue b w)
errorV ty msg = case ty of
  -- bits
  TVBit -> cryUserError msg

  -- sequences
  TVSeq w ety
     | isTBit ety -> return $ VWord w $ return $ BitsVal w $ IndexSeqMap $ \_ -> cryUserError msg
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
