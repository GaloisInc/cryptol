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
module Cryptol.Prims.Eval where

import Control.Monad (join)

import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Solver.InfNat (Nat'(..),fromNat,genLog, nMul)
import qualified Cryptol.Eval.Arch as Arch
import Cryptol.Eval.Env
import Cryptol.Eval.Monad
import Cryptol.Eval.Type(evalTF)
import Cryptol.Eval.Value
import Cryptol.Testing.Random (randomValue)
import Cryptol.Utils.Panic (panic)
import Cryptol.ModuleSystem.Name (asPrim)
import Cryptol.Utils.Ident (Ident,mkIdent)
import Cryptol.Utils.PP

import Data.List (sortBy, transpose, genericTake, genericDrop,
                  genericReplicate, genericSplitAt, genericIndex,
                  foldl')
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
  [ ("+"          , binary (arithBinary (liftBinArith (+))))
  , ("-"          , binary (arithBinary (liftBinArith (-))))
  , ("*"          , binary (arithBinary (liftBinArith (*))))
  , ("/"          , binary (arithBinary (liftBinArith divWrap)))
  , ("%"          , binary (arithBinary (liftBinArith modWrap)))
  , ("^^"         , binary (arithBinary modExp))
  , ("lg2"        , unary  (arithUnary lg2))
  , ("negate"     , unary  (arithUnary negate))
  , ("<"          , binary (cmpOrder "<"  (\o -> o == LT           )))
  , (">"          , binary (cmpOrder ">"  (\o -> o == GT           )))
  , ("<="         , binary (cmpOrder "<=" (\o -> o == LT || o == EQ)))
  , (">="         , binary (cmpOrder ">=" (\o -> o == GT || o == EQ)))
  , ("=="         , binary (cmpOrder "==" (\o ->            o == EQ)))
  , ("!="         , binary (cmpOrder "!=" (\o ->            o /= EQ)))
  , ("&&"         , binary (logicBinary (.&.)))
  , ("||"         , binary (logicBinary (.|.)))
  , ("^"          , binary (logicBinary xor))
  , ("complement" , unary  (logicUnary complement))
  , ("<<"         , logicShift shiftLW shiftLS)
  , (">>"         , logicShift shiftRW shiftRS)
  , ("<<<"        , logicShift rotateLW rotateLS)
  , (">>>"        , logicShift rotateRW rotateRS)
  , ("True"       , VBit True)
  , ("False"      , VBit False)

  , ("demote"     , ecDemoteV)

  , ("#"          , tlam $ \ front ->
                    tlam $ \ back  ->
                    tlam $ \ elty  ->
                    lam  $ \ l     -> return $
                    lam  $ \ r     -> ccatV front back elty l r)

  , ("@"          , indexPrimOne  indexFront)
  , ("@@"         , indexPrimMany indexFront)
  , ("!"          , indexPrimOne  indexBack)
  , ("!!"         , indexPrimMany indexBack)

  , ("zero"       , tlam zeroV)

  , ("join"       , tlam $ \ parts ->
                    tlam $ \ each  ->
                    tlam $ \ a     ->
                    lam  $ \ x     ->
                      joinV parts each a =<< x)

  , ("split"      , ecSplitV)

  , ("splitAt"    , tlam $ \ front ->
                    tlam $ \ back  ->
                    tlam $ \ a     ->
                    lam  $ \ x     ->
                       splitAtV front back a =<< x)

  , ("fromThen"   , fromThenV)
  , ("fromTo"     , fromToV)
  , ("fromThenTo" , fromThenToV)

  , ("infFrom"    , tlam $ \(finTValue -> bits)  ->
                    wlam $ \first ->
                    return $ VStream $ SeqMap $ \i ->
                       ready $ word bits (first+i))

  , ("infFromThen", tlam $ \(finTValue -> bits)  ->
                    wlam $ \first -> return $
                    wlam $ \next  -> do
                    let diff = next - first
                    return $ VStream $ SeqMap $ \i ->
                       ready $ word bits (first + diff*i))

  , ("error"      , tlam $ \_ ->
                    tlam $ \_ ->
                     lam $ \s -> cryUserError =<< (fromStr =<< s))

  , ("reverse"    , tlam $ \a ->
                    tlam $ \b ->
                     lam $ \xs -> reverseV =<< xs)

  , ("transpose"  , tlam $ \a ->
                    tlam $ \b ->
                    tlam $ \c ->
                     lam $ \xs -> transposeV a b c =<< xs)

  , ("pmult"       ,
    let mul !res !_ !_ 0 = res
        mul  res bs as n = mul (if even as then res else xor res bs)
                               (bs `shiftL` 1) (as `shiftR` 1) (n-1)
     in tlam $ \(finTValue -> a) ->
        tlam $ \(finTValue -> b) ->
        wlam $ \x -> return $
        wlam $ \y -> return $ word (max 1 (a + b) - 1) (mul 0 x y b))

  , ("pdiv"        , tlam $ \(fromInteger . finTValue -> a) ->
                     tlam $ \(fromInteger . finTValue -> b) ->
                     wlam $ \x -> return $
                     wlam $ \y -> return $ word (toInteger a)
                                                (fst (divModPoly x a y b)))

  , ("pmod"        , tlam $ \(fromInteger . finTValue -> a) ->
                     tlam $ \(fromInteger . finTValue -> b) ->
                     wlam $ \x -> return $
                     wlam $ \y -> return $ word (toInteger b)
                                                (snd (divModPoly x a y (b+1))))
  , ("random"      , tlam $ \a ->
                     wlam $ \x -> return $ randomV a x)
  , ("trace"       , tlam $ \_n ->
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
ecDemoteV :: Value
ecDemoteV = tlam $ \valT ->
            tlam $ \bitT ->
            case (numTValue valT, numTValue bitT) of
              (Nat v, Nat bs) -> VWord (mkBv bs v)
              _ -> evalPanic "Cryptol.Eval.Prim.evalConst"
                       ["Unexpected Inf in constant."
                       , show valT
                       , show bitT
                       ]

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

type GenUnary b w = TValue -> GenValue b w -> Eval (GenValue b w)
type Unary = GenUnary Bool BV

unary :: GenUnary b w -> GenValue b w
unary f = tlam $ \ ty ->
           lam $ \ a  -> f ty =<< a


-- Arith -----------------------------------------------------------------------

-- | Turn a normal binop on Integers into one that can also deal with a bitsize.
liftBinArith :: (Integer -> Integer -> Integer) -> BinArith BV
liftBinArith op w (BV _ x) (BV _ y) = mkBv w $ op x y

type BinArith w = Integer -> w -> w -> w

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
  loop ty l r

    | Just (len,a) <- isTSeq ty = case numTValue len of

      -- words and finite sequences
      Nat w | isTBit a -> do
                  lw <- fromVWord "arithLeft" l
                  rw <- fromVWord "arithRight" r
                  return $ VWord (op w lw rw)
            | otherwise -> VSeq w (isTBit a) <$> (join (zipSeqMap (loop a) <$> (fromSeq l) <*> (fromSeq r)))
      -- streams
      Inf -> VStream <$> (join (zipSeqMap (loop a) <$> (fromSeq l) <*> (fromSeq r)))

    -- functions
    | Just (_,ety) <- isTFun ty =
      return $ lam $ \ x -> loop' ety (fromVFun l x) (fromVFun r x)

    -- tuples
    | Just (_,tys) <- isTTuple ty =
      let ls = fromVTuple l
          rs = fromVTuple r
       in return $ VTuple (zipWith3 loop' tys ls rs)

    -- records
    | Just fs <- isTRec ty =
      return $ VRecord [ (f, loop' fty (lookupRecord f l) (lookupRecord f r))
                       | (f,fty) <- fs ]

    | otherwise = do
          ldoc <- ppValue defaultPPOpts l
          rdoc <- ppValue defaultPPOpts r
          evalPanic "arithBinop" ["Invalid arguments", show ty
                                 , show ldoc, show rdoc]


arithUnary :: (Integer -> Integer) -> Unary
arithUnary op = loop
  where
  loop' :: TValue -> Eval Value -> Eval Value
  loop' ty x = loop ty =<< x

  loop :: TValue -> Value -> Eval Value
  loop ty x

    | Just (len,a) <- isTSeq ty = case numTValue len of

      -- words and finite sequences
      Nat w | isTBit a -> do
                   BV _ wx <- fromVWord "arithUnary" x
                   return $ VWord $ mkBv w $ op wx
            | otherwise -> VSeq w (isTBit a) <$> (mapSeqMap (loop a) =<< fromSeq x)

      Inf -> VStream <$> (mapSeqMap (loop a) =<< fromSeq x)

    -- functions
    | Just (_,ety) <- isTFun ty =
      return $ lam $ \ y -> loop' ety (fromVFun x y)

    -- tuples
    | Just (_,tys) <- isTTuple ty =
      let as = fromVTuple x
       in return $ VTuple (zipWith loop' tys as)

    -- records
    | Just fs <- isTRec ty =
      return $ VRecord [ (f, loop' fty (lookupRecord f x)) | (f,fty) <- fs ]

    | otherwise = evalPanic "arithUnary" ["Invalid arguments"]

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
lexCompare nm ty l r

  | isTBit ty =
    return $ compare (fromVBit l) (fromVBit r)

  | Just (_,b) <- isTSeq ty, isTBit b = do
    --ldoc <- ppValue defaultPPOpts l
    --io $ putStrLn $ unwords ["lexCompare left", nm, show l]
    compare <$> (fromWord "compareLeft" l) <*> (fromWord "compareRight" r)

  | Just (len,e) <- isTSeq ty = case numTValue len of
      Nat w -> join (zipLexCompare nm (repeat e) <$>
                    (enumerateSeqMap w <$> fromSeq l) <*>
                    (enumerateSeqMap w <$> fromSeq r))
      Inf   -> join (zipLexCompare nm (repeat e) <$>
                    (streamSeqMap <$> fromSeq l) <*>
                    (streamSeqMap <$> fromSeq r))

  -- tuples
  | Just (_,etys) <- isTTuple ty =
    zipLexCompare nm etys (fromVTuple l) (fromVTuple r)

  -- records
  | Just fields <- isTRec ty =
    let tys    = map snd (sortBy (comparing fst) fields)
        ls     = map snd (sortBy (comparing fst) (fromVRecord l))
        rs     = map snd (sortBy (comparing fst) (fromVRecord r))
     in zipLexCompare nm tys ls rs

  | otherwise = evalPanic "lexCompare" ["invalid type"]


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
cmpOrder :: String -> (Ordering -> Bool) -> Binary Bool BV
cmpOrder nm op ty l r = VBit . op <$> lexCompare nm ty l r

withOrder :: String -> (Ordering -> TValue -> Value -> Value -> Value) -> Binary Bool BV
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

zeroV :: TValue -> Value
zeroV ty

  -- bits
  | isTBit ty =
    VBit False

  -- sequences
  | Just (n,ety) <- isTSeq ty =
    case numTValue n of
      Nat w | isTBit ety -> word w 0
            | otherwise  -> mkSeq n ety (SeqMap $ \_ -> ready $ zeroV ety)
      Inf                -> mkSeq n ety (SeqMap $ \_ -> ready $ zeroV ety)

  -- functions
  | Just (_,bty) <- isTFun ty =
    lam (\ _ -> ready (zeroV bty))

  -- tuples
  | Just (_,tys) <- isTTuple ty =
    VTuple (map (ready . zeroV) tys)

  -- records
  | Just fields <- isTRec ty =
    VRecord [ (f,ready $ zeroV fty) | (f,fty) <- fields ]

  | otherwise = evalPanic "zeroV" ["invalid type for zero"]


joinWord :: BV -> BV -> BV
joinWord (BV i x) (BV j y) =
  BV (i + j) (shiftL x (fromInteger j) + y)

joinWords :: Integer -> Integer -> SeqValMap -> Eval Value -> Eval Value
joinWords nParts nEach xs fallback =
  loop (mkBv 0 0) (enumerateSeqMap nParts xs)

 where
 loop :: BV -> [Eval Value] -> Eval Value
 loop !bv [] = return $ VWord bv
 loop !bv (Ready (VWord w) : ws) = loop (joinWord bv w) ws

 -- loop !bv (w : ws) = w >>= \case
 --       VWord w' -> loop (joinWord bv w') ws
 --       _        -> fallback

 loop _   _ = fallback

 -- loop !bv (w:ws) = do
 --     w' <- fromVWord "joinWords" =<< w
 --     loop (joinWord bv w') ws


joinSeq :: TValue -> TValue -> TValue -> SeqValMap -> Eval Value
joinSeq parts each a xs
  | Nat nEach <- numTValue each
  = return $ mkSeq $ (SeqMap $ \i -> do
      let (q,r) = divMod i nEach
      ys <- fromSeq =<< lookupSeqMap xs q
      lookupSeqMap ys r)

  where
  len = numTValue parts `nMul` numTValue each
  mkSeq = case len of
            Inf    -> VStream
            Nat n  -> VSeq n (isTBit a)

-- | Join a sequence of sequences into a single sequence.
joinV :: TValue -> TValue -> TValue -> Value -> Eval Value
joinV parts each a val
  -- Try to join a sequence of words, if we can determine that
  -- each element is actually a word.  Fall back on sequence
  -- join otherwise.
  | Nat nParts  <- numTValue parts
  , Nat nEach   <- numTValue each
  , isTBit a
  = do xs <- fromSeq val
       joinWords nParts nEach xs (joinSeq parts each a xs)

joinV parts each a val =
       joinSeq parts each a =<< fromSeq val


splitAtV :: TValue -> TValue -> TValue -> Value -> Eval Value
splitAtV front back a val =
  case numTValue back of

    -- Remember that words are big-endian in cryptol, so the first component
    -- needs to be shifted, and the second component just needs to be masked.
    Nat rightWidth | aBit, VWord (BV _ i) <- val -> do
          return $ VTuple
                   [ ready $ VWord (BV leftWidth (i `shiftR` fromInteger rightWidth))
                   , ready $ VWord (mkBv rightWidth i) ]

    _ -> do
       seq <- delay Nothing (fromSeq val)
       ls  <- delay Nothing (fst . splitSeqMap leftWidth <$> seq)
       rs  <- delay Nothing (snd . splitSeqMap leftWidth <$> seq)
       return $ VTuple [ VSeq leftWidth aBit <$> ls
                       , mkSeq back a <$> rs
                       ]

  where
  aBit = isTBit a

  leftWidth = case numTValue front of
    Nat n -> n
    _     -> evalPanic "splitAtV" ["invalid `front` len"]


-- | Split implementation.
ecSplitV :: Value
ecSplitV =
  tlam $ \ parts ->
  tlam $ \ each  ->
  tlam $ \ a     ->
  lam  $ \ val ->
    case (numTValue parts, numTValue each) of
       (Nat p, Nat e) | isTBit a -> do
          val' <- delay Nothing (fromVWord "split" =<< val)
          return $ VSeq p False $ SeqMap $ \i -> do
            BV _ x <- val'
            return $ VWord $ mkBv e $ (x `shiftR` (fromInteger ((p-i-1)*e)))
       (Nat p, Nat e) -> do
          val' <- delay Nothing (fromSeq =<< val)
          return $ VSeq p False $ SeqMap $ \i ->
            return $ VSeq e (isTBit a) $ SeqMap $ \j -> do
              xs <- val'
              lookupSeqMap xs (e * i + j)
       (Inf  , Nat e) -> do
          val' <- delay Nothing (fromSeq =<< val)
          return $ VStream $ SeqMap $ \i ->
            return $ VSeq e (isTBit a) $ SeqMap $ \j -> do
              xs <- val'
              lookupSeqMap xs (e * i + j)
       _              -> evalPanic "splitV" ["invalid type arguments to split"]

-- | Split into infinitely many chunks
infChunksOf :: Integer -> [a] -> [[a]]
infChunksOf each xs = let (as,bs) = genericSplitAt each xs
                      in as : infChunksOf each bs

-- | Split into finitely many chunks
finChunksOf :: Integer -> Integer -> [a] -> [[a]]
finChunksOf 0 _ _ = []
finChunksOf parts each xs = let (as,bs) = genericSplitAt each xs
                            in as : finChunksOf (parts - 1) each bs


reverseV :: Value -> Eval Value
reverseV (VSeq n isWord xs) =
  return $ VSeq n isWord $ reverseSeqMap n xs
reverseV (VWord w) = return (VWord revword)
 where
 revword = do
   let bs = unpackWord w :: [Bool]
    in packWord $ reverse bs
reverseV _ =
  evalPanic "reverseV" ["Not a finite sequence"]


transposeV :: TValue -> TValue -> TValue -> Value -> Eval Value
transposeV a b c xs = do
  let bseq = 
        case numTValue b of
          Nat nb -> VSeq nb (isTBit b)
          Inf    -> VStream
  let aseq =
        case numTValue a of
          Nat na -> VSeq na (isTBit a)
          Inf    -> VStream
  return $ bseq $ SeqMap $ \bi ->
    return $ aseq $ SeqMap $ \ai -> do
      ys  <- flip lookupSeqMap ai =<< fromSeq xs
      z   <- flip lookupSeqMap bi =<< fromSeq ys  
      return z

ccatV :: TValue -> TValue -> TValue -> Eval Value -> Eval Value -> Eval Value
ccatV _front _back (isTBit -> True) (Ready (VWord x)) (Ready (VWord y)) =
  return $ VWord $ joinWord x y

-- ccatV _front (numTValue -> Nat _nBack) (isTBit -> True) x y = do
--   xw <- fromVWord "ccatV" =<< x
--   yw <- fromVWord "ccatV" =<< y
--   return $ VWord $ joinWord xw yw

ccatV front back elty l r = do
  l' <- delay Nothing (fromSeq =<< l)
  r' <- delay Nothing (fromSeq =<< r)
  let Nat n = numTValue front
  mkSeq (evalTF TCAdd [front,back]) elty <$> return (SeqMap $ \i ->
     if i < n then do
       ls <- l'
       lookupSeqMap ls i
     else do
       rs <- r'
       lookupSeqMap rs (i-n))

-- | Merge two values given a binop.  This is used for and, or and xor.
logicBinary :: (forall a. Bits a => a -> a -> a) -> Binary Bool BV
logicBinary op = loop
  where
  loop' :: TValue -> Eval Value -> Eval Value -> Eval Value
  loop' ty l r = join (loop ty <$> l <*> r)

  loop :: TValue -> Value -> Value -> Eval Value
  loop ty l r
    | isTBit ty = return $ VBit (op (fromVBit l) (fromVBit r))
    | Just (len,aty) <- isTSeq ty =

      case numTValue len of

         -- words or finite sequences
         Nat w | isTBit aty, VWord (BV _ lw) <- l, VWord (BV _ rw) <- r
              -> return $ VWord $ (BV w (op lw rw))
                   -- We assume that bitwise ops do not need re-masking

         -- Nat w | isTBit aty -> do
         --          BV _ lw <- fromVWord "logicLeft" l
         --          BV _ rw <- fromVWord "logicRight" r
         --          return $ VWord $ mkBv w (op lw rw)

               | otherwise -> VSeq w (isTBit aty) <$>
                                 (join (zipSeqMap (loop aty) <$>
                                          (fromSeq l) <*> (fromSeq r)))

         -- streams
         Inf -> VStream <$> (join (zipSeqMap (loop aty) <$> (fromSeq l) <*> (fromSeq r)))

    | Just (_,etys) <- isTTuple ty = do
        let ls = fromVTuple l
        let rs = fromVTuple r
        return $ VTuple $ (zipWith3 loop' etys ls rs)

    | Just (_,bty) <- isTFun ty =
        return $ lam $ \ a -> loop' bty (fromVFun l a) (fromVFun r a)

    | Just fields <- isTRec ty =
        return $ VRecord [ (f,loop' fty a b)
                         | (f,fty) <- fields 
                         , let a = lookupRecord f l
                               b = lookupRecord f r 
                         ]

    | otherwise = evalPanic "logicBinary" ["invalid logic type"]

logicUnary :: (forall a. Bits a => a -> a) -> Unary
logicUnary op = loop
  where
  loop' :: TValue -> Eval Value -> Eval Value
  loop' ty val = loop ty =<< val

  loop :: TValue -> Value -> Eval Value
  loop ty val
    | isTBit ty = return . VBit . op $ fromVBit val

    | Just (len,ety) <- isTSeq ty =

      case numTValue len of

         -- words or finite sequences
         Nat w | isTBit ety, VWord (BV _ v) <- val
              -> return $ VWord (mkBv w $ op v)

         -- Nat w | isTBit ety
         --      -> do v <- fromWord "logicUnary" val
         --            return $ VWord (mkBv w $ op v)

               | otherwise
              -> VSeq w (isTBit ety) <$> (mapSeqMap (loop ety) =<< fromSeq val)

         -- streams
         Inf -> VStream <$> (mapSeqMap (loop ety) =<< fromSeq val)

    | Just (_,etys) <- isTTuple ty =
      let as = fromVTuple val
       in return $ VTuple (zipWith loop' etys as)

    | Just (_,bty) <- isTFun ty =
      return $ lam $ \ a -> loop' bty (fromVFun val a)

    | Just fields <- isTRec ty =
      return $ VRecord [ (f,loop' fty a) | (f,fty) <- fields, let a = lookupRecord f val ]

    | otherwise = evalPanic "logicUnary" ["invalid logic type"]


logicShift :: (Integer -> Integer -> Integer -> Integer)
              -- ^ The function may assume its arguments are masked.
              -- It is responsible for masking its result if needed.
           -> (TValue -> TValue -> SeqValMap -> Integer -> SeqValMap)
           -> Value
logicShift opW opS
  = tlam $ \ a ->
    tlam $ \ _ ->
    tlam $ \ c ->
     lam  $ \ l -> return $
     lam  $ \ r -> do
        case l of
          Ready (VWord (BV w x)) -> do
            BV _ i <- fromVWord "logicShift amount" =<< r
            return $ VWord $ BV w $ opW w x i
          _ -> do
            BV _ i <- fromVWord "logicShift amount" =<< r
            mkSeq a c <$> (opS a c <$> (fromSeq =<< l) <*> return i)

-- Left shift for words.
shiftLW :: Integer -> Integer -> Integer -> Integer
shiftLW w ival by
  | by >= w   = 0
  | otherwise = mask w (shiftL ival (fromInteger by))

shiftLS :: TValue -> TValue -> SeqValMap -> Integer -> SeqValMap
shiftLS w ety vs by = SeqMap $ \i ->
  case numTValue w of
    Nat len
      | i+by < len -> lookupSeqMap vs (i+by)
      | i    < len -> return $ zeroV ety
      | otherwise  -> evalPanic "shiftLS" ["Index out of bounds"]
    Inf            -> lookupSeqMap vs (i+by)

shiftRW :: Integer -> Integer -> Integer -> Integer
shiftRW w i by
  | by >= w   = 0
  | otherwise = shiftR i (fromInteger by)

shiftRS :: TValue -> TValue -> SeqValMap -> Integer -> SeqValMap
shiftRS w ety vs by = SeqMap $ \i ->
  case numTValue w of
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

rotateLS :: TValue -> TValue -> SeqValMap -> Integer -> SeqValMap
rotateLS w _ vs by = SeqMap $ \i ->
  case numTValue w of
    Nat len -> lookupSeqMap vs ((by + i) `mod` len)
    _ -> panic "Cryptol.Eval.Prim.rotateLS" [ "unexpected infinite sequence" ]

-- XXX integer doesn't implement rotateR, as there's no bit bound
rotateRW :: Integer -> Integer -> Integer -> Integer
rotateRW 0 i _  = i
rotateRW w i by = mask w $ (i `shiftR` b) .|. (i `shiftL` (fromInteger w - b))
  where b = fromInteger (by `mod` w)

rotateRS :: TValue -> TValue -> SeqValMap -> Integer -> SeqValMap
rotateRS w _ vs by = SeqMap $ \i ->
  case numTValue w of
    Nat len -> lookupSeqMap vs ((len - by + i) `mod` len)
    _ -> panic "Cryptol.Eval.Prim.rotateRS" [ "unexpected infinite sequence" ]


-- Sequence Primitives ---------------------------------------------------------

-- | Indexing operations that return one element.
indexPrimOne :: (Maybe Integer -> SeqValMap -> Integer -> Eval Value) -> Value
indexPrimOne op =
  tlam $ \ n  ->
  tlam $ \ _a ->
  tlam $ \ _i ->
   lam $ \ l  -> return $
   lam $ \ r  -> do
      vs <- fromSeq =<< l
      ix <- fromWord "index one" =<< r
      op (fromNat (numTValue n)) vs ix

indexFront :: Maybe Integer -> SeqValMap -> Integer -> Eval Value
indexFront mblen vs ix =
  case mblen of
    Just len | len <= ix -> invalidIndex ix
    _                    -> lookupSeqMap vs ix

indexBack :: Maybe Integer -> SeqValMap -> Integer -> Eval Value
indexBack mblen vs ix =
  case mblen of
    Just len | len > ix  -> lookupSeqMap vs (len - ix - 1)
             | otherwise -> invalidIndex ix
    Nothing              -> evalPanic "indexBack"
                            ["unexpected infinite sequence"]

-- | Indexing operations that return many elements.
indexPrimMany :: (Maybe Integer -> SeqValMap -> Integer -> Eval Value) -> Value
indexPrimMany op =
  tlam $ \ n  ->
  tlam $ \ a  ->
  tlam $ \ m  ->
  tlam $ \ _i ->
   lam $ \ l  -> return $
   lam $ \ r  -> do
     vs  <- fromSeq =<< l
     ixs <- fromSeq =<< r
     mkSeq m a <$> memoMap (SeqMap $ \i -> do
       i' <- fromWord "index many" =<< lookupSeqMap ixs i
       op (fromNat (numTValue n)) vs i')

-- @[ 0, 1 .. ]@
fromThenV :: Value
fromThenV  =
  tlamN $ \ first ->
  tlamN $ \ next  ->
  tlamN $ \ bits  ->
  tlamN $ \ len   ->
    case (first, next, len, bits) of
      (_         , _        , _       , Nat bits')
        | bits' >= Arch.maxBigIntWidth -> wordTooWide bits'
      (Nat first', Nat next', Nat len', Nat bits') ->
        let diff = next' - first'
         in VSeq len' False $ SeqMap $ \i ->
                ready $ VWord $ BV bits' $ (first' + i*diff)
      _ -> evalPanic "fromThenV" ["invalid arguments"]

-- @[ 0 .. 10 ]@
fromToV :: Value
fromToV  =
  tlamN $ \ first ->
  tlamN $ \ lst   ->
  tlamN $ \ bits  ->
    case (first, lst, bits) of
      (_         , _       , Nat bits')
        | bits' >= Arch.maxBigIntWidth -> wordTooWide bits'
      (Nat first', Nat lst', Nat bits') ->
        let len = 1 + (lst' - first')
         in VSeq len False $ SeqMap $ \i ->
               ready $ VWord $ BV bits' (first' + i)
      _ -> evalPanic "fromToV" ["invalid arguments"]

-- @[ 0, 1 .. 10 ]@
fromThenToV :: Value
fromThenToV  =
  tlamN $ \ first ->
  tlamN $ \ next  ->
  tlamN $ \ lst   ->
  tlamN $ \ bits  ->
  tlamN $ \ len   ->
    case (first, next, lst, len, bits) of
      (_         , _        , _       , _       , Nat bits')
        | bits' >= Arch.maxBigIntWidth -> wordTooWide bits'
      (Nat first', Nat next', Nat lst', Nat len', Nat bits') ->
        let diff = next' - first'
         in VSeq len' False $ SeqMap $ \i ->
               ready $ VWord $ BV bits' $ (first' + i*diff)
      _ -> evalPanic "fromThenToV" ["invalid arguments"]

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

tlamN :: (Nat' -> GenValue b w) -> GenValue b w
tlamN f = VPoly (\x -> ready $ f (numTValue x))
