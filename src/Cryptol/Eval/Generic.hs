-- |
-- Module      :  Cryptol.Eval.Concrete
-- Copyright   :  (c) 2013-2020 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE Safe #-}
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
module Cryptol.Eval.Generic where

import Control.Monad (join)

import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Solver.InfNat (Nat'(..),fromNat,nMul,genLog)
import Cryptol.Eval.Monad
import Cryptol.Eval.Type
import Cryptol.Eval.Value
import Cryptol.Utils.Panic (panic)

import qualified Data.Sequence as Seq

import qualified Data.Map.Strict as Map


lg2 :: Integer -> Integer
lg2 i = case genLog i 2 of
  Just (i',isExact) | isExact   -> i'
                    | otherwise -> i' + 1
  Nothing                       -> 0



-- | Make a numeric literal value at the given type.
mkLit :: Backend sym => sym -> TValue -> Integer -> Eval (GenValue sym)
mkLit sym ty i =
  case ty of
    TVInteger                    -> VInteger <$> io (integerLit sym i)
    TVIntMod _                   -> VInteger <$> io (integerLit sym i)
    TVSeq w TVBit                -> pure $ word sym w i
    _                            -> evalPanic "Cryptol.Eval.Prim.evalConst"
                                    [ "Invalid type for number" ]

-- | Make a numeric constant.
ecNumberV :: Backend sym => sym -> GenValue sym
ecNumberV sym =
  nlam $ \valT ->
  VPoly $ \ty ->
  case valT of
    Nat v -> mkLit sym ty v
    _ -> evalPanic "Cryptol.Eval.Prim.evalConst"
             ["Unexpected Inf in constant."
             , show valT
             , show ty
             ]

-- | Convert a word to a non-negative integer.
ecToIntegerV :: Backend sym => sym -> GenValue sym
ecToIntegerV sym =
  nlam $ \ _ ->
  wlam sym $ \ w -> VInteger <$> io (wordToInt sym w)

-- | Convert an unbounded integer to a packed bitvector.
ecFromIntegerV :: Backend sym => sym -> (Integer -> SInteger sym -> SInteger sym) -> GenValue sym
ecFromIntegerV sym opz =
  tlam $ \ a ->
  lam  $ \ v ->
  do i <- fromVInteger <$> v
     arithNullary (\x -> io (wordFromInt sym x i)) (pure i) (\x -> pure (opz x i)) a


-- Operation Lifting -----------------------------------------------------------


type Binary sym = TValue -> GenValue sym -> GenValue sym -> Eval (GenValue sym)

binary :: Binary sym -> GenValue sym
binary f = tlam $ \ ty ->
            lam $ \ a  -> return $
            lam $ \ b  -> do
               --io $ putStrLn "Entering a binary function"
               join (f ty <$> a <*> b)

type Unary sym = TValue -> GenValue sym -> Eval (GenValue sym)

unary :: Unary sym -> GenValue sym
unary f = tlam $ \ ty ->
           lam $ \ a  -> f ty =<< a


type BinArith sym = Integer -> SWord sym -> SWord sym -> Eval (SWord sym)

arithBinary :: forall sym.
  Backend sym =>
  sym ->
  BinArith sym ->
  (SInteger sym -> SInteger sym -> Eval (SInteger sym)) ->
  (Integer -> SInteger sym -> SInteger sym -> Eval (SInteger sym)) ->
  Binary sym
arithBinary sym opw opi opz = loop
  where
  loop' :: TValue
        -> Eval (GenValue sym)
        -> Eval (GenValue sym)
        -> Eval (GenValue sym)
  loop' ty l r = join (loop ty <$> l <*> r)

  loop :: TValue
       -> GenValue sym
       -> GenValue sym
       -> Eval (GenValue sym)
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
                  lw <- fromVWord sym "arithLeft" l
                  rw <- fromVWord sym "arithRight" r
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
         return $ VRecord (Map.fromList fs')

    TVAbstract {} ->
      evalPanic "arithBinary" ["Abstract type not in `Arith`"]

type UnaryArith sym = Integer -> SWord sym -> Eval (SWord sym)


arithUnary :: forall sym.
  Backend sym =>
  sym ->
  UnaryArith sym ->
  (SInteger sym -> Eval (SInteger sym)) ->
  (Integer -> SInteger sym -> Eval (SInteger sym)) ->
  Unary sym
arithUnary sym opw opi opz = loop
  where
  loop' :: TValue -> Eval (GenValue sym) -> Eval (GenValue sym)
  loop' ty v = loop ty =<< v

  loop :: TValue -> GenValue sym -> Eval (GenValue sym)
  loop ty v = case ty of

    TVBit ->
      evalPanic "arithUnary" ["Bit not in class Arith"]

    TVInteger ->
      VInteger <$> opi (fromVInteger v)

    TVIntMod n ->
      VInteger <$> opz n (fromVInteger v)

    TVSeq w a
      -- words and finite sequences
      | isTBit a -> do
              wx <- fromVWord sym "arithUnary" v
              return $ VWord w (WordVal <$> opw w wx)
      | otherwise -> VSeq w <$> (mapSeqMap (loop a) =<< fromSeq "arithUnary" v)

    TVStream a ->
      VStream <$> (mapSeqMap (loop a) =<< fromSeq "arithUnary" v)

    -- functions
    TVFun _ ety ->
      return $ lam $ \ y -> loop' ety (fromVFun v y)

    -- tuples
    TVTuple tys ->
      do as <- mapM (delay Nothing) (fromVTuple v)
         return $ VTuple (zipWith loop' tys as)

    -- records
    TVRec fs ->
      do fs' <- sequence
                 [ (f,) <$> delay Nothing (loop' fty (lookupRecord f v))
                 | (f,fty) <- fs
                 ]
         return $ VRecord (Map.fromList fs')

    TVAbstract {} -> evalPanic "arithUnary" ["Abstract type not in `Arith`"]

arithNullary :: forall sym.
  Backend sym =>
  (Integer -> Eval (SWord sym)) ->
  Eval (SInteger sym) ->
  (Integer -> Eval (SInteger sym)) ->
  TValue ->
  Eval (GenValue sym)
arithNullary opw opi opz = loop
  where
    loop :: TValue -> Eval (GenValue sym)
    loop ty =
      case ty of
        TVBit -> evalPanic "arithNullary" ["Bit not in class Arith"]

        TVInteger -> VInteger <$> opi

        TVIntMod n -> VInteger <$> opz n

        TVSeq w a
          -- words and finite sequences
          | isTBit a -> pure $ VWord w $ (WordVal <$> opw w)
          | otherwise ->
             do v <- delay Nothing (loop a)
                pure $ VSeq w $ IndexSeqMap $ const v

        TVStream a ->
             do v <- delay Nothing (loop a)
                pure $ VStream $ IndexSeqMap $ const v

        TVFun _ b ->
             do v <- delay Nothing (loop b)
                pure $ lam $ const $ v

        TVTuple tys ->
             do xs <- mapM (delay Nothing . loop) tys
                pure $ VTuple xs

        TVRec fs ->
             do xs <- sequence [ do v <- delay Nothing (loop a)
                                    return (f, v)
                               | (f,a) <- fs
                               ]
                pure $ VRecord $ Map.fromList xs

        TVAbstract {} ->
          evalPanic "arithNullary" ["Abstract type not in `Arith`"]


addV :: Backend sym => sym -> Binary sym
addV sym = arithBinary sym opw opi opz
  where
    opw _w x y = io $ wordPlus sym x y
    opi x y = io $ intPlus sym x y
    opz m x y = io $ intModPlus sym m x y

subV :: Backend sym => sym -> Binary sym
subV sym = arithBinary sym opw opi opz
  where
    opw _w x y = io $ wordMinus sym x y
    opi x y = io $ intMinus sym x y
    opz m x y = io $ intModMinus sym m x y

mulV :: Backend sym => sym -> Binary sym
mulV sym = arithBinary sym opw opi opz
  where
    opw _w x y = io $ wordMult sym x y
    opi x y = io $ intMult sym x y
    opz m x y = io $ intModMult sym m x y

intV :: Backend sym => sym -> SInteger sym -> TValue -> Eval (GenValue sym)
intV sym i = arithNullary (\w -> io (wordFromInt sym w i)) (pure i) (pure . const i)


-- Cmp -------------------------------------------------------------------------

cmpValue ::
  Backend sym =>
  sym ->
  (SBit sym -> SBit sym -> Eval a -> Eval a) ->
  (SWord sym -> SWord sym -> Eval a -> Eval a) ->
  (SInteger sym -> SInteger sym -> Eval a -> Eval a) ->
  (Integer -> SInteger sym -> SInteger sym -> Eval a -> Eval a) ->
  (TValue -> GenValue sym -> GenValue sym -> Eval a -> Eval a)
cmpValue sym fb fw fi fz = cmp
  where
    cmp ty v1 v2 k =
      case ty of
        TVBit         -> fb (fromVBit v1) (fromVBit v2) k
        TVInteger     -> fi (fromVInteger v1) (fromVInteger v2) k
        TVIntMod n    -> fz n (fromVInteger v1) (fromVInteger v2) k
        TVSeq n t
          | isTBit t  -> do w1 <- fromVWord sym "cmpValue" v1
                            w2 <- fromVWord sym "cmpValue" v2
                            fw w1 w2 k
          | otherwise -> cmpValues (repeat t)
                         (enumerateSeqMap n (fromVSeq v1))
                         (enumerateSeqMap n (fromVSeq v2)) k
        TVStream _    -> panic "Cryptol.Prims.Value.cmpValue"
                         [ "Infinite streams are not comparable" ]
        TVFun _ _     -> panic "Cryptol.Prims.Value.cmpValue"
                         [ "Functions are not comparable" ]
        TVTuple tys   -> cmpValues tys (fromVTuple v1) (fromVTuple v2) k
        TVRec fields  -> do let tys = Map.elems (Map.fromList fields)
                            cmpValues tys
                              (Map.elems (fromVRecord v1))
                              (Map.elems (fromVRecord v2)) k
        TVAbstract {} -> evalPanic "cmpValue"
                          [ "Abstract type not in `Cmp`" ]

    cmpValues (t : ts) (x1 : xs1) (x2 : xs2) k =
      do x1' <- x1
         x2' <- x2
         cmp t x1' x2' (cmpValues ts xs1 xs2 k)
    cmpValues _ _ _ k = k



-- Signed arithmetic -----------------------------------------------------------

-- | Lifted operation on finite bitsequences.  Used
--   for signed comparisons and arithemtic.
liftWord ::
  Backend sym =>
  sym ->
  (SWord sym -> SWord sym -> Eval (GenValue sym)) ->
  GenValue sym
liftWord sym op =
  nlam $ \_n ->
  wlam sym $ \w1 -> return $
  wlam sym $ \w2 -> op w1 w2


-- Logic -----------------------------------------------------------------------

zeroV :: forall sym.
  Backend sym =>
  sym ->
  TValue ->
  Eval (GenValue sym)
zeroV sym ty = case ty of

  -- bits
  TVBit ->
    VBit <$> io (bitLit sym False)

  -- integers
  TVInteger ->
    VInteger <$> io (integerLit sym 0)

  -- integers mod n
  TVIntMod _ ->
    VInteger <$> io (integerLit sym 0)

  -- sequences
  TVSeq w ety
      | isTBit ety -> pure $ word sym w 0
      | otherwise  ->
           do z <- delay Nothing (zeroV sym ety)
              pure $ VSeq w (IndexSeqMap $ const z)

  TVStream ety ->
     do z <- delay Nothing (zeroV sym ety)
        pure $ VStream (IndexSeqMap $ const z)

  -- functions
  TVFun _ bty ->
     do z <- delay Nothing (zeroV sym bty)
        pure $ lam (const z)

  -- tuples
  TVTuple tys ->
      do xs <- mapM (delay Nothing . zeroV sym) tys
         pure $ VTuple xs

  -- records
  TVRec fields ->
      do xs <- sequence [ do z <- delay Nothing (zeroV sym fty)
                             pure (f, z)
                        | (f,fty) <- fields
                        ]
         pure $ VRecord (Map.fromList xs)

  TVAbstract {} -> evalPanic "zeroV" [ "Abstract type not in `Zero`" ]

--  | otherwise = evalPanic "zeroV" ["invalid type for zero"]


joinWordVal :: Backend sym => sym -> WordValue sym -> WordValue sym -> Eval (WordValue sym)
joinWordVal sym (WordVal w1) (WordVal w2)
  | wordLen sym w1 + wordLen sym w2 < largeBitSize
  = WordVal <$> io (joinWord sym w1 w2)
joinWordVal sym w1 w2
  = pure $ LargeBitsVal (n1+n2) (concatSeqMap n1 (asBitsMap sym w1) (asBitsMap sym w2))
 where n1 = wordValueSize sym w1
       n2 = wordValueSize sym w2


joinWords :: forall sym.
  Backend sym =>
  sym ->
  Integer ->
  Integer ->
  SeqMap sym ->
  Eval (GenValue sym)
joinWords sym nParts nEach xs =
  loop (WordVal <$> io (wordLit sym 0 0)) (enumerateSeqMap nParts xs)

 where
 loop :: Eval (WordValue sym) -> [Eval (GenValue sym)] -> Eval (GenValue sym)
 loop !wv [] =
    VWord (nParts * nEach) <$> delay Nothing wv
 loop !wv (w : ws) =
    w >>= \case
      VWord _ w' ->
        loop (join (joinWordVal sym <$> wv <*> w')) ws
      _ -> evalPanic "joinWords: expected word value" []


joinSeq ::
  Backend sym =>
  sym ->
  Nat' ->
  Integer ->
  TValue ->
  SeqMap sym ->
  Eval (GenValue sym)

-- Special case for 0 length inner sequences.
joinSeq sym _parts 0 a _xs
  = zeroV sym (TVSeq 0 a)

-- finite sequence of words
joinSeq sym (Nat parts) each TVBit xs
  | parts * each < largeBitSize
  = joinWords sym parts each xs
  | otherwise
  = do let zs = IndexSeqMap $ \i ->
                  do let (q,r) = divMod i each
                     ys <- fromWordVal "join seq" =<< lookupSeqMap xs q
                     VBit <$> indexWordValue sym ys (fromInteger r)
       return $ VWord (parts * each) $ ready $ LargeBitsVal (parts * each) zs

-- infinite sequence of words
joinSeq sym Inf each TVBit xs
  = return $ VStream $ IndexSeqMap $ \i ->
      do let (q,r) = divMod i each
         ys <- fromWordVal "join seq" =<< lookupSeqMap xs q
         VBit <$> indexWordValue sym ys (fromInteger r)

-- finite or infinite sequence of non-words
joinSeq _sym parts each _a xs
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
joinV ::
  Backend sym =>
  sym ->
  Nat' ->
  Integer ->
  TValue ->
  GenValue sym ->
  Eval (GenValue sym)
joinV sym parts each a val = joinSeq sym parts each a =<< fromSeq "joinV" val


splitWordVal ::
  Backend sym =>
  sym ->
  Integer ->
  Integer ->
  WordValue sym ->
  Eval (WordValue sym, WordValue sym)
splitWordVal sym leftWidth rightWidth (WordVal w) =
  do (lw, rw) <- io (splitWord sym leftWidth rightWidth w)
     pure (WordVal lw, WordVal rw)
splitWordVal _ leftWidth rightWidth (LargeBitsVal _n xs) =
  let (lxs, rxs) = splitSeqMap leftWidth xs
   in pure (LargeBitsVal leftWidth lxs, LargeBitsVal rightWidth rxs)

splitAtV ::
  Backend sym =>
  sym ->
  Nat' ->
  Nat' ->
  TValue ->
  GenValue sym ->
  Eval (GenValue sym)
splitAtV sym front back a val =
  case back of

    Nat rightWidth | aBit -> do
          ws <- delay Nothing (splitWordVal sym leftWidth rightWidth =<< fromWordVal "splitAtV" val)
          return $ VTuple
                   [ VWord leftWidth  . ready . fst <$> ws
                   , VWord rightWidth . ready . snd <$> ws
                   ]

    Inf | aBit -> do
       vs <- delay Nothing (fromSeq "splitAtV" val)
       ls <- delay Nothing (fst . splitSeqMap leftWidth <$> vs)
       rs <- delay Nothing (snd . splitSeqMap leftWidth <$> vs)
       return $ VTuple [ return $ VWord leftWidth (LargeBitsVal leftWidth <$> ls)
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
extractWordVal ::
  Backend sym =>
  sym ->
  Integer ->
  Integer ->
  WordValue sym ->
  Eval (WordValue sym)
extractWordVal sym len start (WordVal w) =
   WordVal <$> io (extractWord sym len start w)
extractWordVal _ len start (LargeBitsVal n xs) =
   let xs' = dropSeqMap (n - start - len) xs
    in pure $ LargeBitsVal len xs'

-- | Split implementation.
ecSplitV :: Backend sym => sym -> GenValue sym
ecSplitV sym =
  nlam $ \ parts ->
  nlam $ \ each  ->
  tlam $ \ a     ->
  lam  $ \ val ->
    case (parts, each) of
       (Nat p, Nat e) | isTBit a -> do
          ~(VWord _ val') <- val
          return $ VSeq p $ IndexSeqMap $ \i ->
            pure $ VWord e (extractWordVal sym e ((p-i-1)*e) =<< val')
       (Inf, Nat e) | isTBit a -> do
          val' <- delay Nothing (fromSeq "ecSplitV" =<< val)
          return $ VStream $ IndexSeqMap $ \i ->
            return $ VWord e $ return $ LargeBitsVal e $ IndexSeqMap $ \j ->
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


reverseV :: forall sym.
  Backend sym =>
  sym ->
  GenValue sym ->
  Eval (GenValue sym)
reverseV _ (VSeq n xs) =
  return $ VSeq n $ reverseSeqMap n xs
reverseV sym (VWord n x) = return (VWord n (revword <$> x))
 where
 revword wv =
   let m = wordValueSize sym wv in
   LargeBitsVal m $ reverseSeqMap m $ asBitsMap sym wv
reverseV _ _ =
  evalPanic "reverseV" ["Not a finite sequence"]



transposeV ::
  Backend sym =>
  sym ->
  Nat' ->
  Nat' ->
  TValue ->
  GenValue sym ->
  Eval (GenValue sym)
transposeV sym a b c xs
  | isTBit c, Nat na <- a = -- Fin a => [a][b]Bit -> [b][a]Bit
      return $ bseq $ IndexSeqMap $ \bi ->
        return $ VWord na $ return $ LargeBitsVal na $ IndexSeqMap $ \ai ->
         do ys <- flip lookupSeqMap (toInteger ai) =<< fromSeq "transposeV" xs
            case ys of
              VStream ys' -> lookupSeqMap ys' bi
              VWord _ wv  -> VBit <$> (flip (indexWordValue sym) bi =<< wv)
              _ -> evalPanic "transpose" ["expected sequence of bits"]

  | isTBit c, Inf <- a = -- [inf][b]Bit -> [b][inf]Bit
      return $ bseq $ IndexSeqMap $ \bi ->
        return $ VStream $ IndexSeqMap $ \ai ->
         do ys <- flip lookupSeqMap ai =<< fromSeq "transposeV" xs
            case ys of
              VStream ys' -> lookupSeqMap ys' bi
              VWord _ wv  -> VBit <$> (flip (indexWordValue sym) bi =<< wv)
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




ccatV ::
  Backend sym =>
  sym ->
  Nat' ->
  Nat' ->
  TValue ->
  (GenValue sym) ->
  (GenValue sym) ->
  Eval (GenValue sym)

ccatV sym _front _back _elty (VWord m l) (VWord n r) =
  return $ VWord (m+n) (join (joinWordVal sym <$> l <*> r))

ccatV sym _front _back _elty (VWord m l) (VStream r) = do
  l' <- delay Nothing l
  return $ VStream $ IndexSeqMap $ \i ->
    if i < m then
      VBit <$> (flip (indexWordValue sym) i =<< l')
    else
      lookupSeqMap r (i-m)

ccatV _sym front back elty l r = do
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

wordValLogicOp ::
  Backend sym =>
  sym ->
  (SBit sym -> SBit sym -> Eval (SBit sym)) ->
  (SWord sym -> SWord sym -> Eval (SWord sym)) ->
  WordValue sym ->
  WordValue sym ->
  Eval (WordValue sym)
wordValLogicOp _sym _ wop (WordVal w1) (WordVal w2) = WordVal <$> wop w1 w2

wordValLogicOp sym bop _ w1 w2 = LargeBitsVal (wordValueSize sym w1) <$> zs
     where zs = memoMap $ IndexSeqMap $ \i -> join (op <$> (lookupSeqMap xs i) <*> (lookupSeqMap ys i))
           xs = asBitsMap sym w1
           ys = asBitsMap sym w2
           op x y = VBit <$> (bop (fromVBit x) (fromVBit y))

-- | Merge two values given a binop.  This is used for and, or and xor.
logicBinary :: forall sym.
  Backend sym =>
  sym ->
  (SBit sym -> SBit sym -> Eval (SBit sym)) ->
  (SWord sym -> SWord sym -> Eval (SWord sym)) ->
  Binary sym
logicBinary sym opb opw = loop
  where
  loop' :: TValue
        -> Eval (GenValue sym)
        -> Eval (GenValue sym)
        -> Eval (GenValue sym)
  loop' ty l r = join (loop ty <$> l <*> r)

  loop :: TValue
        -> GenValue sym
        -> GenValue sym
        -> Eval (GenValue sym)

  loop ty l r = case ty of
    TVBit -> VBit <$> (opb (fromVBit l) (fromVBit r))
    TVInteger -> evalPanic "logicBinary" ["Integer not in class Logic"]
    TVIntMod _ -> evalPanic "logicBinary" ["Z not in class Logic"]
    TVSeq w aty
         -- words
         | isTBit aty
              -> do v <- delay Nothing $ join
                            (wordValLogicOp sym opb opw <$>
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
           return $ VRecord $ Map.fromList fs

    TVAbstract {} -> evalPanic "logicBinary"
                        [ "Abstract type not in `Logic`" ]


wordValUnaryOp ::
  Backend sym =>
  (SBit sym -> SBit sym) ->
  (SWord sym -> SWord sym) ->
  WordValue sym ->
  Eval (WordValue sym)
wordValUnaryOp _ wop (WordVal w)  = return $ WordVal (wop w)
wordValUnaryOp bop _ (LargeBitsVal n xs) = LargeBitsVal n <$> mapSeqMap f xs
  where f x = VBit . bop <$> fromBit x

logicUnary :: forall sym.
  Backend sym =>
  (SBit sym -> SBit sym) ->
  (SWord sym -> SWord sym) ->
  Unary sym
logicUnary opb opw = loop
  where
  loop' :: TValue -> Eval (GenValue sym) -> Eval (GenValue sym)
  loop' ty val = loop ty =<< val

  loop :: TValue -> GenValue sym -> Eval (GenValue sym)
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
         return $ VRecord $ Map.fromList fs

    TVAbstract {} -> evalPanic "logicUnary" [ "Abstract type not in `Logic`" ]

-- | Indexing operations.
indexPrim ::
  Backend sym =>
  sym ->
  (Maybe Integer -> TValue -> SeqMap sym -> Seq.Seq (SBit sym) -> Eval (GenValue sym)) ->
  (Maybe Integer -> TValue -> SeqMap sym -> SWord sym -> Eval (GenValue sym)) ->
  GenValue sym
indexPrim sym bits_op word_op =
  nlam $ \ n  ->
  tlam $ \ a ->
  nlam $ \ _i ->
   lam $ \ l  -> return $
   lam $ \ r  -> do
      vs <- l >>= \case
               VWord _ w  -> w >>= \w' -> return $ IndexSeqMap (\i -> VBit <$> indexWordValue sym w' i)
               VSeq _ vs  -> return vs
               VStream vs -> return vs
               _ -> evalPanic "Expected sequence value" ["indexPrim"]
      r >>= \case
         VWord _ w -> w >>= \case
           WordVal w' -> word_op (fromNat n) a vs w'
           LargeBitsVal m xs -> bits_op (fromNat n) a vs . Seq.fromList =<< traverse (fromBit =<<) (enumerateSeqMap m xs)
         _ -> evalPanic "Expected word value" ["indexPrim"]


updatePrim ::
  Backend sym =>
  (Nat' -> TValue -> WordValue sym -> WordValue sym -> Eval (GenValue sym) -> Eval (WordValue sym)) ->
  (Nat' -> TValue -> SeqMap sym    -> WordValue sym -> Eval (GenValue sym) -> Eval (SeqMap sym)) ->
  GenValue sym
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
fromToV :: Backend sym => sym -> GenValue sym
fromToV sym =
  nlam $ \ first ->
  nlam $ \ lst   ->
  tlam $ \ ty    ->
    let !f = mkLit sym ty in
    case (first, lst) of
      (Nat first', Nat lst') ->
        let len = 1 + (lst' - first')
        in VSeq len $ IndexSeqMap $ \i -> f (first' + i)
      _ -> evalPanic "fromToV" ["invalid arguments"]

-- @[ 0, 1 .. 10 ]@
fromThenToV :: Backend sym => sym -> GenValue sym
fromThenToV sym =
  nlam $ \ first ->
  nlam $ \ next  ->
  nlam $ \ lst   ->
  tlam $ \ ty    ->
  nlam $ \ len   ->
    let !f = mkLit sym ty in
    case (first, next, lst, len) of
      (Nat first', Nat next', Nat _lst', Nat len') ->
        let diff = next' - first'
        in VSeq len' $ IndexSeqMap $ \i -> f (first' + i*diff)
      _ -> evalPanic "fromThenToV" ["invalid arguments"]


infFromV :: Backend sym => sym -> GenValue sym
infFromV sym =
  tlam $ \ ty ->
  lam  $ \ x ->
  return $ VStream $ IndexSeqMap $ \i ->
  do x' <- x
     i' <- io (integerLit sym i)
     addV sym ty x' =<< intV sym i' ty

infFromThenV :: Backend sym => sym -> GenValue sym
infFromThenV sym =
  tlam $ \ ty ->
  lam $ \ first -> return $
  lam $ \ next ->
  do x <- first
     y <- next
     d <- subV sym ty y x
     return $ VStream $ IndexSeqMap $ \i -> do
       i' <- io (integerLit sym i)
       addV sym ty x =<< mulV sym ty d =<< intV sym i' ty

-- Miscellaneous ---------------------------------------------------------------

errorV :: forall sym.
  Backend sym =>
  TValue ->
  String ->
  Eval (GenValue sym)
errorV ty msg = case ty of
  -- bits
  TVBit -> cryUserError msg
  TVInteger -> cryUserError msg
  TVIntMod _ -> cryUserError msg

  -- sequences
  TVSeq w ety
     | isTBit ety -> return $ VWord w $ return $ LargeBitsVal w $ IndexSeqMap $ \_ -> cryUserError msg
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
    return $ VRecord $ fmap (flip errorV msg) $ Map.fromList fields

  TVAbstract {} -> cryUserError msg


-- Merge and if/then/else

iteValue :: Backend sym =>
  sym ->
  SBit sym ->
  Eval (GenValue sym) ->
  Eval (GenValue sym) ->
  Eval (GenValue sym)
iteValue sym b x y
  | Just True  <- bitAsLit sym b = x
  | Just False <- bitAsLit sym b = y
  | otherwise = mergeValue' sym b x y

mergeWord :: Backend sym =>
  sym ->
  SBit sym ->
  WordValue sym ->
  WordValue sym ->
  Eval (WordValue sym)
mergeWord sym c (WordVal w1) (WordVal w2) =
  WordVal <$> io (iteWord sym c w1 w2)
mergeWord sym c w1 w2 =
  pure $ LargeBitsVal (wordValueSize sym w1) (mergeSeqMap sym c (asBitsMap sym w1) (asBitsMap sym w2))

mergeWord' :: Backend sym =>
  sym ->
  SBit sym ->
  Eval (WordValue sym) ->
  Eval (WordValue sym) ->
  Eval (WordValue sym)
mergeWord' sym c mx my =
  do x <- mx
     y <- my
     mergeWord sym c x y

mergeValue' :: Backend sym =>
  sym ->
  SBit sym ->
  Eval (GenValue sym) ->
  Eval (GenValue sym) ->
  Eval (GenValue sym)
mergeValue' sym b mx my =
  do x <- mx
     y <- my
     mergeValue sym b x y


mergeValue :: Backend sym =>
  sym ->
  SBit sym ->
  GenValue sym ->
  GenValue sym ->
  Eval (GenValue sym)
mergeValue sym c v1 v2 =
  case (v1, v2) of
    (VRecord fs1, VRecord fs2)  | Map.keys fs1 == Map.keys fs2 ->
                                  pure $ VRecord $ Map.intersectionWith (mergeValue' sym c) fs1 fs2
    (VTuple vs1 , VTuple vs2 ) | length vs1 == length vs2  ->
                                  pure $ VTuple $ zipWith (mergeValue' sym c) vs1 vs2
    (VBit b1    , VBit b2    ) -> VBit <$> io (iteBit sym c b1 b2)
    (VInteger i1, VInteger i2) -> VInteger <$> io (iteInteger sym c i1 i2)
    (VWord n1 w1, VWord n2 w2 ) | n1 == n2 -> pure $ VWord n1 $ mergeWord' sym c w1 w2
    (VSeq n1 vs1, VSeq n2 vs2 ) | n1 == n2 -> VSeq n1 <$> memoMap (mergeSeqMap sym c vs1 vs2)
    (VStream vs1, VStream vs2) -> VStream <$> memoMap (mergeSeqMap sym c vs1 vs2)
    (VFun f1    , VFun f2    ) -> pure $ VFun $ \x -> mergeValue' sym c (f1 x) (f2 x)
    (VPoly f1   , VPoly f2   ) -> pure $ VPoly $ \x -> mergeValue' sym c (f1 x) (f2 x)
    (_          , _          ) -> panic "Cryptol.Eval.Generic"
                                  [ "mergeValue: incompatible values" ]

mergeSeqMap :: Backend sym =>
  sym ->
  SBit sym ->
  SeqMap sym ->
  SeqMap sym ->
  SeqMap sym 
mergeSeqMap sym c x y =
  IndexSeqMap $ \i ->
  do xi <- lookupSeqMap x i
     yi <- lookupSeqMap y i
     mergeValue sym c xi yi
