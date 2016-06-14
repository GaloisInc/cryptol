-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe #-}

{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module Cryptol.Eval.Value where

import Data.Bits
import Data.IORef
--import           Data.Map (Map)
import qualified Data.Sequence as Seq
import qualified Data.Map.Strict as Map
import qualified Data.Foldable as Fold
import qualified Data.Set as Set

import MonadLib

import qualified Cryptol.Eval.Arch as Arch
import Cryptol.Eval.Monad
import Cryptol.Eval.Type

import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Solver.InfNat(Nat'(..))
import Cryptol.Utils.Ident (Ident,mkIdent)
import Cryptol.Utils.PP
import Cryptol.Utils.Panic(panic)

--import Control.Monad (guard, zipWithM)
import Data.List(genericLength, genericIndex)
import Data.Bits (setBit,testBit,(.&.),shiftL)
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import Numeric (showIntAtBase)

import GHC.Generics (Generic)
import Control.DeepSeq

import qualified Data.Cache.LRU.IO as LRU


-- Values ----------------------------------------------------------------------

-- | width, value
-- Invariant: The value must be within the range 0 .. 2^width-1
data BV = BV !Integer !Integer deriving (Generic, NFData)

instance Show BV where
  show = show . bvVal

-- | Apply an integer function to the values of bitvectors.
--   This function assumes both bitvectors are the same width.
binBV :: (Integer -> Integer -> Integer) -> BV -> BV -> BV
binBV f (BV w x) (BV _ y) = mkBv w (f x y)

-- | Apply an integer function to the values of a bitvector.
--   This function assumes the function will not require masking.
unaryBV :: (Integer -> Integer) -> BV -> BV
unaryBV f (BV w x) = mkBv w $ f x

bvVal :: BV -> Integer
bvVal (BV _w x) = x

-- | Smart constructor for 'BV's that checks for the width limit
mkBv :: Integer -> Integer -> BV
mkBv w i = BV w (mask w i)

newtype SeqMap b w = SeqMap { lookupSeqMap :: Integer -> Eval (GenValue b w) }
type SeqValMap = SeqMap Bool BV

instance NFData (SeqMap b w) where
  rnf x = seq x ()

finiteSeqMap :: [Eval (GenValue b w)] -> Eval (SeqMap b w)
finiteSeqMap xs = do
   memoMap (SeqMap $ \i -> genericIndex xs i)

infiniteSeqMap :: [Eval (GenValue b w)] -> Eval (SeqMap b w)
infiniteSeqMap xs =
   memoMap (SeqMap $ \i -> genericIndex xs i)

enumerateSeqMap :: (Integral n) => n -> SeqMap b w -> [Eval (GenValue b w)]
enumerateSeqMap n m = [ lookupSeqMap m i | i <- [0 .. (toInteger n)-1] ]

streamSeqMap :: SeqMap b w -> [Eval (GenValue b w)]
streamSeqMap m = [ lookupSeqMap m i | i <- [0..] ]

reverseSeqMap :: Integer -> SeqMap b w -> SeqMap b w
reverseSeqMap n vals = SeqMap $ \i -> lookupSeqMap vals (n - 1 - i)

splitSeqMap :: Integer -> SeqMap b w -> (SeqMap b w, SeqMap b w)
splitSeqMap n xs = (hd,tl)
  where
  hd = xs
  tl = SeqMap $ \i -> lookupSeqMap xs (i+n)

memoMap :: SeqMap b w -> Eval (SeqMap b w)
memoMap x = do
  -- TODO: make the size of the LRU cache a tuneable parameter...
  lru <- io $ LRU.newAtomicLRU (Just 64)
  return $ SeqMap $ memo lru

 where
 memo lru i =  do
    mz <- io $ LRU.lookup i lru
    case mz of
      Just z  -> return z
      Nothing -> doEval lru i

 doEval lru i = do
    v <- lookupSeqMap x i
    io $ LRU.insert i v lru
    return v

zipSeqMap :: (GenValue b w -> GenValue b w -> Eval (GenValue b w))
          -> SeqMap b w
          -> SeqMap b w
          -> Eval (SeqMap b w)
zipSeqMap f x y =
  memoMap (SeqMap $ \i -> join (f <$> lookupSeqMap x i <*> lookupSeqMap y i))

mapSeqMap :: (GenValue b w -> Eval (GenValue b w))
          -> SeqMap b w -> Eval (SeqMap b w)
mapSeqMap f x =
  memoMap (SeqMap $ \i -> f =<< lookupSeqMap x i)

data WordValue b w
  = WordVal !w
  | BitsVal !(Seq.Seq (Eval b))
 deriving (Generic, NFData)

asWordVal :: BitWord b w => WordValue b w -> Eval w
asWordVal (WordVal w)  = return w
asWordVal (BitsVal bs) = packWord <$> sequence (Fold.toList bs)

asBitsVal :: BitWord b w => WordValue b w -> Seq.Seq (Eval b)
asBitsVal (WordVal w)  = Seq.fromList $ map ready $ unpackWord w
asBitsVal (BitsVal bs) = bs

indexWordValue :: BitWord b w => WordValue b w -> Integer -> Eval b
indexWordValue (WordVal w)  idx = return $ genericIndex (unpackWord w) idx
indexWordValue (BitsVal bs) idx = Seq.index bs (fromInteger idx)


-- | Generic value type, parameterized by bit and word types.
data GenValue b w
  = VRecord ![(Ident, Eval (GenValue b w))] -- @ { .. } @
  | VTuple ![Eval (GenValue b w)]           -- @ ( .. ) @
  | VBit !b                                 -- @ Bit    @
  | VSeq !Integer !(SeqMap b w)             -- @ [n]a   @
                                            -- Invariant: VSeq is never a sequence of bits
  | VWord !Integer !(Eval (WordValue b w))  -- @ [n]Bit @
  | VStream !(SeqMap b w)                   -- @ [inf]a @
  | VFun (Eval (GenValue b w) -> Eval (GenValue b w)) -- functions
  | VPoly (TValue -> Eval (GenValue b w))   -- polymorphic values (kind *)
  | VNumPoly (Nat' -> Eval (GenValue b w))  -- polymorphic values (kind #)
  deriving (Generic, NFData)


forceWordValue :: WordValue b w -> Eval ()
forceWordValue (WordVal w)  = return ()
forceWordValue (BitsVal bs) = mapM_ (\b -> const () <$> b) bs

forceValue :: GenValue b w -> Eval ()
forceValue v = case v of
  VRecord fs  -> mapM_ (\x -> forceValue =<< snd x) fs
  VTuple xs   -> mapM_ (forceValue =<<) xs
  VSeq n xs   -> mapM_ (forceValue =<<) (enumerateSeqMap n xs)
  VBit b      -> return ()
  VWord _ wv  -> forceWordValue =<< wv
  VStream _   -> return ()
  VFun _      -> return ()
  VPoly _     -> return ()


instance (Show b, Show w) => Show (GenValue b w) where
  show v = case v of
    VRecord fs -> "record:" ++ show (map fst fs)
    VTuple xs  -> "tuple:" ++ show (length xs)
    VBit b     -> show b
    VSeq n _   -> "seq:" ++ show n
    VWord n _  -> "word:"  ++ show n
    VStream _  -> "stream"
    VFun _     -> "fun"
    VPoly _    -> "poly"

type Value = GenValue Bool BV


-- Pretty Printing -------------------------------------------------------------

data PPOpts = PPOpts
  { useAscii     :: Bool
  , useBase      :: Int
  , useInfLength :: Int
  }

defaultPPOpts :: PPOpts
defaultPPOpts = PPOpts { useAscii = False, useBase = 10, useInfLength = 5 }

atFst :: Functor f => (a -> f b) -> (a, c) -> f (b, c)
atFst f (x,y) = fmap (,y) $ f x

atSnd :: Functor f => (a -> f b) -> (c, a) -> f (c, b)
atSnd f (x,y) = fmap (x,) $ f y

ppValue :: forall b w
         . BitWord b w
        => PPOpts
        -> GenValue b w
        -> Eval Doc
ppValue opts = loop
  where
  loop :: GenValue b w -> Eval Doc
  loop val = case val of
    VRecord fs         -> do fs' <- traverse (atSnd (>>=loop)) $ fs
                             return $ braces (sep (punctuate comma (map ppField fs')))
      where
      ppField (f,r) = pp f <+> char '=' <+> r
    VTuple vals        -> do vals' <- traverse (>>=loop) vals
                             return $ parens (sep (punctuate comma vals'))
    VBit b             -> return $ ppBit b
    VSeq sz vals       -> ppWordSeq sz vals
    VWord _ wv         -> ppWordVal =<< wv
    VStream vals       -> do vals' <- traverse (>>=loop) $ enumerateSeqMap (useInfLength opts) vals
                             return $ brackets $ fsep
                                   $ punctuate comma
                                   ( vals' ++ [text "..."]
                                   )
    VFun _             -> return $ text "<function>"
    VPoly _            -> return $ text "<polymorphic value>"

  ppWordVal :: WordValue b w -> Eval Doc
  ppWordVal w = ppWord opts <$> asWordVal w

  ppWordSeq :: Integer -> SeqMap b w -> Eval Doc
  ppWordSeq sz vals = do
    ws <- sequence (enumerateSeqMap sz vals)
    case ws of
      w : _
        | Just l <- vWordLen w
        , asciiMode opts l
        -> do vs <- traverse (fromVWord "ppWordSeq") ws
              case traverse wordAsChar vs of
                Just str -> return $ text str
                _ -> return $ brackets (fsep (punctuate comma $ map (ppWord opts) vs))
      _ -> do ws' <- traverse loop ws
              return $ brackets (fsep (punctuate comma ws'))

asciiMode :: PPOpts -> Integer -> Bool
asciiMode opts width = useAscii opts && (width == 7 || width == 8)

integerToChar :: Integer -> Char
integerToChar = toEnum . fromInteger


ppBV :: PPOpts -> BV -> Doc
ppBV opts (BV width i)
  | base > 36 = integer i -- not sure how to rule this out
  | asciiMode opts width = text (show (toEnum (fromInteger i) :: Char))
  | otherwise = prefix <> text value
  where
  base = useBase opts

  padding bitsPerDigit = text (replicate padLen '0')
    where
    padLen | m > 0     = d + 1
           | otherwise = d

    (d,m) = (fromInteger width - (length value * bitsPerDigit))
                   `divMod` bitsPerDigit

  prefix = case base of
    2  -> text "0b" <> padding 1
    8  -> text "0o" <> padding 3
    10 -> empty
    16 -> text "0x" <> padding 4
    _  -> text "0"  <> char '<' <> int base <> char '>'

  value  = showIntAtBase (toInteger base) (digits !!) i ""
  digits = "0123456789abcdefghijklmnopqrstuvwxyz"


-- Big-endian Words ------------------------------------------------------------

class BitWord b w | b -> w, w -> b where
  ppBit :: b -> Doc

  ppWord :: PPOpts -> w -> Doc

  wordAsChar :: w -> Maybe Char

  wordLen :: w -> Integer

  bitLit :: Bool -> b
  wordLit :: Integer -> Integer -> w

  -- | NOTE this assumes that the sequence of bits is big-endian and finite, so the
  -- first element of the list will be the most significant bit.
  packWord :: [b] -> w

  -- | NOTE this produces a list of bits that represent a big-endian word, so the
  -- most significant bit is the first element of the list.
  unpackWord :: w -> [b]

  -- | NOTE first argument represents the more-significant bits
  joinWord :: w -> w -> w

  -- | Take the most-significant bits, and return
  --   those bits and the remainder.  The first element
  --   of the pair is the most significant bits.
  splitWord :: Integer -- ^ left width
            -> Integer -- ^ right width
            -> w
            -> (w, w)

  extractWord :: Integer -- ^ Number of bits to take
              -> Integer -- ^ starting bit
              -> w
              -> w

  wordPlus :: w -> w -> w
  wordMinus :: w -> w -> w
  wordMult :: w -> w -> w


class BitWord b w => EvalPrims b w where
  evalPrim :: Decl -> GenValue b w
  iteValue :: b
           -> Eval (GenValue b w)
           -> Eval (GenValue b w)
           -> Eval (GenValue b w)

mask :: Integer  -- ^ Bit-width
     -> Integer  -- ^ Value
     -> Integer  -- ^ Masked result
mask w i | w >= Arch.maxBigIntWidth = wordTooWide w
         | otherwise                = i .&. ((1 `shiftL` fromInteger w) - 1)


instance BitWord Bool BV where
  wordLen (BV w _) = w
  wordAsChar (BV _ x) = Just $ integerToChar x

  ppBit b | b         = text "True"
          | otherwise = text "False"

  ppWord = ppBV

  bitLit b = b
  wordLit = mkBv

  packWord bits = BV (toInteger w) a
    where
      w = case length bits of
            len | toInteger len >= Arch.maxBigIntWidth -> wordTooWide (toInteger len)
                | otherwise                  -> len
      a = foldl set 0 (zip [w - 1, w - 2 .. 0] bits)
      set acc (n,b) | b         = setBit acc n
                    | otherwise = acc

  unpackWord (BV w a) = [ testBit a n | n <- [w' - 1, w' - 2 .. 0] ]
    where
      w' = fromInteger w

  joinWord (BV i x) (BV j y) =
    BV (i + j) (shiftL x (fromInteger j) + y)

  splitWord leftW rightW (BV _ x) =
     ( BV leftW (x `shiftR` (fromInteger rightW)), mkBv rightW x )

  extractWord n i (BV _ x) = mkBv n (x `shiftR` (fromInteger i))

  wordPlus (BV i x) (BV j y)
    | i == j = mkBv i (x+y)
    | otherwise = panic "Attempt to add words of different sizes: wordPlus" []

  wordMinus (BV i x) (BV j y)
    | i == j = mkBv i (x-y)
    | otherwise = panic "Attempt to subtract words of different sizes: wordMinus" []

  wordMult (BV i x) (BV j y)
    | i == j = mkBv i (x*y)
    | otherwise = panic "Attempt to multiply words of different sizes: wordMult" []


-- Value Constructors ----------------------------------------------------------

-- | Create a packed word of n bits.
word :: BitWord b w => Integer -> Integer -> GenValue b w
word n i = VWord n $ ready $ WordVal $ wordLit n i

lam :: (Eval (GenValue b w) -> Eval (GenValue b w)) -> GenValue b w
lam  = VFun

-- | Functions that assume word inputs
wlam :: BitWord b w => (w -> Eval (GenValue b w)) -> GenValue b w
wlam f = VFun (\x -> x >>= fromVWord "wlam" >>= f)

-- | A type lambda that expects a @Type@.
tlam :: (TValue -> GenValue b w) -> GenValue b w
tlam f = VPoly (return . f)

-- | A type lambda that expects a @Type@ of kind #.
nlam :: (Nat' -> GenValue b w) -> GenValue b w
nlam f = VNumPoly (return . f)

-- | Generate a stream.
toStream :: [GenValue b w] -> Eval (GenValue b w)
toStream vs =
   VStream <$> infiniteSeqMap (map ready vs)

toFinSeq :: BitWord b w
         => Integer -> TValue -> [GenValue b w] -> Eval (GenValue b w)
toFinSeq len elty vs
   | isTBit elty = return $ VWord len $ ready $ WordVal $ packWord $ map fromVBit vs
   | otherwise   = VSeq len <$> finiteSeqMap (map ready vs)

-- | This is strict!
boolToWord :: [Bool] -> Value
boolToWord bs = VWord (genericLength bs) $ ready $ WordVal $ packWord bs

-- | Construct either a finite sequence, or a stream.  In the finite case,
-- record whether or not the elements were bits, to aid pretty-printing.
toSeq :: BitWord b w
      => Nat' -> TValue -> [GenValue b w] -> Eval (GenValue b w)
toSeq len elty vals = case len of
  Nat n -> toFinSeq n elty vals
  Inf   -> toStream vals


-- | Construct either a finite sequence, or a stream.  In the finite case,
-- record whether or not the elements were bits, to aid pretty-printing.
mkSeq :: Nat' -> TValue -> SeqMap b w -> GenValue b w
mkSeq len elty vals = case len of
  Nat n
    | isTBit elty -> VWord n $ return $ BitsVal $ Seq.fromFunction (fromInteger n) $ \i ->
                        fromVBit <$> lookupSeqMap vals (toInteger i)
    | otherwise   -> VSeq n vals
  Inf             -> VStream vals


-- Value Destructors -----------------------------------------------------------

-- | Extract a bit value.
fromVBit :: GenValue b w -> b
fromVBit val = case val of
  VBit b -> b
  _      -> evalPanic "fromVBit" ["not a Bit"]

bitsSeq :: BitWord b w => WordValue b w -> Integer -> Eval b
bitsSeq (WordVal w) =
  let bs = unpackWord w
   in \i -> return $ genericIndex bs i
bitsSeq (BitsVal bs) = \i -> Seq.index bs (fromInteger i)

-- | Extract a sequence.
fromSeq :: forall b w. BitWord b w => String -> GenValue b w -> Eval (SeqMap b w)
fromSeq msg val = case val of
  VSeq _ vs   -> return vs
  VStream vs  -> return vs
  _           -> evalPanic "fromSeq" ["not a sequence", msg]

fromStr :: Value -> Eval String
fromStr (VSeq n vals) =
  traverse (\x -> toEnum . fromInteger <$> (fromWord "fromStr" =<< x)) (enumerateSeqMap n vals)
fromStr _ = evalPanic "fromStr" ["Not a finite sequence"]

fromWordVal :: String -> GenValue b w -> Eval (WordValue b w)
fromWordVal _msg (VWord _ wval) = wval
fromWordVal msg _ = evalPanic "fromWordVal" ["not a word value", msg]

-- | Extract a packed word.
fromVWord :: BitWord b w => String -> GenValue b w -> Eval w
fromVWord _msg (VWord _ wval) = wval >>= asWordVal 
fromVWord msg _ = evalPanic "fromVWord" ["not a word", msg]

vWordLen :: BitWord b w => GenValue b w -> Maybe Integer
vWordLen val = case val of
  VWord n _wv              -> Just n
  _                        -> Nothing

tryFromBits :: BitWord b w => [Eval (GenValue b w)] -> Maybe w
tryFromBits = go id
 where
 go f [] = Just (packWord (f []))
 go f (Ready (VBit b):vs) = go ((b:) . f) vs
 go f (v:vs) = Nothing


-- | Turn a value into an integer represented by w bits.
fromWord :: String -> Value -> Eval Integer
fromWord msg val = bvVal <$> fromVWord msg val

-- | Extract a function from a value.
fromVFun :: GenValue b w -> (Eval (GenValue b w) -> Eval (GenValue b w))
fromVFun val = case val of
  VFun f -> f
  _      -> evalPanic "fromVFun" ["not a function"]

-- | Extract a polymorphic function from a value.
fromVPoly :: GenValue b w -> (TValue -> Eval (GenValue b w))
fromVPoly val = case val of
  VPoly f -> f
  _       -> evalPanic "fromVPoly" ["not a polymorphic value"]

-- | Extract a polymorphic function from a value.
fromVNumPoly :: GenValue b w -> (Nat' -> Eval (GenValue b w))
fromVNumPoly val = case val of
  VNumPoly f -> f
  _          -> evalPanic "fromVNumPoly" ["not a polymorphic value"]

-- | Extract a tuple from a value.
fromVTuple :: GenValue b w -> [Eval (GenValue b w)]
fromVTuple val = case val of
  VTuple vs -> vs
  _         -> evalPanic "fromVTuple" ["not a tuple"]

-- | Extract a record from a value.
fromVRecord :: GenValue b w -> [(Ident, Eval (GenValue b w))]
fromVRecord val = case val of
  VRecord fs -> fs
  _          -> evalPanic "fromVRecord" ["not a record"]

-- | Lookup a field in a record.
lookupRecord :: Ident -> GenValue b w -> Eval (GenValue b w)
lookupRecord f rec = case lookup f (fromVRecord rec) of
  Just val -> val
  Nothing  -> evalPanic "lookupRecord" ["malformed record"]

-- Value to Expression conversion ----------------------------------------------

-- | Given an expected type, returns an expression that evaluates to
-- this value, if we can determine it.
--
-- XXX: View patterns would probably clean up this definition a lot.
toExpr :: PrimMap -> Type -> Value -> Eval (Maybe Expr)
toExpr prims t0 v0 = findOne (go t0 v0)
  where

  prim n = ePrim prims (mkIdent (T.pack n))

  go :: Type -> Value -> ChoiceT Eval Expr
  go ty val = case (ty, val) of
    (TRec tfs, VRecord vfs) -> do
      let fns = map fst vfs
      guard (map fst tfs == fns)
      fes <- zipWithM go (map snd tfs) =<< lift (traverse snd vfs)
      return $ ERec (zip fns fes)
    (TCon (TC (TCTuple tl)) ts, VTuple tvs) -> do
      guard (tl == (length tvs))
      ETuple `fmap` (zipWithM go ts =<< lift (sequence tvs))
    (TCon (TC TCBit) [], VBit True ) -> return (prim "True")
    (TCon (TC TCBit) [], VBit False) -> return (prim "False")
    (TCon (TC TCSeq) [a,b], VSeq 0 _) -> do
      guard (a == tZero)
      return $ EList [] b
    (TCon (TC TCSeq) [a,b], VSeq n svs) -> do
      guard (a == tNum n)
      ses <- mapM (go b) =<< lift (sequence (enumerateSeqMap n svs))
      return $ EList ses b
    (TCon (TC TCSeq) [a,(TCon (TC TCBit) [])], VWord _ wval) -> do
      BV w v <- lift (asWordVal =<< wval)
      guard (a == tNum w)
      return $ ETApp (ETApp (prim "demote") (tNum v)) (tNum w)
    (_, VStream _) -> fail "cannot construct infinite expressions"
    (_, VFun    _) -> fail "cannot convert function values to expressions"
    (_, VPoly   _) -> fail "cannot convert polymorphic values to expressions"
    _ -> do doc <- lift (ppValue defaultPPOpts val)
            panic "Cryptol.Eval.Value.toExpr"
             ["type mismatch:"
             , pretty ty
             , render doc
             ]
