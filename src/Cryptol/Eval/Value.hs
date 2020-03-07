-- |
-- Module      :  Cryptol.Eval.Value
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Cryptol.Eval.Value where

import Data.Kind (Type)
import Data.Bits
import Data.IORef
import qualified Data.Sequence as Seq
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import MonadLib

import qualified Cryptol.Eval.Arch as Arch
import Cryptol.Eval.Monad
import Cryptol.Eval.Type

import Cryptol.TypeCheck.AST hiding (Type)
import qualified Cryptol.TypeCheck.AST as AST
import Cryptol.TypeCheck.Solver.InfNat(Nat'(..))
import Cryptol.Utils.Ident (Ident,mkIdent)
import Cryptol.Utils.PP
import Cryptol.Utils.Panic(panic)

import Data.List(genericLength, genericIndex, genericDrop)
import qualified Data.Text as T
import Numeric (showIntAtBase)

import GHC.Generics (Generic)
import Control.DeepSeq

-- Values ----------------------------------------------------------------------

-- | Concrete bitvector values: width, value
-- Invariant: The value must be within the range 0 .. 2^width-1
data BV = BV !Integer !Integer deriving (Generic, NFData)

instance Show BV where
  show = show . bvVal

-- | Apply an integer function to the values of bitvectors.
--   This function assumes both bitvectors are the same width.
binBV :: Applicative m => (Integer -> Integer -> Integer) -> BV -> BV -> m BV
binBV f (BV w x) (BV _ y) = pure $ mkBv w (f x y)

-- | Apply an integer function to the values of a bitvector.
--   This function assumes the function will not require masking.
unaryBV :: (Integer -> Integer) -> BV -> BV
unaryBV f (BV w x) = mkBv w $ f x

bvVal :: BV -> Integer
bvVal (BV _w x) = x

-- | Smart constructor for 'BV's that checks for the width limit
mkBv :: Integer -> Integer -> BV
mkBv w i = BV w (mask w i)

-- | A sequence map represents a mapping from nonnegative integer indices
--   to values.  These are used to represent both finite and infinite sequences.
data SeqMap sym
  = IndexSeqMap  !(Integer -> Eval (GenValue sym))
  | UpdateSeqMap !(Map Integer (Eval (GenValue sym)))
                 !(Integer -> Eval (GenValue sym))

lookupSeqMap :: SeqMap sym -> Integer -> Eval (GenValue sym)
lookupSeqMap (IndexSeqMap f) i = f i
lookupSeqMap (UpdateSeqMap m f) i =
  case Map.lookup i m of
    Just x  -> x
    Nothing -> f i

type SeqValMap = SeqMap ()

-- | An arbitrarily-chosen number of elements where we switch from a dense
--   sequence representation of bit-level words to 'SeqMap' representation.
largeBitSize :: Integer
largeBitSize = 1 `shiftL` 16

-- | Generate a finite sequence map from a list of values
finiteSeqMap :: [Eval (GenValue sym)] -> SeqMap sym
finiteSeqMap xs =
   UpdateSeqMap
      (Map.fromList (zip [0..] xs))
      invalidIndex

-- | Generate an infinite sequence map from a stream of values
infiniteSeqMap :: [Eval (GenValue sym)] -> Eval (SeqMap sym)
infiniteSeqMap xs =
   -- TODO: use an int-trie?
   memoMap (IndexSeqMap $ \i -> genericIndex xs i)

-- | Create a finite list of length @n@ of the values from @[0..n-1]@ in
--   the given the sequence emap.
enumerateSeqMap :: (Integral n) => n -> SeqMap sym -> [Eval (GenValue sym)]
enumerateSeqMap n m = [ lookupSeqMap m i | i <- [0 .. (toInteger n)-1] ]

-- | Create an infinite stream of all the values in a sequence map
streamSeqMap :: SeqMap sym -> [Eval (GenValue sym)]
streamSeqMap m = [ lookupSeqMap m i | i <- [0..] ]

-- | Reverse the order of a finite sequence map
reverseSeqMap :: Integer     -- ^ Size of the sequence map
              -> SeqMap sym
              -> SeqMap sym
reverseSeqMap n vals = IndexSeqMap $ \i -> lookupSeqMap vals (n - 1 - i)

updateSeqMap :: SeqMap sym -> Integer -> Eval (GenValue sym) -> SeqMap sym
updateSeqMap (UpdateSeqMap m sm) i x = UpdateSeqMap (Map.insert i x m) sm
updateSeqMap (IndexSeqMap f) i x = UpdateSeqMap (Map.singleton i x) f

-- | Concatenate the first @n@ values of the first sequence map onto the
--   beginning of the second sequence map.
concatSeqMap :: Integer -> SeqMap sym -> SeqMap sym -> SeqMap sym
concatSeqMap n x y =
    IndexSeqMap $ \i ->
       if i < n
         then lookupSeqMap x i
         else lookupSeqMap y (i-n)

-- | Given a number @n@ and a sequence map, return two new sequence maps:
--   the first containing the values from @[0..n-1]@ and the next containing
--   the values from @n@ onward.
splitSeqMap :: Integer -> SeqMap sym -> (SeqMap sym, SeqMap sym)
splitSeqMap n xs = (hd,tl)
  where
  hd = xs
  tl = IndexSeqMap $ \i -> lookupSeqMap xs (i+n)

-- | Drop the first @n@ elements of the given 'SeqMap'.
dropSeqMap :: Integer -> SeqMap sym -> SeqMap sym
dropSeqMap 0 xs = xs
dropSeqMap n xs = IndexSeqMap $ \i -> lookupSeqMap xs (i+n)

-- | Given a sequence map, return a new sequence map that is memoized using
--   a finite map memo table.
memoMap :: SeqMap sym -> Eval (SeqMap sym)
memoMap x = do
  cache <- io $ newIORef $ Map.empty
  return $ IndexSeqMap (memo cache)

  where
  memo cache i = do
    mz <- io (Map.lookup i <$> readIORef cache)
    case mz of
      Just z  -> return z
      Nothing -> doEval cache i

  doEval cache i = do
    v <- lookupSeqMap x i
    io $ modifyIORef' cache (Map.insert i v)
    return v

-- | Apply the given evaluation function pointwise to the two given
--   sequence maps.
zipSeqMap ::
  (GenValue sym -> GenValue sym -> Eval (GenValue sym)) ->
  SeqMap sym ->
  SeqMap sym ->
  Eval (SeqMap sym)
zipSeqMap f x y =
  memoMap (IndexSeqMap $ \i -> join (f <$> lookupSeqMap x i <*> lookupSeqMap y i))

-- | Apply the given function to each value in the given sequence map
mapSeqMap ::
  (GenValue sym -> Eval (GenValue sym)) ->
  SeqMap sym -> Eval (SeqMap sym)
mapSeqMap f x =
  memoMap (IndexSeqMap $ \i -> f =<< lookupSeqMap x i)

-- | For efficiency reasons, we handle finite sequences of bits as special cases
--   in the evaluator.  In cases where we know it is safe to do so, we prefer to
--   used a "packed word" representation of bit sequences.  This allows us to rely
--   directly on Integer types (in the concrete evaluator) and SBV's Word types (in
--   the symbolic simulator).
--
--   However, if we cannot be sure all the bits of the sequence
--   will eventually be forced, we must instead rely on an explicit sequence of bits
--   representation.
data WordValue sym
  = WordVal !(SWord sym)                      -- ^ Packed word representation for bit sequences.
  | LargeBitsVal !Integer !(SeqMap sym)       -- ^ A large bitvector sequence, represented as a
                                            --   'SeqMap' of bits.
 deriving (Generic)

-- | Force a word value into packed word form
asWordVal :: BitWord sym => sym -> WordValue sym -> Eval (SWord sym)
asWordVal _   (WordVal w)         = return w
asWordVal sym (LargeBitsVal n xs) = io . packWord sym =<< traverse (fromBit =<<) (enumerateSeqMap n xs)

-- | Force a word value into a sequence of bits
asBitsMap :: BitWord sym => sym -> WordValue sym -> SeqMap sym
asBitsMap sym (WordVal w)  = IndexSeqMap $ \i -> VBit <$> io (wordBit sym w i)
asBitsMap _   (LargeBitsVal _ xs) = xs

-- | Turn a word value into a sequence of bits, forcing each bit.
--   The sequence is returned in big-endian order.
enumerateWordValue :: BitWord sym => sym -> WordValue sym -> Eval [SBit sym]
enumerateWordValue sym (WordVal w) = io (unpackWord sym w)
enumerateWordValue _ (LargeBitsVal n xs) = traverse (fromBit =<<) (enumerateSeqMap n xs)

-- | Turn a word value into a sequence of bits, forcing each bit.
--   The sequence is returned in reverse of the usual order, which is little-endian order.
enumerateWordValueRev :: BitWord sym => sym -> WordValue sym -> Eval [SBit sym]
enumerateWordValueRev sym (WordVal w)  = reverse <$> io (unpackWord sym w)
enumerateWordValueRev _   (LargeBitsVal n xs) = traverse (fromBit =<<) (enumerateSeqMap n (reverseSeqMap n xs))

-- | Compute the size of a word value
wordValueSize :: BitWord sym => sym -> WordValue sym -> Integer
wordValueSize sym (WordVal w)  = wordLen sym w
wordValueSize _ (LargeBitsVal n _) = n

checkedSeqIndex :: Seq.Seq a -> Integer -> Eval a
checkedSeqIndex xs i =
  case Seq.viewl (Seq.drop (fromInteger i) xs) of
    x Seq.:< _ -> return x
    Seq.EmptyL -> invalidIndex i

checkedIndex :: [a] -> Integer -> Eval a
checkedIndex xs i =
  case genericDrop i xs of
    (x:_) -> return x
    _     -> invalidIndex i

-- | Select an individual bit from a word value
indexWordValue :: BitWord sym => sym -> WordValue sym -> Integer -> Eval (SBit sym)
indexWordValue sym (WordVal w) idx
   | idx < wordLen sym w = io (wordBit sym w idx)
   | otherwise = invalidIndex idx
indexWordValue _ (LargeBitsVal n xs) idx
   | idx < n   = fromBit =<< lookupSeqMap xs idx
   | otherwise = invalidIndex idx

-- | Produce a new 'WordValue' from the one given by updating the @i@th bit with the
--   given bit value.
updateWordValue :: BitWord sym => sym -> WordValue sym -> Integer -> Eval (SBit sym) -> Eval (WordValue sym)
updateWordValue sym (WordVal w) idx (Ready b)
   | idx < wordLen sym w = WordVal <$> io (wordUpdate sym w idx b)
   | otherwise = invalidIndex idx
updateWordValue sym wv idx b
   | idx < wordValueSize sym wv =
        pure $ LargeBitsVal (wordValueSize sym wv) $ updateSeqMap (asBitsMap sym wv) idx (VBit <$> b)
   | otherwise = invalidIndex idx


-- | Generic value type, parameterized by bit and word types.
--
--   NOTE: we maintain an important invariant regarding sequence types.
--   'VSeq' must never be used for finite sequences of bits.
--   Always use the 'VWord' constructor instead!  Infinite sequences of bits
--   are handled by the 'VStream' constructor, just as for other types.
data GenValue sym
  = VRecord !(Map Ident (Eval (GenValue sym))) -- ^ @ { .. } @
  | VTuple ![Eval (GenValue sym)]              -- ^ @ ( .. ) @
  | VBit !(SBit sym)                           -- ^ @ Bit    @
  | VInteger !(SInteger sym)                   -- ^ @ Integer @ or @ Z n @
  | VSeq !Integer !(SeqMap sym)                -- ^ @ [n]a   @
                                               --   Invariant: VSeq is never a sequence of bits
  | VWord !Integer !(Eval (WordValue sym))  -- ^ @ [n]Bit @
  | VStream !(SeqMap sym)                   -- ^ @ [inf]a @
  | VFun (Eval (GenValue sym) -> Eval (GenValue sym)) -- ^ functions
  | VPoly (TValue -> Eval (GenValue sym))   -- ^ polymorphic values (kind *)
  | VNumPoly (Nat' -> Eval (GenValue sym))  -- ^ polymorphic values (kind #)
 deriving Generic


-- | Force the evaluation of a word value
forceWordValue :: WordValue sym -> Eval ()
forceWordValue (WordVal _w)  = return ()
forceWordValue (LargeBitsVal n xs) = mapM_ (\x -> const () <$> x) (enumerateSeqMap n xs)

-- | Force the evaluation of a value
forceValue :: GenValue sym -> Eval ()
forceValue v = case v of
  VRecord fs  -> mapM_ (forceValue =<<) fs
  VTuple xs   -> mapM_ (forceValue =<<) xs
  VSeq n xs   -> mapM_ (forceValue =<<) (enumerateSeqMap n xs)
  VBit _b     -> return ()
  VInteger _i -> return ()
  VWord _ wv  -> forceWordValue =<< wv
  VStream _   -> return ()
  VFun _      -> return ()
  VPoly _     -> return ()
  VNumPoly _  -> return ()


instance BitWord sym => Show (GenValue sym) where
  show v = case v of
    VRecord fs -> "record:" ++ show (Map.keys fs)
    VTuple xs  -> "tuple:" ++ show (length xs)
    VBit _     -> "bit"
    VInteger _ -> "integer"
    VSeq n _   -> "seq:" ++ show n
    VWord n _  -> "word:"  ++ show n
    VStream _  -> "stream"
    VFun _     -> "fun"
    VPoly _    -> "poly"
    VNumPoly _ -> "numpoly"

type Value = GenValue ()


-- Pretty Printing -------------------------------------------------------------

defaultPPOpts :: PPOpts
defaultPPOpts = PPOpts { useAscii = False, useBase = 10, useInfLength = 5 }

atFst :: Functor f => (a -> f b) -> (a, c) -> f (b, c)
atFst f (x,y) = fmap (,y) $ f x

atSnd :: Functor f => (a -> f b) -> (c, a) -> f (c, b)
atSnd f (x,y) = fmap (x,) $ f y

ppValue :: forall sym.
  BitWord sym =>
  sym ->
  PPOpts ->
  GenValue sym ->
  Eval Doc
ppValue x opts = loop
  where
  loop :: GenValue sym -> Eval Doc
  loop val = case val of
    VRecord fs         -> do fs' <- traverse (>>= loop) fs
                             return $ braces (sep (punctuate comma (map ppField (Map.assocs fs'))))
      where
      ppField (f,r) = pp f <+> char '=' <+> r
    VTuple vals        -> do vals' <- traverse (>>=loop) vals
                             return $ parens (sep (punctuate comma vals'))
    VBit b             -> return $ ppBit x b
    VInteger i         -> return $ ppInteger x opts i
    VSeq sz vals       -> ppWordSeq sz vals
    VWord _ wv         -> ppWordVal =<< wv
    VStream vals       -> do vals' <- traverse (>>=loop) $ enumerateSeqMap (useInfLength opts) vals
                             return $ brackets $ fsep
                                   $ punctuate comma
                                   ( vals' ++ [text "..."]
                                   )
    VFun _             -> return $ text "<function>"
    VPoly _            -> return $ text "<polymorphic value>"
    VNumPoly _         -> return $ text "<polymorphic value>"

  ppWordVal :: WordValue sym -> Eval Doc
  ppWordVal w = ppWord x opts <$> asWordVal x w

  ppWordSeq :: Integer -> SeqMap sym -> Eval Doc
  ppWordSeq sz vals = do
    ws <- sequence (enumerateSeqMap sz vals)
    case ws of
      w : _
        | Just l <- vWordLen w
        , asciiMode opts l
        -> do vs <- traverse (fromVWord x "ppWordSeq") ws
              case traverse (wordAsChar x) vs of
                Just str -> return $ text (show str)
                _ -> return $ brackets (fsep (punctuate comma $ map (ppWord x opts) vs))
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
  | otherwise = prefix <.> text value
  where
  base = useBase opts

  padding bitsPerDigit = text (replicate padLen '0')
    where
    padLen | m > 0     = d + 1
           | otherwise = d

    (d,m) = (fromInteger width - (length value * bitsPerDigit))
                   `divMod` bitsPerDigit

  prefix = case base of
    2  -> text "0b" <.> padding 1
    8  -> text "0o" <.> padding 3
    10 -> empty
    16 -> text "0x" <.> padding 4
    _  -> text "0"  <.> char '<' <.> int base <.> char '>'

  value  = showIntAtBase (toInteger base) (digits !!) i ""
  digits = "0123456789abcdefghijklmnopqrstuvwxyz"


-- | This type class defines a collection of operations on bits and words that
--   are necessary to define generic evaluator primitives that operate on both concrete
--   and symbolic values uniformly.
class BitWord sym where
  type SBit sym :: Type
  type SWord sym :: Type
  type SInteger sym :: Type

  -- | Pretty-print an individual bit
  ppBit :: sym -> SBit sym -> Doc

  -- | Pretty-print a word value
  ppWord :: sym -> PPOpts -> SWord sym -> Doc

  -- | Pretty-print an integer value
  ppInteger :: sym -> PPOpts -> SInteger sym -> Doc

  -- | Attempt to render a word value as an ASCII character.  Return 'Nothing'
  --   if the character value is unknown (e.g., for symbolic values).
  wordAsChar :: sym -> SWord sym -> Maybe Char

  -- | The number of bits in a word value.
  wordLen :: sym -> SWord sym -> Integer

  -- | Construct a literal bit value from a boolean.
  bitLit :: sym -> Bool -> IO (SBit sym)

  -- | Construct a literal word value given a bit width and a value.
  wordLit ::
    sym ->
    Integer {- ^ Width -} ->
    Integer {- ^ Value -} ->
    IO (SWord sym)

  -- | Construct a literal integer value from the given integer.
  integerLit ::
    sym ->
    Integer {- ^ Value -} ->
    IO (SInteger sym)

  -- | Extract the numbered bit from the word.
  --
  --   NOTE: this assumes that the sequence of bits is big-endian and finite, so the
  --   bit numbered 0 is the most significant bit.
  wordBit ::
    sym ->
    SWord sym ->
    Integer {- ^ Bit position to extract -} ->
    IO (SBit sym)

  -- | Update the numbered bit in the word.
  --
  --   NOTE: this assumes that the sequence of bits is big-endian and finite, so the
  --   bit numbered 0 is the most significant bit.
  wordUpdate ::
    sym ->
    SWord sym ->
    Integer {- ^ Bit position to update -} ->
    SBit sym ->
    IO (SWord sym)

  -- | Construct a word value from a finite sequence of bits.
  --   NOTE: this assumes that the sequence of bits is big-endian and finite, so the
  --   first element of the list will be the most significant bit.
  packWord ::
    sym ->
    [SBit sym] ->
    IO (SWord sym)

  -- | Deconstruct a packed word value in to a finite sequence of bits.
  --   NOTE: this produces a list of bits that represent a big-endian word, so
  --   the most significant bit is the first element of the list.
  unpackWord ::
    sym ->
    SWord sym ->
    IO [SBit sym]

  -- | Concatenate the two given word values.
  --   NOTE: the first argument represents the more-significant bits
  joinWord ::
    sym ->
    SWord sym ->
    SWord sym ->
    IO (SWord sym)

  -- | Take the most-significant bits, and return
  --   those bits and the remainder.  The first element
  --   of the pair is the most significant bits.
  --   The two integer sizes must sum to the length of the given word value.
  splitWord ::
    sym ->
    Integer {- ^ left width -} ->
    Integer {- ^ right width -} ->
    SWord sym ->
    IO (SWord sym, SWord sym)

  -- | Extract a subsequence of bits from a packed word value.
  --   The first integer argument is the number of bits in the
  --   resulting word.  The second integer argument is the
  --   number of less-significant digits to discard.  Stated another
  --   way, the operation @extractWord n i w@ is equivalent to
  --   first shifting @w@ right by @i@ bits, and then truncating to
  --   @n@ bits.
  extractWord ::
    sym ->
    Integer {- ^ Number of bits to take -} ->
    Integer {- ^ starting bit -} ->
    SWord sym ->
    IO (SWord sym)

  -- | 2's complement addition of packed words.  The arguments must have
  --   equal bit width, and the result is of the same width. Overflow is silently
  --   discarded.
  wordPlus ::
    sym ->
    SWord sym ->
    SWord sym ->
    IO (SWord sym)

  -- | 2's complement subtraction of packed words.  The arguments must have
  --   equal bit width, and the result is of the same width. Overflow is silently
  --   discarded.
  wordMinus ::
    sym ->
    SWord sym ->
    SWord sym ->
    IO (SWord sym)

  -- | 2's complement multiplication of packed words.  The arguments must have
  --   equal bit width, and the result is of the same width. The high bits of the
  --   multiplication are silently discarded.
  wordMult ::
    sym ->
    SWord sym ->
    SWord sym ->
    IO (SWord sym)

  -- | Construct an integer value from the given packed word.
  wordToInt ::
    sym ->
    SWord sym ->
    IO (SInteger sym)

  -- | Addition of unbounded integers.
  intPlus ::
    sym ->
    SInteger sym ->
    SInteger sym ->
    IO (SInteger sym)

  -- | Subtraction of unbounded integers.
  intMinus ::
    sym ->
    SInteger sym ->
    SInteger sym ->
    IO (SInteger sym)

  -- | Multiplication of unbounded integers.
  intMult ::
    sym ->
    SInteger sym ->
    SInteger sym ->
    IO (SInteger sym)

  -- | Addition of integers modulo n, for a concrete positive integer n.
  intModPlus ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SInteger sym ->
    IO (SInteger sym)

  -- | Subtraction of integers modulo n, for a concrete positive integer n.
  intModMinus ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SInteger sym ->
    IO (SInteger sym)

  -- | Multiplication of integers modulo n, for a concrete positive integer n.
  intModMult ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SInteger sym ->
    IO (SInteger sym)

  -- | Construct a packed word of the specified width from an integer value.
  wordFromInt ::
    sym ->
    Integer {- ^ bit-width -} ->
    SInteger sym ->
    IO (SWord sym)

-- | This class defines additional operations necessary to define generic evaluation
--   functions.
class BitWord sym => EvalPrims sym where
  -- | Eval prim binds primitive declarations to the primitive values that implement them.  Returns 'Nothing' for abstract primitives (i.e., once that are
  -- not implemented by this backend).
  evalPrim :: Decl -> Maybe (GenValue sym)

  -- | if/then/else operation.  Choose either the 'then' value or the 'else' value depending
  --   on the value of the test bit.
  iteValue ::
    sym ->
    SBit sym {- ^ Test bit -} ->
    Eval (GenValue sym)  {- ^ 'then' value -} ->
    Eval (GenValue sym)  {- ^ 'else' value -} ->
    Eval (GenValue sym)

-- Concrete Big-endian Words ------------------------------------------------------------

mask ::
  Integer  {- ^ Bit-width -} ->
  Integer  {- ^ Value -} ->
  Integer  {- ^ Masked result -}
mask w i | w >= Arch.maxBigIntWidth = wordTooWide w
         | otherwise                = i .&. ((1 `shiftL` fromInteger w) - 1)

instance BitWord () where
  type SBit () = Bool
  type SWord () = BV
  type SInteger () = Integer

  wordLen _ (BV w _) = w
  wordAsChar _ (BV _ x) = Just $! integerToChar x

  wordBit _ (BV w x) idx = pure $! testBit x (fromInteger (w - 1 - idx))

  wordUpdate _ (BV w x) idx True  = pure $! BV w (setBit   x (fromInteger (w - 1 - idx)))
  wordUpdate _ (BV w x) idx False = pure $! BV w (clearBit x (fromInteger (w - 1 - idx)))

  ppBit _ b | b         = text "True"
            | otherwise = text "False"

  ppWord _ = ppBV

  ppInteger _ _opts i = integer i

  bitLit _ b = pure b
  wordLit _ w i = pure $! mkBv w i
  integerLit _ i = pure i

  packWord _ bits = pure $! BV (toInteger w) a
    where
      w = case length bits of
            len | toInteger len >= Arch.maxBigIntWidth -> wordTooWide (toInteger len)
                | otherwise                  -> len
      a = foldl setb 0 (zip [w - 1, w - 2 .. 0] bits)
      setb acc (n,b) | b         = setBit acc n
                     | otherwise = acc

  unpackWord _ (BV w a) = pure [ testBit a n | n <- [w' - 1, w' - 2 .. 0] ]
    where
      w' = fromInteger w

  joinWord _ (BV i x) (BV j y) =
    pure $! BV (i + j) (shiftL x (fromInteger j) + y)

  splitWord _ leftW rightW (BV _ x) =
    pure ( BV leftW (x `shiftR` (fromInteger rightW)), mkBv rightW x )

  extractWord _ n i (BV _ x) = pure $! mkBv n (x `shiftR` (fromInteger i))

  wordPlus _ (BV i x) (BV j y)
    | i == j = pure $! mkBv i (x+y)
    | otherwise = panic "Attempt to add words of different sizes: wordPlus" []

  wordMinus _ (BV i x) (BV j y)
    | i == j = pure $! mkBv i (x-y)
    | otherwise = panic "Attempt to subtract words of different sizes: wordMinus" []

  wordMult _ (BV i x) (BV j y)
    | i == j = pure $! mkBv i (x*y)
    | otherwise = panic "Attempt to multiply words of different sizes: wordMult" []

  intPlus  _ x y = pure $! x + y
  intMinus _ x y = pure $! x - y
  intMult  _ x y = pure $! x * y

  intModPlus  _ m x y = pure $! ((x + y) `mod` m)
  intModMinus _ m x y = pure $! ((x - y) `mod` m)
  intModMult  _ m x y = pure $! ((x * y) `mod` m)

  wordToInt _ (BV _ x) = pure x
  wordFromInt _ w x = pure $! mkBv w x

-- Value Constructors ----------------------------------------------------------

-- | Create a packed word of n bits.
word :: BitWord sym => sym -> Integer -> Integer -> GenValue sym
word sym n i
  | n >= Arch.maxBigIntWidth = wordTooWide n
  | otherwise                = VWord n (WordVal <$> io (wordLit sym n i))


lam :: (Eval (GenValue sym) -> Eval (GenValue sym)) -> GenValue sym
lam  = VFun

-- | Functions that assume word inputs
wlam :: BitWord sym => sym -> (SWord sym -> Eval (GenValue sym)) -> GenValue sym
wlam sym f = VFun (\arg -> arg >>= fromVWord sym "wlam" >>= f)

-- | A type lambda that expects a 'Type'.
tlam :: (TValue -> GenValue sym) -> GenValue sym
tlam f = VPoly (return . f)

-- | A type lambda that expects a 'Type' of kind #.
nlam :: (Nat' -> GenValue sym) -> GenValue sym
nlam f = VNumPoly (return . f)

-- | Generate a stream.
toStream :: [GenValue sym] -> Eval (GenValue sym)
toStream vs =
   VStream <$> infiniteSeqMap (map ready vs)

toFinSeq ::
  BitWord sym =>
  sym -> Integer -> TValue -> [GenValue sym] -> GenValue sym
toFinSeq sym len elty vs
   | isTBit elty = VWord len (WordVal <$> io (packWord sym (map fromVBit vs)))
   | otherwise   = VSeq len $ finiteSeqMap (map ready vs)

-- | This is strict!
boolToWord :: [Bool] -> Value
boolToWord bs = VWord (genericLength bs) (WordVal <$> io (packWord () bs))

-- | Construct either a finite sequence, or a stream.  In the finite case,
-- record whether or not the elements were bits, to aid pretty-printing.
toSeq ::
  BitWord sym =>
  sym -> Nat' -> TValue -> [GenValue sym] -> Eval (GenValue sym)
toSeq sym len elty vals = case len of
  Nat n -> return $ toFinSeq sym n elty vals
  Inf   -> toStream vals


-- | Construct either a finite sequence, or a stream.  In the finite case,
-- record whether or not the elements were bits, to aid pretty-printing.
mkSeq :: Nat' -> TValue -> SeqMap sym -> GenValue sym
mkSeq len elty vals = case len of
  Nat n
    | isTBit elty -> VWord n $ return $ LargeBitsVal n vals
    | otherwise   -> VSeq n vals
  Inf             -> VStream vals


-- Value Destructors -----------------------------------------------------------

-- | Extract a bit value.
fromVBit :: GenValue sym -> SBit sym
fromVBit val = case val of
  VBit b -> b
  _      -> evalPanic "fromVBit" ["not a Bit"]

-- | Extract an integer value.
fromVInteger :: GenValue sym -> SInteger sym
fromVInteger val = case val of
  VInteger i -> i
  _      -> evalPanic "fromVInteger" ["not an Integer"]

-- | Extract a finite sequence value.
fromVSeq :: GenValue sym -> SeqMap sym
fromVSeq val = case val of
  VSeq _ vs -> vs
  _         -> evalPanic "fromVSeq" ["not a sequence"]

-- | Extract a sequence.
fromSeq :: BitWord sym => String -> GenValue sym -> Eval (SeqMap sym)
fromSeq msg val = case val of
  VSeq _ vs   -> return vs
  VStream vs  -> return vs
  _           -> evalPanic "fromSeq" ["not a sequence", msg]

fromStr :: Value -> Eval String
fromStr (VSeq n vals) =
  traverse (\x -> toEnum . fromInteger <$> (fromWord "fromStr" =<< x)) (enumerateSeqMap n vals)
fromStr _ = evalPanic "fromStr" ["Not a finite sequence"]

fromBit :: GenValue sym -> Eval (SBit sym)
fromBit (VBit b) = return b
fromBit _ = evalPanic "fromBit" ["Not a bit value"]

fromWordVal :: String -> GenValue sym -> Eval (WordValue sym)
fromWordVal _msg (VWord _ wval) = wval
fromWordVal msg _ = evalPanic "fromWordVal" ["not a word value", msg]

-- | Extract a packed word.
fromVWord :: BitWord sym => sym -> String -> GenValue sym -> Eval (SWord sym)
fromVWord sym _msg (VWord _ wval) = wval >>= asWordVal sym
fromVWord _ msg _ = evalPanic "fromVWord" ["not a word", msg]

vWordLen :: BitWord sym => GenValue sym -> Maybe Integer
vWordLen val = case val of
  VWord n _wv              -> Just n
  _                        -> Nothing

-- | If the given list of values are all fully-evaluated thunks
--   containing bits, return a packed word built from the same bits.
--   However, if any value is not a fully-evaluated bit, return 'Nothing'.
tryFromBits :: BitWord sym => sym -> [Eval (GenValue sym)] -> Maybe (IO (SWord sym))
tryFromBits sym = go id
  where
  go f [] = Just (packWord sym (f []))
  go f (Ready (VBit b) : vs) = go (f . (b :)) vs
  go _ (_ : _) = Nothing

-- | Turn a value into an integer represented by w bits.
fromWord :: String -> Value -> Eval Integer
fromWord msg val = bvVal <$> fromVWord () msg val

-- | Extract a function from a value.
fromVFun :: GenValue sym -> (Eval (GenValue sym) -> Eval (GenValue sym))
fromVFun val = case val of
  VFun f -> f
  _      -> evalPanic "fromVFun" ["not a function"]

-- | Extract a polymorphic function from a value.
fromVPoly :: GenValue sym -> (TValue -> Eval (GenValue sym))
fromVPoly val = case val of
  VPoly f -> f
  _       -> evalPanic "fromVPoly" ["not a polymorphic value"]

-- | Extract a polymorphic function from a value.
fromVNumPoly :: GenValue sym -> (Nat' -> Eval (GenValue sym))
fromVNumPoly val = case val of
  VNumPoly f -> f
  _          -> evalPanic "fromVNumPoly" ["not a polymorphic value"]

-- | Extract a tuple from a value.
fromVTuple :: GenValue sym -> [Eval (GenValue sym)]
fromVTuple val = case val of
  VTuple vs -> vs
  _         -> evalPanic "fromVTuple" ["not a tuple"]

-- | Extract a record from a value.
fromVRecord :: GenValue sym -> Map Ident (Eval (GenValue sym))
fromVRecord val = case val of
  VRecord fs -> fs
  _          -> evalPanic "fromVRecord" ["not a record"]

-- | Lookup a field in a record.
lookupRecord :: Ident -> GenValue sym -> Eval (GenValue sym)
lookupRecord f val =
  case Map.lookup f (fromVRecord val) of
    Just x  -> x
    Nothing -> evalPanic "lookupRecord" ["malformed record"]

-- Value to Expression conversion ----------------------------------------------

-- | Given an expected type, returns an expression that evaluates to
-- this value, if we can determine it.
--
-- XXX: View patterns would probably clean up this definition a lot.
toExpr :: PrimMap -> AST.Type -> Value -> Eval (Maybe Expr)
toExpr prims t0 v0 = findOne (go t0 v0)
  where

  prim n = ePrim prims (mkIdent (T.pack n))

  go :: AST.Type -> Value -> ChoiceT Eval Expr
  go ty val = case (tNoUser ty, val) of
    (TRec tfs, VRecord vfs) -> do
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
      BV w v <- lift (asWordVal () =<< wval)
      guard (a == tNum w)
      return $ ETApp (ETApp (prim "number") (tNum v)) ty
    (_, VStream _) -> fail "cannot construct infinite expressions"
    (_, VFun    _) -> fail "cannot convert function values to expressions"
    (_, VPoly   _) -> fail "cannot convert polymorphic values to expressions"
    _ -> do doc <- lift (ppValue () defaultPPOpts val)
            panic "Cryptol.Eval.Value.toExpr"
             ["type mismatch:"
             , pretty ty
             , render doc
             ]
