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
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Cryptol.Eval.Value
  ( -- * GenericValue
    GenValue(..)
  , forceWordValue
  , forceValue
  , Backend(..)
  , asciiMode
    -- ** Value introduction operations
  , word
  , lam
  , wlam
  , flam
  , tlam
  , nlam
  , ilam
  , toStream
  , toFinSeq
  , toSeq
  , mkSeq
    -- ** Value eliminators
  , fromVBit
  , fromVInteger
  , fromVRational
  , fromVFloat
  , fromVSeq
  , fromSeq
  , fromWordVal
  , asIndex
  , fromVWord
  , vWordLen
  , tryFromBits
  , fromVFun
  , fromVPoly
  , fromVNumPoly
  , fromVTuple
  , fromVRecord
  , lookupRecord
    -- ** Pretty printing
  , defaultPPOpts
  , ppValue

    -- * Sequence Maps
  , SeqMap (..)
  , lookupSeqMap
  , finiteSeqMap
  , infiniteSeqMap
  , enumerateSeqMap
  , streamSeqMap
  , reverseSeqMap
  , updateSeqMap
  , dropSeqMap
  , concatSeqMap
  , splitSeqMap
  , memoMap
  , zipSeqMap
  , mapSeqMap
  , largeBitSize
    -- * WordValue
  , WordValue(..)
  , asWordVal
  , asBitsMap
  , enumerateWordValue
  , enumerateWordValueRev
  , wordValueSize
  , indexWordValue
  , updateWordValue
  ) where

import Control.Monad.IO.Class
import Data.Bits
import Data.IORef
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import MonadLib

import Cryptol.Backend
import qualified Cryptol.Backend.Arch as Arch
import Cryptol.Backend.Monad ( PPOpts(..), evalPanic, wordTooWide, defaultPPOpts, asciiMode )
import Cryptol.Eval.Type

import Cryptol.TypeCheck.Solver.InfNat(Nat'(..))
import Cryptol.Utils.Ident (Ident)
import Cryptol.Utils.Panic(panic)
import Cryptol.Utils.PP
import Cryptol.Utils.RecordMap

import Data.List(genericIndex)

import GHC.Generics (Generic)

-- Values ----------------------------------------------------------------------

-- | A sequence map represents a mapping from nonnegative integer indices
--   to values.  These are used to represent both finite and infinite sequences.
data SeqMap sym
  = IndexSeqMap  !(Integer -> SEval sym (GenValue sym))
  | UpdateSeqMap !(Map Integer (SEval sym (GenValue sym)))
                 !(Integer -> SEval sym (GenValue sym))

lookupSeqMap :: SeqMap sym -> Integer -> SEval sym (GenValue sym)
lookupSeqMap (IndexSeqMap f) i = f i
lookupSeqMap (UpdateSeqMap m f) i =
  case Map.lookup i m of
    Just x  -> x
    Nothing -> f i

-- | An arbitrarily-chosen number of elements where we switch from a dense
--   sequence representation of bit-level words to 'SeqMap' representation.
largeBitSize :: Integer
largeBitSize = 1 `shiftL` 48

-- | Generate a finite sequence map from a list of values
finiteSeqMap :: Backend sym => sym -> [SEval sym (GenValue sym)] -> SeqMap sym
finiteSeqMap sym xs =
   UpdateSeqMap
      (Map.fromList (zip [0..] xs))
      (invalidIndex sym)

-- | Generate an infinite sequence map from a stream of values
infiniteSeqMap :: Backend sym => [SEval sym (GenValue sym)] -> SEval sym (SeqMap sym)
infiniteSeqMap xs =
   -- TODO: use an int-trie?
   memoMap (IndexSeqMap $ \i -> genericIndex xs i)

-- | Create a finite list of length @n@ of the values from @[0..n-1]@ in
--   the given the sequence emap.
enumerateSeqMap :: (Integral n) => n -> SeqMap sym -> [SEval sym (GenValue sym)]
enumerateSeqMap n m = [ lookupSeqMap m i | i <- [0 .. (toInteger n)-1] ]

-- | Create an infinite stream of all the values in a sequence map
streamSeqMap :: SeqMap sym -> [SEval sym (GenValue sym)]
streamSeqMap m = [ lookupSeqMap m i | i <- [0..] ]

-- | Reverse the order of a finite sequence map
reverseSeqMap :: Integer     -- ^ Size of the sequence map
              -> SeqMap sym
              -> SeqMap sym
reverseSeqMap n vals = IndexSeqMap $ \i -> lookupSeqMap vals (n - 1 - i)

updateSeqMap :: SeqMap sym -> Integer -> SEval sym (GenValue sym) -> SeqMap sym
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
memoMap :: (MonadIO m, Backend sym) => SeqMap sym -> m (SeqMap sym)
memoMap x = do
  cache <- liftIO $ newIORef $ Map.empty
  return $ IndexSeqMap (memo cache)

  where
  memo cache i = do
    mz <- liftIO (Map.lookup i <$> readIORef cache)
    case mz of
      Just z  -> return z
      Nothing -> doEval cache i

  doEval cache i = do
    v <- lookupSeqMap x i
    liftIO $ atomicModifyIORef' cache (\m -> (Map.insert i v m, ()))
    return v

-- | Apply the given evaluation function pointwise to the two given
--   sequence maps.
zipSeqMap ::
  Backend sym =>
  (GenValue sym -> GenValue sym -> SEval sym (GenValue sym)) ->
  SeqMap sym ->
  SeqMap sym ->
  SEval sym (SeqMap sym)
zipSeqMap f x y =
  memoMap (IndexSeqMap $ \i -> join (f <$> lookupSeqMap x i <*> lookupSeqMap y i))

-- | Apply the given function to each value in the given sequence map
mapSeqMap ::
  Backend sym =>
  (GenValue sym -> SEval sym (GenValue sym)) ->
  SeqMap sym -> SEval sym (SeqMap sym)
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
asWordVal :: Backend sym => sym -> WordValue sym -> SEval sym (SWord sym)
asWordVal _   (WordVal w)         = return w
asWordVal sym (LargeBitsVal n xs) = packWord sym =<< traverse (fromVBit <$>) (enumerateSeqMap n xs)

-- | Force a word value into a sequence of bits
asBitsMap :: Backend sym => sym -> WordValue sym -> SeqMap sym
asBitsMap sym (WordVal w)  = IndexSeqMap $ \i -> VBit <$> (wordBit sym w i)
asBitsMap _   (LargeBitsVal _ xs) = xs

-- | Turn a word value into a sequence of bits, forcing each bit.
--   The sequence is returned in big-endian order.
enumerateWordValue :: Backend sym => sym -> WordValue sym -> SEval sym [SBit sym]
enumerateWordValue sym (WordVal w) = unpackWord sym w
enumerateWordValue _ (LargeBitsVal n xs) = traverse (fromVBit <$>) (enumerateSeqMap n xs)

-- | Turn a word value into a sequence of bits, forcing each bit.
--   The sequence is returned in reverse of the usual order, which is little-endian order.
enumerateWordValueRev :: Backend sym => sym -> WordValue sym -> SEval sym [SBit sym]
enumerateWordValueRev sym (WordVal w)  = reverse <$> unpackWord sym w
enumerateWordValueRev _   (LargeBitsVal n xs) = traverse (fromVBit <$>) (enumerateSeqMap n (reverseSeqMap n xs))

-- | Compute the size of a word value
wordValueSize :: Backend sym => sym -> WordValue sym -> Integer
wordValueSize sym (WordVal w)  = wordLen sym w
wordValueSize _ (LargeBitsVal n _) = n

-- | Select an individual bit from a word value
indexWordValue :: Backend sym => sym -> WordValue sym -> Integer -> SEval sym (SBit sym)
indexWordValue sym (WordVal w) idx
   | 0 <= idx && idx < wordLen sym w = wordBit sym w idx
   | otherwise = invalidIndex sym idx
indexWordValue sym (LargeBitsVal n xs) idx
   | 0 <= idx && idx < n = fromVBit <$> lookupSeqMap xs idx
   | otherwise = invalidIndex sym idx

-- | Produce a new 'WordValue' from the one given by updating the @i@th bit with the
--   given bit value.
updateWordValue :: Backend sym => sym -> WordValue sym -> Integer -> SEval sym (SBit sym) -> SEval sym (WordValue sym)
updateWordValue sym (WordVal w) idx b
   | idx < 0 || idx >= wordLen sym w = invalidIndex sym idx
   | isReady sym b = WordVal <$> (wordUpdate sym w idx =<< b)

updateWordValue sym wv idx b
   | 0 <= idx && idx < wordValueSize sym wv =
        pure $ LargeBitsVal (wordValueSize sym wv) $ updateSeqMap (asBitsMap sym wv) idx (VBit <$> b)
   | otherwise = invalidIndex sym idx


-- | Generic value type, parameterized by bit and word types.
--
--   NOTE: we maintain an important invariant regarding sequence types.
--   'VSeq' must never be used for finite sequences of bits.
--   Always use the 'VWord' constructor instead!  Infinite sequences of bits
--   are handled by the 'VStream' constructor, just as for other types.
data GenValue sym
  = VRecord !(RecordMap Ident (SEval sym (GenValue sym))) -- ^ @ { .. } @
  | VTuple ![SEval sym (GenValue sym)]              -- ^ @ ( .. ) @
  | VBit !(SBit sym)                           -- ^ @ Bit    @
  | VInteger !(SInteger sym)                   -- ^ @ Integer @ or @ Z n @
  | VRational !(SRational sym)                 -- ^ @ Rational @
  | VFloat !(SFloat sym)
  | VSeq !Integer !(SeqMap sym)                -- ^ @ [n]a   @
                                               --   Invariant: VSeq is never a sequence of bits
  | VWord !Integer !(SEval sym (WordValue sym))  -- ^ @ [n]Bit @
  | VStream !(SeqMap sym)                   -- ^ @ [inf]a @
  | VFun (SEval sym (GenValue sym) -> SEval sym (GenValue sym)) -- ^ functions
  | VPoly (TValue -> SEval sym (GenValue sym))   -- ^ polymorphic values (kind *)
  | VNumPoly (Nat' -> SEval sym (GenValue sym))  -- ^ polymorphic values (kind #)
 deriving Generic


-- | Force the evaluation of a word value
forceWordValue :: Backend sym => WordValue sym -> SEval sym ()
forceWordValue (WordVal w)  = seq w (return ())
forceWordValue (LargeBitsVal n xs) = mapM_ (\x -> const () <$> x) (enumerateSeqMap n xs)

-- | Force the evaluation of a value
forceValue :: Backend sym => GenValue sym -> SEval sym ()
forceValue v = case v of
  VRecord fs  -> mapM_ (forceValue =<<) fs
  VTuple xs   -> mapM_ (forceValue =<<) xs
  VSeq n xs   -> mapM_ (forceValue =<<) (enumerateSeqMap n xs)
  VBit b      -> seq b (return ())
  VInteger i  -> seq i (return ())
  VRational q -> seq q (return ())
  VFloat f    -> seq f (return ())
  VWord _ wv  -> forceWordValue =<< wv
  VStream _   -> return ()
  VFun _      -> return ()
  VPoly _     -> return ()
  VNumPoly _  -> return ()



instance Backend sym => Show (GenValue sym) where
  show v = case v of
    VRecord fs -> "record:" ++ show (displayOrder fs)
    VTuple xs  -> "tuple:" ++ show (length xs)
    VBit _     -> "bit"
    VInteger _ -> "integer"
    VRational _ -> "rational"
    VFloat _   -> "float"
    VSeq n _   -> "seq:" ++ show n
    VWord n _  -> "word:"  ++ show n
    VStream _  -> "stream"
    VFun _     -> "fun"
    VPoly _    -> "poly"
    VNumPoly _ -> "numpoly"


-- Pretty Printing -------------------------------------------------------------

ppValue :: forall sym.
  Backend sym =>
  sym ->
  PPOpts ->
  GenValue sym ->
  SEval sym Doc
ppValue x opts = loop
  where
  loop :: GenValue sym -> SEval sym Doc
  loop val = case val of
    VRecord fs         -> do fs' <- traverse (>>= loop) fs
                             return $ braces (sep (punctuate comma (map ppField (displayFields fs'))))
      where
      ppField (f,r) = pp f <+> char '=' <+> r
    VTuple vals        -> do vals' <- traverse (>>=loop) vals
                             return $ parens (sep (punctuate comma vals'))
    VBit b             -> return $ ppBit x b
    VInteger i         -> return $ ppInteger x opts i
    VRational q        -> return $ ppRational x opts q
    VFloat i           -> return $ ppFloat x opts i
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

  ppWordVal :: WordValue sym -> SEval sym Doc
  ppWordVal w = ppWord x opts <$> asWordVal x w

  ppWordSeq :: Integer -> SeqMap sym -> SEval sym Doc
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


-- Value Constructors ----------------------------------------------------------

-- | Create a packed word of n bits.
word :: Backend sym => sym -> Integer -> Integer -> GenValue sym
word sym n i
  | n >= Arch.maxBigIntWidth = wordTooWide n
  | otherwise                = VWord n (WordVal <$> wordLit sym n i)


lam :: (SEval sym (GenValue sym) -> SEval sym (GenValue sym)) -> GenValue sym
lam  = VFun

-- | Functions that assume word inputs
wlam :: Backend sym => sym -> (SWord sym -> SEval sym (GenValue sym)) -> GenValue sym
wlam sym f = VFun (\arg -> arg >>= fromVWord sym "wlam" >>= f)

-- | Functions that assume floating point inputs
flam :: Backend sym =>
        (SFloat sym -> SEval sym (GenValue sym)) -> GenValue sym
flam f = VFun (\arg -> arg >>= f . fromVFloat)



-- | A type lambda that expects a 'Type'.
tlam :: Backend sym => (TValue -> GenValue sym) -> GenValue sym
tlam f = VPoly (return . f)

-- | A type lambda that expects a 'Type' of kind #.
nlam :: Backend sym => (Nat' -> GenValue sym) -> GenValue sym
nlam f = VNumPoly (return . f)

-- | A type lambda that expects a finite numeric type.
ilam :: Backend sym => (Integer -> GenValue sym) -> GenValue sym
ilam f = nlam (\n -> case n of
                       Nat i -> f i
                       Inf   -> panic "ilam" [ "Unexpected `inf`" ])

-- | Generate a stream.
toStream :: Backend sym => [GenValue sym] -> SEval sym (GenValue sym)
toStream vs =
   VStream <$> infiniteSeqMap (map pure vs)

toFinSeq ::
  Backend sym =>
  sym -> Integer -> TValue -> [GenValue sym] -> GenValue sym
toFinSeq sym len elty vs
   | isTBit elty = VWord len (WordVal <$> packWord sym (map fromVBit vs))
   | otherwise   = VSeq len $ finiteSeqMap sym (map pure vs)

-- | Construct either a finite sequence, or a stream.  In the finite case,
-- record whether or not the elements were bits, to aid pretty-printing.
toSeq ::
  Backend sym =>
  sym -> Nat' -> TValue -> [GenValue sym] -> SEval sym (GenValue sym)
toSeq sym len elty vals = case len of
  Nat n -> return $ toFinSeq sym n elty vals
  Inf   -> toStream vals


-- | Construct either a finite sequence, or a stream.  In the finite case,
-- record whether or not the elements were bits, to aid pretty-printing.
mkSeq :: Backend sym => Nat' -> TValue -> SeqMap sym -> GenValue sym
mkSeq len elty vals = case len of
  Nat n
    | isTBit elty -> VWord n $ pure $ LargeBitsVal n vals
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

-- | Extract a rational value.
fromVRational :: GenValue sym -> SRational sym
fromVRational val = case val of
  VRational q -> q
  _      -> evalPanic "fromVRational" ["not a Rational"]

-- | Extract a finite sequence value.
fromVSeq :: GenValue sym -> SeqMap sym
fromVSeq val = case val of
  VSeq _ vs -> vs
  _         -> evalPanic "fromVSeq" ["not a sequence"]

-- | Extract a sequence.
fromSeq :: Backend sym => String -> GenValue sym -> SEval sym (SeqMap sym)
fromSeq msg val = case val of
  VSeq _ vs   -> return vs
  VStream vs  -> return vs
  _           -> evalPanic "fromSeq" ["not a sequence", msg]

fromWordVal :: Backend sym => String -> GenValue sym -> SEval sym (WordValue sym)
fromWordVal _msg (VWord _ wval) = wval
fromWordVal msg _ = evalPanic "fromWordVal" ["not a word value", msg]

asIndex :: Backend sym =>
  sym -> String -> TValue -> GenValue sym -> SEval sym (Either (SInteger sym) (WordValue sym))
asIndex _sym _msg TVInteger (VInteger i) = pure (Left i)
asIndex _sym _msg _ (VWord _ wval) = Right <$> wval
asIndex _sym  msg _ _ = evalPanic "asIndex" ["not an index value", msg]

-- | Extract a packed word.
fromVWord :: Backend sym => sym -> String -> GenValue sym -> SEval sym (SWord sym)
fromVWord sym _msg (VWord _ wval) = wval >>= asWordVal sym
fromVWord _ msg _ = evalPanic "fromVWord" ["not a word", msg]

vWordLen :: Backend sym => GenValue sym -> Maybe Integer
vWordLen val = case val of
  VWord n _wv              -> Just n
  _                        -> Nothing

-- | If the given list of values are all fully-evaluated thunks
--   containing bits, return a packed word built from the same bits.
--   However, if any value is not a fully-evaluated bit, return 'Nothing'.
tryFromBits :: Backend sym => sym -> [SEval sym (GenValue sym)] -> Maybe (SEval sym (SWord sym))
tryFromBits sym = go id
  where
  go f [] = Just (packWord sym =<< sequence (f []))
  go f (v : vs) | isReady sym v = go (f . ((fromVBit <$> v):)) vs
  go _ (_ : _) = Nothing

-- | Extract a function from a value.
fromVFun :: GenValue sym -> (SEval sym (GenValue sym) -> SEval sym (GenValue sym))
fromVFun val = case val of
  VFun f -> f
  _      -> evalPanic "fromVFun" ["not a function"]

-- | Extract a polymorphic function from a value.
fromVPoly :: GenValue sym -> (TValue -> SEval sym (GenValue sym))
fromVPoly val = case val of
  VPoly f -> f
  _       -> evalPanic "fromVPoly" ["not a polymorphic value"]

-- | Extract a polymorphic function from a value.
fromVNumPoly :: GenValue sym -> (Nat' -> SEval sym (GenValue sym))
fromVNumPoly val = case val of
  VNumPoly f -> f
  _          -> evalPanic "fromVNumPoly" ["not a polymorphic value"]

-- | Extract a tuple from a value.
fromVTuple :: GenValue sym -> [SEval sym (GenValue sym)]
fromVTuple val = case val of
  VTuple vs -> vs
  _         -> evalPanic "fromVTuple" ["not a tuple"]

-- | Extract a record from a value.
fromVRecord :: GenValue sym -> RecordMap Ident (SEval sym (GenValue sym))
fromVRecord val = case val of
  VRecord fs -> fs
  _          -> evalPanic "fromVRecord" ["not a record"]

fromVFloat :: GenValue sym -> SFloat sym
fromVFloat val =
  case val of
    VFloat x -> x
    _        -> evalPanic "fromVFloat" ["not a Float"]

-- | Lookup a field in a record.
lookupRecord :: Ident -> GenValue sym -> SEval sym (GenValue sym)
lookupRecord f val =
  case lookupField f (fromVRecord val) of
    Just x  -> x
    Nothing -> evalPanic "lookupRecord" ["malformed record"]
