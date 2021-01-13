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

  , EvalOpts(..)
    -- ** Value introduction operations
  , word
  , lam
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
  , fromVGen
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

import Data.Bits
import Data.Ratio
import Numeric (showIntAtBase)

import Cryptol.Backend
import qualified Cryptol.Backend.Arch as Arch
import Cryptol.Backend.Monad
  ( evalPanic, wordTooWide, CallStack, combineCallStacks )
import Cryptol.Backend.FloatHelpers (fpPP)
import Cryptol.Eval.Type

import Cryptol.TypeCheck.Solver.InfNat(Nat'(..))
import Cryptol.Utils.Ident (Ident)
import Cryptol.Utils.Logger(Logger)
import Cryptol.Utils.Panic(panic)
import Cryptol.Utils.PP
import Cryptol.Utils.RecordMap

import GHC.Generics (Generic)

-- | Some options for evalutaion
data EvalOpts = EvalOpts
  { evalLogger :: Logger    -- ^ Where to print stuff (e.g., for @trace@)
  , evalPPOpts :: PPOpts    -- ^ How to pretty print things.
  }


-- Values ----------------------------------------------------------------------

-- | An arbitrarily-chosen number of elements where we switch from a dense
--   sequence representation of bit-level words to 'SeqMap' representation.
largeBitSize :: Integer
largeBitSize = 1 `shiftL` 48


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
  | LargeBitsVal !Integer !(SeqMap sym (GenValue sym))
       -- ^ A large bitvector sequence, represented as a
       --   'SeqMap' of bits.
 deriving (Generic)

-- | Force a word value into packed word form
asWordVal :: Backend sym => sym -> WordValue sym -> SEval sym (SWord sym)
asWordVal _   (WordVal w)         = return w
asWordVal sym (LargeBitsVal n xs) = packWord sym =<< traverse (fromVBit <$>) (enumerateSeqMap n xs)

-- | Force a word value into a sequence of bits
asBitsMap :: Backend sym => sym -> WordValue sym -> SeqMap sym (GenValue sym)
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
updateWordValue :: Backend sym =>
  sym -> WordValue sym -> Integer -> SEval sym (SBit sym) -> SEval sym (WordValue sym)
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
  | VSeq !Integer !(SeqMap sym (GenValue sym)) -- ^ @ [n]a   @
                                               --   Invariant: VSeq is never a sequence of bits
  | VWord !Integer !(SEval sym (WordValue sym))  -- ^ @ [n]Bit @
  | VStream !(SeqMap sym (GenValue sym))       -- ^ @ [inf]a @
  | VGen  !(SGen sym (GenValue sym))           -- ^ @ Gen a @
  | VFun  CallStack (SEval sym (GenValue sym) -> SEval sym (GenValue sym)) -- ^ functions
  | VPoly CallStack (TValue -> SEval sym (GenValue sym))   -- ^ polymorphic values (kind *)
  | VNumPoly CallStack (Nat' -> SEval sym (GenValue sym))  -- ^ polymorphic values (kind #)
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
  VGen{}      -> return ()
  VFun{}      -> return ()
  VPoly{}     -> return ()
  VNumPoly{}  -> return ()



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
    VGen{}     -> "generator"
    VFun{}     -> "fun"
    VPoly{}    -> "poly"
    VNumPoly{} -> "numpoly"


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
    VBit b             -> ppSBit x b
    VInteger i         -> ppSInteger x i
    VRational q        -> ppSRational x q
    VFloat i           -> ppSFloat x opts i
    VSeq sz vals       -> ppWordSeq sz vals
    VWord _ wv         -> ppWordVal =<< wv
    VStream vals       -> do vals' <- traverse (>>=loop) $ enumerateSeqMap (useInfLength opts) vals
                             return $ brackets $ fsep
                                   $ punctuate comma
                                   ( vals' ++ [text "..."]
                                   )
    VGen{}             -> return $ text "<random generator>"
    VFun{}             -> return $ text "<function>"
    VPoly{}            -> return $ text "<polymorphic value>"
    VNumPoly{}         -> return $ text "<polymorphic value>"

  ppWordVal :: WordValue sym -> SEval sym Doc
  ppWordVal w = ppSWord x opts =<< asWordVal x w

  ppWordSeq :: Integer -> SeqMap sym (GenValue sym) -> SEval sym Doc
  ppWordSeq sz vals = do
    ws <- sequence (enumerateSeqMap sz vals)
    case ws of
      w : _
        | Just l <- vWordLen w
        , asciiMode opts l
        -> do vs <- traverse (fromVWord x "ppWordSeq") ws
              case traverse (wordAsChar x) vs of
                Just str -> return $ text (show str)
                _ -> do vs' <- mapM (ppSWord x opts) vs
                        return $ brackets (fsep (punctuate comma vs'))
      _ -> do ws' <- traverse loop ws
              return $ brackets (fsep (punctuate comma ws'))

ppSBit :: Backend sym => sym -> SBit sym -> SEval sym Doc
ppSBit sym b =
  case bitAsLit sym b of
    Just True  -> pure (text "True")
    Just False -> pure (text "False")
    Nothing    -> pure (text "?")

ppSInteger :: Backend sym => sym -> SInteger sym -> SEval sym Doc
ppSInteger sym x =
  case integerAsLit sym x of
    Just i  -> pure (integer i)
    Nothing -> pure (text "[?]")

ppSFloat :: Backend sym => sym -> PPOpts -> SFloat sym -> SEval sym Doc
ppSFloat sym opts x =
  case fpAsLit sym x of
    Just fp -> pure (fpPP opts fp)
    Nothing -> pure (text "[?]")

ppSRational :: Backend sym => sym -> SRational sym -> SEval sym Doc
ppSRational sym (SRational n d)
  | Just ni <- integerAsLit sym n
  , Just di <- integerAsLit sym d
  = let q = ni % di in
      pure (text "(ratio" <+> integer (numerator q) <+> (integer (denominator q) <> text ")"))

  | otherwise
  = do n' <- ppSInteger sym n
       d' <- ppSInteger sym d
       pure (text "(ratio" <+> n' <+> (d' <> text ")"))

ppSWord :: Backend sym => sym -> PPOpts -> SWord sym -> SEval sym Doc
ppSWord sym opts bv
  | asciiMode opts width =
      case wordAsLit sym bv of
        Just (_,i) -> pure (text (show (toEnum (fromInteger i) :: Char)))
        Nothing    -> pure (text "?")

  | otherwise =
      case wordAsLit sym bv of
        Just (_,i) ->
          let val = value i in
          pure (prefix (length val) <.> text val)
        Nothing
          | base == 2  -> sliceDigits 1 "0b"
          | base == 8  -> sliceDigits 3 "0o"
          | base == 16 -> sliceDigits 4 "0x"
          | otherwise  -> pure (text "[?]")

  where
  width = wordLen sym bv

  base = if useBase opts > 36 then 10 else useBase opts

  padding bitsPerDigit len = text (replicate padLen '0')
    where
    padLen | m > 0     = d + 1
           | otherwise = d

    (d,m) = (fromInteger width - (len * bitsPerDigit))
                   `divMod` bitsPerDigit

  prefix len = case base of
    2  -> text "0b" <.> padding 1 len
    8  -> text "0o" <.> padding 3 len
    10 -> empty
    16 -> text "0x" <.> padding 4 len
    _  -> text "0"  <.> char '<' <.> int base <.> char '>'

  value i = showIntAtBase (toInteger base) (digits !!) i ""
  digits  = "0123456789abcdefghijklmnopqrstuvwxyz"

  toDigit w =
    case wordAsLit sym w of
      Just (_,i) | i <= 36 -> digits !! fromInteger i
      _ -> '?'

  sliceDigits bits pfx =
    do ws <- goDigits bits [] bv
       let ds = map toDigit ws
       pure (text pfx <.> text ds)

  goDigits bits ds w
    | wordLen sym w > bits =
        do (hi,lo) <- splitWord sym (wordLen sym w - bits) bits w
           goDigits bits (lo:ds) hi

    | wordLen sym w > 0 = pure (w:ds)

    | otherwise          = pure ds

-- Value Constructors ----------------------------------------------------------

-- | Create a packed word of n bits.
word :: Backend sym => sym -> Integer -> Integer -> GenValue sym
word sym n i
  | n >= Arch.maxBigIntWidth = wordTooWide n
  | otherwise                = VWord n (WordVal <$> wordLit sym n i)


-- | Construct a function value
lam :: Backend sym => sym -> (SEval sym (GenValue sym) -> SEval sym (GenValue sym)) -> SEval sym (GenValue sym)
lam sym f = VFun <$> sGetCallStack sym <*> pure f

-- | Functions that assume floating point inputs
flam :: Backend sym => sym ->
        (SFloat sym -> SEval sym (GenValue sym)) -> SEval sym (GenValue sym)
flam sym f = VFun <$> sGetCallStack sym <*> pure (\arg -> arg >>= f . fromVFloat)

-- | A type lambda that expects a 'Type'.
tlam :: Backend sym => sym -> (TValue -> SEval sym (GenValue sym)) -> SEval sym (GenValue sym)
tlam sym f = VPoly <$> sGetCallStack sym <*> pure f

-- | A type lambda that expects a 'Type' of kind #.
nlam :: Backend sym => sym -> (Nat' -> SEval sym (GenValue sym)) -> SEval sym (GenValue sym)
nlam sym f = VNumPoly <$> sGetCallStack sym <*> pure f

-- | A type lambda that expects a finite numeric type.
ilam :: Backend sym => sym -> (Integer -> SEval sym (GenValue sym)) -> SEval sym (GenValue sym)
ilam sym f =
   nlam sym (\n -> case n of
                     Nat i -> f i
                     Inf   -> panic "ilam" [ "Unexpected `inf`" ])

-- | Generate a stream.
toStream :: Backend sym => sym -> [GenValue sym] -> SEval sym (GenValue sym)
toStream sym vs =
   VStream <$> infiniteSeqMap sym (map pure vs)

toFinSeq ::
  Backend sym =>
  sym -> Integer -> TValue -> [GenValue sym] -> GenValue sym
toFinSeq sym len elty vs
   | isTBit elty = VWord len (WordVal <$> packWord sym (map fromVBit vs))
   | otherwise   = VSeq len $ finiteSeqMap (map pure vs)

-- | Construct either a finite sequence, or a stream.  In the finite case,
-- record whether or not the elements were bits, to aid pretty-printing.
toSeq ::
  Backend sym =>
  sym -> Nat' -> TValue -> [GenValue sym] -> SEval sym (GenValue sym)
toSeq sym len elty vals = case len of
  Nat n -> return $ toFinSeq sym n elty vals
  Inf   -> toStream sym vals


-- | Construct either a finite sequence, or a stream.  In the finite case,
-- record whether or not the elements were bits, to aid pretty-printing.
mkSeq :: Backend sym => Nat' -> TValue -> SeqMap sym (GenValue sym) -> GenValue sym
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
fromVSeq :: GenValue sym -> SeqMap sym (GenValue sym)
fromVSeq val = case val of
  VSeq _ vs -> vs
  _         -> evalPanic "fromVSeq" ["not a sequence"]

fromVGen :: GenValue sym -> SGen sym (GenValue sym)
fromVGen val = case val of
  VGen x -> x
  _      -> evalPanic "fromVGen" ["not a random generator"]

-- | Extract a sequence.
fromSeq :: Backend sym => String -> GenValue sym -> SEval sym (SeqMap sym (GenValue sym))
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
fromVFun :: Backend sym => sym -> GenValue sym -> (SEval sym (GenValue sym) -> SEval sym (GenValue sym))
fromVFun sym val = case val of
  VFun fnstk f ->
    \x -> sModifyCallStack sym (\stk -> combineCallStacks stk fnstk) (f x)
  _ -> evalPanic "fromVFun" ["not a function"]

-- | Extract a polymorphic function from a value.
fromVPoly :: Backend sym => sym -> GenValue sym -> (TValue -> SEval sym (GenValue sym))
fromVPoly sym val = case val of
  VPoly fnstk f ->
    \x -> sModifyCallStack sym (\stk -> combineCallStacks stk fnstk) (f x)
  _ -> evalPanic "fromVPoly" ["not a polymorphic value"]

-- | Extract a polymorphic function from a value.
fromVNumPoly :: Backend sym => sym -> GenValue sym -> (Nat' -> SEval sym (GenValue sym))
fromVNumPoly sym val = case val of
  VNumPoly fnstk f ->
    \x -> sModifyCallStack sym (\stk -> combineCallStacks stk fnstk) (f x)
  _  -> evalPanic "fromVNumPoly" ["not a polymorphic value"]

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
