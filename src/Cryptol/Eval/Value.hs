-- |
-- Module      :  Cryptol.Eval.Value
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE BangPatterns #-}
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
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Cryptol.Eval.Value
  ( -- * GenericValue
    GenValue 
      (VRecord, VTuple
      , VEnum, VBit
      , VInteger, VRational
      , VFloat, VWord
      , VStream, VFun
      , VPoly, VNumPoly
      , VSeq) -- pattern synonym
  , ConValue
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
  , FinSeq
  , toFinSeq
  , unsafeToFinSeq
  , finSeq
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
  , fromVEnum
    -- ** Pretty printing
  , defaultPPOpts
  , ppValue
  , ppValuePrec
    -- * Merge and if/then/else
  , iteValue
  , caseValue, CaseCont(..)
  , mergeValue
  ) where

import Data.Ratio
import Numeric (showIntAtBase)
import Data.Map(Map)
import qualified Data.Map as Map
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IMap
import qualified Data.Vector as Vector

import Cryptol.Backend
import Cryptol.Backend.SeqMap
import qualified Cryptol.Backend.Arch as Arch
import Cryptol.Backend.Monad
  ( evalPanic, wordTooWide, CallStack, combineCallStacks,EvalError(..))
import Cryptol.Backend.FloatHelpers (fpPP)
import Cryptol.Backend.WordValue

import Cryptol.Eval.Type

import Cryptol.TypeCheck.Solver.InfNat(Nat'(..))

import Cryptol.Utils.Ident (Ident,unpackIdent)
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

-- | Generic value type, parameterized by bit and word types.
--
--   NOTE: we maintain an important invariant regarding sequence types.
--   'VSeq' must never be used for finite sequences of bits.
--   Always use the 'VWord' constructor instead!  Infinite sequences of bits
--   are handled by the 'VStream' constructor, just as for other types.
data GenValue sym
  = VRecord !(RecordMap Ident (SEval sym (GenValue sym))) -- ^ @ { .. } @
  | VTuple ![SEval sym (GenValue sym)]              -- ^ @ ( .. ) @
  | VEnum !(SInteger sym) !(IntMap (ConValue sym))
    -- ^ As an example, consider the enum value @Just ()@. The 'SInteger' is the
    -- tag (e.g., 'Just' would have the tag @0@), and the 'IntMap' contains the
    -- fields (e.g., @{ 0 -> ("Just",()) }@. The 'IntMap' is only really needed
    -- to represent symbolic values.
  | VBit !(SBit sym)                           -- ^ @ Bit    @
  | VInteger !(SInteger sym)                   -- ^ @ Integer @ or @ Z n @
  | VRational !(SRational sym)                 -- ^ @ Rational @
  | VFloat !(SFloat sym)
  | VSeqCtor !Integer !(SeqMap sym (GenValue sym)) -- ^ @ [n]a   @
                                                   --   Invariant: VSeqCtor is never a sequence of bits
                                                   --   This constructor is intentionally not exported
                                                   --   to preserve the invariant. Use smart constructors
                                                   --   such as 'mkSeq' or 'finSeq' instead.
  | VWord !(WordValue sym)                     -- ^ @ [n]Bit @
  | VStream !(SeqMap sym (GenValue sym))       -- ^ @ [inf]a @
  | VFun  CallStack (SEval sym (GenValue sym) -> SEval sym (GenValue sym)) -- ^ functions
  | VPoly CallStack (TValue -> SEval sym (GenValue sym))   -- ^ polymorphic values (kind *)
  | VNumPoly CallStack (Nat' -> SEval sym (GenValue sym))  -- ^ polymorphic values (kind #)
 deriving Generic

-- | A view-only pattern for deconstructing finite sequences. Use
--   'mkSeq' or 'finSeq' for construction.
pattern VSeq :: Integer -> SeqMap sym (GenValue sym) -> GenValue sym
pattern VSeq len vals <- VSeqCtor len vals

-- This is all GenValue constructors except for VSeqCtor, which
-- is instead swapped for the view-only VSeq pattern
{-# COMPLETE VRecord, VTuple, VEnum, VBit, VInteger,
             VRational, VFloat, VWord, VStream,
             VFun, VPoly, VNumPoly, VSeq #-}

type ConValue sym = ConInfo (SEval sym (GenValue sym))

-- | Force the evaluation of a value
forceValue :: Backend sym => GenValue sym -> SEval sym ()
forceValue v = case v of
  VRecord fs  -> mapM_ (forceValue =<<) fs
  VTuple xs   -> mapM_ (forceValue =<<) xs
  VEnum i xs  -> seq i (mapM_ forceConValue xs)
  VSeq n xs   -> mapM_ (forceValue =<<) (enumerateSeqMap n xs)
  VBit b      -> seq b (return ())
  VInteger i  -> seq i (return ())
  VRational q -> seq q (return ())
  VFloat f    -> seq f (return ())
  VWord wv    -> forceWordValue wv
  VStream _   -> return ()
  VFun{}      -> return ()
  VPoly{}     -> return ()
  VNumPoly{}  -> return ()

forceConValue :: Backend sym => ConValue sym -> SEval sym ()
forceConValue (ConInfo i vs) = i `seq` mapM_ (forceValue =<<) vs

instance Backend sym => Show (GenValue sym) where
  show v = case v of
    VRecord fs -> "record:" ++ show (displayOrder fs)
    VTuple xs  -> "tuple:" ++ show (length xs)
    VEnum _ _  -> "enum"
    VBit _     -> "bit"
    VInteger _ -> "integer"
    VRational _ -> "rational"
    VFloat _   -> "float"
    VSeq n _   -> "seq:" ++ show n
    VWord wv    -> "word:"  ++ show (wordValWidth wv)
    VStream _  -> "stream"
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
ppValue x opts = ppValuePrec x opts 0

ppValuePrec :: forall sym.
  Backend sym =>
  sym ->
  PPOpts ->
  Int ->
  GenValue sym ->
  SEval sym Doc
ppValuePrec x opts = loop
  where
  loop :: Int -> GenValue sym -> SEval sym Doc
  loop prec val = case val of
    VRecord fs         -> do fs' <- traverse (>>= loop 0) fs
                             return $ ppRecord (map ppField (fields fs'))
      where
      ppField (f,r) = pp f <+> char '=' <+> r
    VTuple vals        -> do vals' <- traverse (>>=loop 0) vals
                             return $ ppTuple vals'
    VEnum c vs         -> ppEnumVal prec c vs
    VBit b             -> ppSBit x b
    VInteger i         -> ppSInteger x i
    VRational q        -> ppSRational x q
    VFloat i           -> ppSFloat x opts i
    VSeq sz vals       -> ppWordSeq sz vals
    VWord wv           -> ppWordVal wv
    VStream vals       -> do vals' <- traverse (>>=loop 0) $ enumerateSeqMap (useInfLength opts) vals
                             return $ ppList ( vals' ++ [text "..."] )
    VFun{}             -> return $ text "<function>"
    VPoly{}            -> return $ text "<polymorphic value>"
    VNumPoly{}         -> return $ text "<polymorphic value>"

  fields :: RecordMap Ident Doc -> [(Ident, Doc)]
  fields = case useFieldOrder opts of
    DisplayOrder -> displayFields
    CanonicalOrder -> canonicalFields

  ppEnumVal prec i mp =
    case integerAsLit x i of
      Just c ->
        case IMap.lookup (fromInteger c) mp of
          Just con
            | isNullaryCon con -> pure (pp (conIdent con))
            | otherwise ->
              do vds <- traverse (>>= loop 1) (conFields con)
                 let d = pp (conIdent con) <+> hsep (Vector.toList vds)
                 pure (if prec > 0 then parens d else d)
          Nothing -> panic "ppEnumVal" ["Malformed enum value", show c]
      Nothing -> pure (text "[?]")

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
                        return $ ppList vs'
      _ -> do ws' <- traverse (loop 0) ws
              return $ ppList ws'

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
    10 -> mempty
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
word :: Backend sym => sym -> Integer -> Integer -> SEval sym (GenValue sym)
word sym n i
  | n >= Arch.maxBigIntWidth = wordTooWide n
  | otherwise                = VWord . wordVal <$> wordLit sym n i


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

-- | A finite sequence of non-VBit values. Used in 'finSeq' to
--   safely construct a 'VSeq'.
newtype FinSeq sym = FinSeq { fromFinSeq :: [GenValue sym] }
  deriving Generic

-- | Safely wrap a 'GenValue' list as a 'FinSeq'. Returns 'Nothing'
--   if any values are a 'VBit'.
toFinSeq :: [GenValue sym] -> Maybe (FinSeq sym)
toFinSeq xs = FinSeq <$> mapM go xs
  where
    go x = case x of
      VBit _ -> Nothing
      _ -> Just x

-- | Wrap a 'GenValue' list as a 'FinSeq'. Raises a runtime
--   error if any values are a 'VBit'
unsafeToFinSeq :: [GenValue sym] -> FinSeq sym
unsafeToFinSeq xs = FinSeq (map go xs)
  where
    go x = case x of
      VBit _ -> panic "unsafeToFinSeq" [ "Unexpected `VBit`" ]
      _ -> x

-- | Construct a finite sequence from a 'FinSeq'. In contrast to
--   'mkSeq' this is a pure function. See 'toFinSeq' or 'unsafeToFinSeq'
--   for creating a 'FinSeq' from a list of values.
finSeq :: Backend sym => sym -> Integer -> FinSeq sym -> GenValue sym
finSeq sym len (FinSeq vs) = VSeqCtor len (finiteSeqMap sym (map pure vs))

-- | Construct either a finite sequence, or a stream.  In the finite case,
-- record whether or not the elements were bits, to aid pretty-printing.
mkSeq :: Backend sym => sym -> Nat' -> TValue -> SeqMap sym (GenValue sym) -> SEval sym (GenValue sym)
mkSeq sym len elty vals = case len of
  Nat n
    | isTBit elty -> VWord <$> bitmapWordVal sym n (fromVBit <$> vals)
    | otherwise   -> pure $ VSeqCtor n vals
  Inf             -> pure $ VStream vals

-- Value Destructors -----------------------------------------------------------

-- | Extract a bit value.
fromVBit :: Backend sym => GenValue sym -> SBit sym
fromVBit val = case val of
  VBit b -> b
  _      -> evalPanic "fromVBit" ["not a Bit", show val]

-- | Extract an integer value.
fromVInteger :: Backend sym => GenValue sym -> SInteger sym
fromVInteger val = case val of
  VInteger i -> i
  _      -> evalPanic "fromVInteger" ["not an Integer", show val]

-- | Extract a rational value.
fromVRational :: Backend sym => GenValue sym -> SRational sym
fromVRational val = case val of
  VRational q -> q
  _      -> evalPanic "fromVRational" ["not a Rational", show val]

-- | Extract a finite sequence value.
fromVSeq :: Backend sym => GenValue sym -> SeqMap sym (GenValue sym)
fromVSeq val = case val of
  VSeq _ vs -> vs
  _         -> evalPanic "fromVSeq" ["not a sequence", show val]

-- | Extract a sequence.
fromSeq :: Backend sym => String -> GenValue sym -> SEval sym (SeqMap sym (GenValue sym))
fromSeq msg val = case val of
  VSeq _ vs   -> return vs
  VStream vs  -> return vs
  _           -> evalPanic "fromSeq" ["not a sequence", msg, show val]

fromWordVal :: Backend sym => String -> GenValue sym -> WordValue sym
fromWordVal _msg (VWord wval) = wval
fromWordVal msg val = evalPanic "fromWordVal" ["not a word value", msg, show val]

asIndex :: Backend sym =>
  sym -> String -> TValue -> GenValue sym -> Either (SInteger sym) (WordValue sym)
asIndex _sym _msg TVInteger (VInteger i) = Left i
asIndex _sym _msg _ (VWord wval) = Right wval
asIndex _sym  msg _ val = evalPanic "asIndex" ["not an index value", msg, show val]

-- | Extract a packed word.
fromVWord :: Backend sym => sym -> String -> GenValue sym -> SEval sym (SWord sym)
fromVWord sym _msg (VWord wval) = asWordVal sym wval
fromVWord _ msg val = evalPanic "fromVWord" ["not a word", msg, show val]

vWordLen :: Backend sym => GenValue sym -> Maybe Integer
vWordLen val = case val of
  VWord wv              -> Just (wordValWidth wv)
  _                     -> Nothing

-- | If the given list of values are all fully-evaluated thunks
--   containing bits, return a packed word built from the same bits.
--   However, if any value is not a fully-evaluated bit, return 'Nothing'.
tryFromBits :: Backend sym => sym -> [SEval sym (GenValue sym)] -> SEval sym (Maybe (SWord sym))
tryFromBits sym = go id
  where
  go f [] = Just <$> (packWord sym (f []))
  go f (v : vs) =
    isReady sym v >>= \case
      Just v' -> go (f . ((fromVBit v'):)) vs
      Nothing -> pure Nothing

-- | Extract a function from a value.
fromVFun :: Backend sym => sym -> GenValue sym -> (SEval sym (GenValue sym) -> SEval sym (GenValue sym))
fromVFun sym val = case val of
  VFun fnstk f ->
    \x -> sModifyCallStack sym (\stk -> combineCallStacks stk fnstk) (f x)
  _ -> evalPanic "fromVFun" ["not a function", show val]

-- | Extract a polymorphic function from a value.
fromVPoly :: Backend sym => sym -> GenValue sym -> (TValue -> SEval sym (GenValue sym))
fromVPoly sym val = case val of
  VPoly fnstk f ->
    \x -> sModifyCallStack sym (\stk -> combineCallStacks stk fnstk) (f x)
  _ -> evalPanic "fromVPoly" ["not a polymorphic value", show val]

-- | Extract a polymorphic function from a value.
fromVNumPoly :: Backend sym => sym -> GenValue sym -> (Nat' -> SEval sym (GenValue sym))
fromVNumPoly sym val = case val of
  VNumPoly fnstk f ->
    \x -> sModifyCallStack sym (\stk -> combineCallStacks stk fnstk) (f x)
  _  -> evalPanic "fromVNumPoly" ["not a polymorphic value", show val]

-- | Extract a tuple from a value.
fromVTuple :: Backend sym => GenValue sym -> [SEval sym (GenValue sym)]
fromVTuple val = case val of
  VTuple vs -> vs
  _         -> evalPanic "fromVTuple" ["not a tuple", show val]

-- | Extract a record from a value.
fromVRecord :: Backend sym => GenValue sym -> RecordMap Ident (SEval sym (GenValue sym))
fromVRecord val = case val of
  VRecord fs -> fs
  _          -> evalPanic "fromVRecord" ["not a record", show val]

fromVEnum :: Backend sym => GenValue sym -> (SInteger sym, IntMap (ConValue sym))
fromVEnum val =
  case val of
    VEnum c xs -> (c,xs)
    _          -> evalPanic "fromVEnum" ["not an enum", show val]

fromVFloat :: Backend sym => GenValue sym -> SFloat sym
fromVFloat val =
  case val of
    VFloat x -> x
    _        -> evalPanic "fromVFloat" ["not a Float", show val]

-- | Lookup a field in a record.
lookupRecord :: Backend sym => Ident -> GenValue sym -> SEval sym (GenValue sym)
lookupRecord f val =
  case lookupField f (fromVRecord val) of
    Just x  -> x
    Nothing -> evalPanic "lookupRecord" ["malformed record", show val]


-- Merge and if/then/else and case

{-# INLINE iteValue #-}
iteValue :: Backend sym =>
  sym ->
  SBit sym ->
  SEval sym (GenValue sym) ->
  SEval sym (GenValue sym) ->
  SEval sym (GenValue sym)
iteValue sym b x y
  | Just True  <- bitAsLit sym b = x
  | Just False <- bitAsLit sym b = y
  | otherwise = mergeValue' sym b x y

data CaseCont sym = CaseCont
  { caseCon  :: Map Ident ([SEval sym (GenValue sym)] -> SEval sym (GenValue sym))
  , caseDflt :: Maybe (SEval sym (GenValue sym))
  }

caseValue :: Backend sym =>
  sym ->
  SInteger sym ->
  IntMap (ConValue sym) ->
  CaseCont sym ->
  SEval sym (GenValue sym)
caseValue sym tag alts k
  | Just c <- integerAsLit sym tag =
    case IMap.lookup (fromInteger c) alts of
      Just conV -> doCase conV
      Nothing -> panic "caseValue" ["Missing constructor for tag", show c]
  | otherwise = foldr doSymCase (doDefault Nothing) (IMap.toList alts)
  where
  doSymCase (n,con) otherOpts =
    do expect <- integerLit sym (toInteger n)
       yes    <- intEq sym tag expect
       iteValue sym yes (doCase con) otherOpts

  doDefault mb =
    case caseDflt k of
      Just yes -> yes
      Nothing  -> raiseError sym (NoMatchingConstructor mb)

  doCase (ConInfo con fs) =
    case Map.lookup con (caseCon k) of
      Just yes -> yes (Vector.toList fs)
      Nothing  -> doDefault (Just $! unpackIdent con)

{-# INLINE mergeValue' #-}
mergeValue' :: Backend sym =>
  sym ->
  SBit sym ->
  SEval sym (GenValue sym) ->
  SEval sym (GenValue sym) ->
  SEval sym (GenValue sym)
mergeValue' sym = mergeEval sym (mergeValue sym)

mergeConValue ::
  Backend sym => sym -> SBit sym -> ConValue sym -> ConValue sym -> ConValue sym
mergeConValue sym c = zipConInfo (mergeValue' sym c)

mergeValue :: Backend sym =>
  sym ->
  SBit sym ->
  GenValue sym ->
  GenValue sym ->
  SEval sym (GenValue sym)
mergeValue sym c v1 v2 =
  case (v1, v2) of
    (VRecord fs1 , VRecord fs2 ) ->
      do let res = zipRecords (\_lbl -> mergeValue' sym c) fs1 fs2
         case res of
           Left f -> panic "Cryptol.Eval.Value" [ "mergeValue: incompatible record values", show f ]
           Right r -> pure (VRecord r)

    (VEnum c1 fs1, VEnum c2 fs2) ->
      VEnum <$> iteInteger sym c c1 c2
            <*> pure (IMap.unionWith (mergeConValue sym c) fs1 fs2)

    (VTuple vs1  , VTuple vs2  ) | length vs1 == length vs2  ->
                                  pure $ VTuple $ zipWith (mergeValue' sym c) vs1 vs2
    (VBit b1     , VBit b2     ) -> VBit <$> iteBit sym c b1 b2
    (VInteger i1 , VInteger i2 ) -> VInteger <$> iteInteger sym c i1 i2
    (VRational q1, VRational q2) -> VRational <$> iteRational sym c q1 q2
    (VFloat f1   , VFloat f2)    -> VFloat <$> iteFloat sym c f1 f2
    (VWord w1    , VWord w2 ) | wordValWidth w1 == wordValWidth w2 -> VWord <$> mergeWord sym c w1 w2
    (VSeqCtor n1 vs1 , VSeqCtor n2 vs2 ) | n1 == n2 -> VSeqCtor n1 <$> memoMap sym (Nat n1) (mergeSeqMapVal sym c vs1 vs2)
    (VStream vs1 , VStream vs2 ) -> VStream <$> memoMap sym Inf (mergeSeqMapVal sym c vs1 vs2)
    (f1@VFun{}   , f2@VFun{}   ) -> lam sym $ \x -> mergeValue' sym c (fromVFun sym f1 x) (fromVFun sym f2 x)
    (f1@VPoly{}  , f2@VPoly{}  ) -> tlam sym $ \x -> mergeValue' sym c (fromVPoly sym f1 x) (fromVPoly sym f2 x)
    (_           , _           ) -> panic "Cryptol.Eval.Value"
                                  [ "mergeValue: incompatible values", show v1, show v2 ]

{-# INLINE mergeSeqMapVal #-}
mergeSeqMapVal :: Backend sym =>
  sym ->
  SBit sym ->
  SeqMap sym (GenValue sym)->
  SeqMap sym (GenValue sym)->
  SeqMap sym (GenValue sym)
mergeSeqMapVal sym c x y =
  indexSeqMap $ \i ->
    iteValue sym c (lookupSeqMap x i) (lookupSeqMap y i)
