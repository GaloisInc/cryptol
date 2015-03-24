-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Safe #-}

module Cryptol.Eval.Value where

import qualified Cryptol.Eval.Arch as Arch
import Cryptol.Eval.Error
import Cryptol.Prims.Syntax (ECon(..))
import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Solver.InfNat(Nat'(..))
import Cryptol.Utils.PP
import Cryptol.Utils.Panic(panic)

import Control.Monad (guard, zipWithM)
import Data.List(genericTake)
import Data.Bits (setBit,testBit,(.&.),shiftL)
import Numeric (showIntAtBase)


-- Utilities -------------------------------------------------------------------

isTBit :: TValue -> Bool
isTBit (TValue ty) = case ty of
  TCon (TC TCBit) [] -> True
  _                  -> False

isTSeq :: TValue -> Maybe (TValue, TValue)
isTSeq (TValue (TCon (TC TCSeq) [t1,t2])) = Just (TValue t1, TValue t2)
isTSeq _ = Nothing

isTFun :: TValue -> Maybe (TValue, TValue)
isTFun (TValue (TCon (TC TCFun) [t1,t2])) = Just (TValue t1, TValue t2)
isTFun _ = Nothing

isTTuple :: TValue -> Maybe (Int,[TValue])
isTTuple (TValue (TCon (TC (TCTuple n)) ts)) = Just (n, map TValue ts)
isTTuple _ = Nothing

isTRec :: TValue -> Maybe [(Name, TValue)]
isTRec (TValue (TRec fs)) = Just [ (x, TValue t) | (x,t) <- fs ]
isTRec _ = Nothing

tvSeq :: TValue -> TValue -> TValue
tvSeq (TValue x) (TValue y) = TValue (tSeq x y)



numTValue :: TValue -> Nat'
numTValue (TValue ty) =
  case ty of
    TCon (TC (TCNum x)) _ -> Nat x
    TCon (TC TCInf) _     -> Inf
    _ -> panic "Cryptol.Eval.Value.numTValue" [ "Not a numeric type:", show ty ]

toNumTValue :: Nat' -> TValue
toNumTValue (Nat n) = TValue (TCon (TC (TCNum n)) [])
toNumTValue Inf     = TValue (TCon (TC TCInf) [])

finTValue :: TValue -> Integer
finTValue tval =
  case numTValue tval of
    Nat x -> x
    Inf   -> panic "Cryptol.Eval.Value.finTValue" [ "Unexpected `inf`" ]


-- Values ----------------------------------------------------------------------

data BV = BV !Integer !Integer -- ^ width, value
                               -- The value may contain junk bits

-- | Smart constructor for 'BV's that checks for the width limit
mkBv :: Integer -> Integer -> BV
mkBv w i | w >= Arch.maxBigIntWidth = wordTooWide w
         | otherwise = BV w i

-- | Generic value type, parameterized by bit and word types.
data GenValue b w
  = VRecord [(Name, GenValue b w)]      -- @ { .. } @
  | VTuple [GenValue b w]               -- @ ( .. ) @
  | VBit b                              -- @ Bit    @
  | VSeq Bool [GenValue b w]            -- @ [n]a   @
                                        -- The boolean parameter indicates whether or not
                                        -- this is a sequence of bits.
  | VWord w                             -- @ [n]Bit @
  | VStream [GenValue b w]              -- @ [inf]a @
  | VFun (GenValue b w -> GenValue b w) -- functions
  | VPoly (TValue -> GenValue b w)      -- polymorphic values (kind *)

type Value = GenValue Bool BV

-- | An evaluated type.
-- These types do not contain type variables, type synonyms, or type functions.
newtype TValue = TValue { tValTy :: Type }

instance Show TValue where
  showsPrec p (TValue v) = showsPrec p v


-- Pretty Printing -------------------------------------------------------------

data PPOpts = PPOpts
  { useAscii     :: Bool
  , useBase      :: Int
  , useInfLength :: Int
  }

defaultPPOpts :: PPOpts
defaultPPOpts = PPOpts { useAscii = False, useBase = 10, useInfLength = 5 }

ppValue :: PPOpts -> Value -> Doc
ppValue opts = loop
  where
  loop val = case val of
    VRecord fs         -> braces (sep (punctuate comma (map ppField fs)))
      where
      ppField (f,r) = pp f <+> char '=' <+> loop r
    VTuple vals        -> parens (sep (punctuate comma (map loop vals)))
    VBit b | b         -> text "True"
           | otherwise -> text "False"
    VSeq isWord vals
       | isWord        -> ppWord opts (fromVWord val)
       | otherwise     -> ppWordSeq vals
    VWord (BV w i)     -> ppWord opts (BV w (mask w i))
    VStream vals       -> brackets $ fsep
                                   $ punctuate comma
                                   ( take (useInfLength opts) (map loop vals)
                                     ++ [text "..."]
                                   )
    VFun _             -> text "<function>"
    VPoly _            -> text "<polymorphic value>"

  ppWordSeq ws =
    case ws of
      w : _
        | Just l <- vWordLen w, asciiMode opts l ->
                text $ show $ map (integerToChar . fromWord) ws
      _ -> brackets (fsep (punctuate comma (map loop ws)))


asciiMode :: PPOpts -> Integer -> Bool
asciiMode opts width = useAscii opts && (width == 7 || width == 8)

integerToChar :: Integer -> Char
integerToChar = toEnum . fromInteger

data WithBase a = WithBase PPOpts a
    deriving (Functor)

instance PP (WithBase Value) where
  ppPrec _ (WithBase opts v) = ppValue opts v

ppWord :: PPOpts -> BV -> Doc
ppWord opts (BV width i)
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

class BitWord b w where

  -- | NOTE this assumes that the sequence of bits is big-endian and finite, so the
  -- first element of the list will be the most significant bit.
  packWord :: [b] -> w

  -- | NOTE this produces a list of bits that represent a big-endian word, so the
  -- most significant bit is the first element of the list.
  unpackWord :: w -> [b]


mask :: Integer  -- ^ Bit-width
     -> Integer  -- ^ Value
     -> Integer  -- ^ Masked result
mask w i | w >= Arch.maxBigIntWidth = wordTooWide w
         | otherwise                = i .&. ((1 `shiftL` fromInteger w) - 1)


instance BitWord Bool BV where

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


-- Value Constructors ----------------------------------------------------------

-- | Create a packed word of n bits.
word :: Integer -> Integer -> Value
word n i = VWord (mkBv n (mask n i))

lam :: (GenValue b w -> GenValue b w) -> GenValue b w
lam  = VFun

-- | A type lambda that expects a @Type@.
tlam :: (TValue -> GenValue b w) -> GenValue b w
tlam  = VPoly

-- | Generate a stream.
toStream :: [GenValue b w] -> GenValue b w
toStream  = VStream

toFinSeq :: TValue -> [GenValue b w] -> GenValue b w
toFinSeq elty = VSeq (isTBit elty)

-- | This is strict!
boolToWord :: [Bool] -> Value
boolToWord = VWord . packWord

-- | Construct either a finite sequence, or a stream.  In the finite case,
-- record whether or not the elements were bits, to aid pretty-printing.
toSeq :: TValue -> TValue -> [GenValue b w] -> GenValue b w
toSeq len elty vals = case numTValue len of
  Nat n -> toFinSeq elty (genericTake n vals)
  Inf   -> toStream vals

-- | Construct one of:
--   * a word, when the sequence is finite and the elements are bits
--   * a sequence, when the sequence is finite but the elements aren't bits
--   * a stream, when the sequence is not finite
--
-- NOTE: do not use this constructor in the case where the thing may be a
-- finite, but recursive, sequence.
toPackedSeq :: TValue -> TValue -> [Value] -> Value
toPackedSeq len elty vals = case numTValue len of

  -- finite sequence, pack a word if the elements are bits.
  Nat _ | isTBit elty -> boolToWord (map fromVBit vals)
        | otherwise  -> VSeq False vals

  -- infinite sequence, construct a stream
  Inf -> VStream vals


-- Value Destructors -----------------------------------------------------------

-- | Extract a bit value.
fromVBit :: GenValue b w -> b
fromVBit val = case val of
  VBit b -> b
  _      -> evalPanic "fromVBit" ["not a Bit"]

-- | Extract a sequence.
fromSeq :: BitWord b w => GenValue b w -> [GenValue b w]
fromSeq val = case val of
  VSeq _ vs  -> vs
  VWord bv   -> map VBit (unpackWord bv)
  VStream vs -> vs
  _          -> evalPanic "fromSeq" ["not a sequence"]

fromStr :: Value -> String
fromStr = map (toEnum . fromInteger . fromWord) . fromSeq

-- | Extract a packed word.
-- Note that this does not clean-up any junk bits in the word.
fromVWord :: BitWord b w => GenValue b w -> w
fromVWord val = case val of
  VWord bv                -> bv -- this should always mask
  VSeq isWord bs | isWord -> packWord (map fromVBit bs)
  _                       -> evalPanic "fromVWord" ["not a word"]

vWordLen :: Value -> Maybe Integer
vWordLen val = case val of
  VWord (BV w _)          -> Just w
  VSeq isWord bs | isWord -> Just (toInteger (length bs))
  _                       -> Nothing


-- | Turn a value into an integer represented by w bits.
fromWord :: Value -> Integer
fromWord val = mask w a
  where
  BV w a = fromVWord val

-- | Extract a function from a value.
fromVFun :: GenValue b w -> (GenValue b w -> GenValue b w)
fromVFun val = case val of
  VFun f -> f
  _      -> evalPanic "fromVFun" ["not a function"]

-- | Extract a polymorphic function from a value.
fromVPoly :: GenValue b w -> (TValue -> GenValue b w)
fromVPoly val = case val of
  VPoly f -> f
  _       -> evalPanic "fromVPoly" ["not a polymorphic value"]

-- | Extract a tuple from a value.
fromVTuple :: GenValue b w -> [GenValue b w]
fromVTuple val = case val of
  VTuple vs -> vs
  _         -> evalPanic "fromVTuple" ["not a tuple"]

-- | Extract a record from a value.
fromVRecord :: GenValue b w -> [(Name, GenValue b w)]
fromVRecord val = case val of
  VRecord fs -> fs
  _          -> evalPanic "fromVRecord" ["not a record"]

-- | Lookup a field in a record.
lookupRecord :: Name -> GenValue b w -> GenValue b w
lookupRecord f rec = case lookup f (fromVRecord rec) of
  Just val -> val
  Nothing  -> evalPanic "lookupRecord" ["malformed record"]

-- Value to Expression conversion ----------------------------------------------

-- | Given an expected type, returns an expression that evaluates to
-- this value, if we can determine it.
--
-- XXX: View patterns would probably clean up this definition a lot.
toExpr :: Type -> Value -> Maybe Expr
toExpr ty val = case (ty, val) of
  (TRec tfs, VRecord vfs) -> do
    let fns = map fst vfs
    guard (map fst tfs == fns)
    fes <- zipWithM toExpr (map snd tfs) (map snd vfs)
    return $ ERec (zip fns fes)
  (TCon (TC (TCTuple tl)) ts, VTuple tvs) -> do
    guard (tl == (length tvs))
    ETuple `fmap` zipWithM toExpr ts tvs
  (TCon (TC TCBit) [], VBit True ) -> return $ ECon ECTrue
  (TCon (TC TCBit) [], VBit False) -> return $ ECon ECFalse
  (TCon (TC TCSeq) [a,b], VSeq _ []) -> do
    guard (a == tZero)
    return $ EList [] b
  (TCon (TC TCSeq) [a,b], VSeq _ svs) -> do
    guard (a == tNum (length svs))
    ses <- mapM (toExpr b) svs
    return $ EList ses b
  (TCon (TC TCSeq) [a,(TCon (TC TCBit) [])], VWord (BV w v)) -> do
    guard (a == tNum w)
    return $ ETApp (ETApp (ECon ECDemote) (tNum v)) (tNum w)
  (_, VStream _) -> fail "cannot construct infinite expressions"
  (_, VFun    _) -> fail "cannot convert function values to expressions"
  (_, VPoly   _) -> fail "cannot convert polymorphic values to expressions"
  _ -> panic "Cryptol.Eval.Value.toExpr"
         ["type mismatch:"
         , pretty ty
         , render (ppValue defaultPPOpts val)
         ]
