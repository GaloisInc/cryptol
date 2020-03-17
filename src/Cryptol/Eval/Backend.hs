{-# Language FlexibleContexts #-}
{-# Language TypeFamilies #-}
module Cryptol.Eval.Backend
  ( Backend(..)
  , sDelay
  , invalidIndex
  , cryUserError
  , cryNoPrimError
  ) where

import Control.Monad.IO.Class
import Data.Kind (Type)

import Cryptol.Eval.Monad
import Cryptol.TypeCheck.AST(Name)
import Cryptol.Utils.PP


invalidIndex :: Backend sym => sym -> Integer -> SEval sym a
invalidIndex sym = raiseError sym . InvalidIndex

cryUserError :: Backend sym => sym -> String -> SEval sym a
cryUserError sym = raiseError sym . UserError

cryNoPrimError :: Backend sym => sym -> Name -> SEval sym a
cryNoPrimError sym = raiseError sym . NoPrim


{-# INLINE sDelay #-}
-- | Delay the given evaluation computation, returning a thunk
--   which will run the computation when forced.  Raise a loop
--   error if the resulting thunk is forced during its own evaluation.
sDelay :: Backend sym => sym -> Maybe String -> SEval sym a -> SEval sym (SEval sym a)
sDelay sym msg m =
  let msg'  = maybe "" ("while evaluating "++) msg
      retry = raiseError sym (LoopError msg')
   in sDelayFill sym m retry

-- | This type class defines a collection of operations on bits and words that
--   are necessary to define generic evaluator primitives that operate on both concrete
--   and symbolic values uniformly.
class MonadIO (SEval sym) => Backend sym where
  type SBit sym :: Type
  type SWord sym :: Type
  type SInteger sym :: Type
  type SEval sym :: Type -> Type

  isReady :: sym -> SEval sym a -> Bool

  sDeclareHole :: sym -> String -> SEval sym (SEval sym a, SEval sym a -> SEval sym ())
  sDelayFill :: sym -> SEval sym a -> SEval sym a -> SEval sym (SEval sym a)

  mergeEval ::
     sym ->
     (SBit sym -> a -> a -> SEval sym a) -> 
     SBit sym -> SEval sym a -> SEval sym a -> SEval sym a

  assertSideCondition :: sym -> SBit sym -> EvalError -> SEval sym ()

  raiseError :: sym -> EvalError -> SEval sym a

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
  bitLit :: sym -> Bool -> SEval sym (SBit sym)

  -- | Determine if this symbolic bit is a boolean literal
  bitAsLit :: sym -> SBit sym -> Maybe Bool

  iteBit :: sym -> SBit sym -> SBit sym -> SBit sym -> SEval sym (SBit sym)

  bitEq  :: sym -> SBit sym -> SBit sym -> SEval sym (SBit sym)
  bitOr  :: sym -> SBit sym -> SBit sym -> SEval sym (SBit sym)
  bitAnd :: sym -> SBit sym -> SBit sym -> SEval sym (SBit sym)
  bitXor :: sym -> SBit sym -> SBit sym -> SEval sym (SBit sym)
  bitComplement :: sym -> SBit sym -> SEval sym (SBit sym)

  -- | Construct a literal word value given a bit width and a value.
  wordLit ::
    sym ->
    Integer {- ^ Width -} ->
    Integer {- ^ Value -} ->
    SEval sym (SWord sym)

  iteWord :: sym -> SBit sym -> SWord sym -> SWord sym -> SEval sym (SWord sym)

  iteInteger :: sym -> SBit sym -> SInteger sym -> SInteger sym -> SEval sym (SInteger sym)

  -- | Construct a literal integer value from the given integer.
  integerLit ::
    sym ->
    Integer {- ^ Value -} ->
    SEval sym (SInteger sym)

  -- | Extract the numbered bit from the word.
  --
  --   NOTE: this assumes that the sequence of bits is big-endian and finite, so the
  --   bit numbered 0 is the most significant bit.
  wordBit ::
    sym ->
    SWord sym ->
    Integer {- ^ Bit position to extract -} ->
    SEval sym (SBit sym)

  -- | Update the numbered bit in the word.
  --
  --   NOTE: this assumes that the sequence of bits is big-endian and finite, so the
  --   bit numbered 0 is the most significant bit.
  wordUpdate ::
    sym ->
    SWord sym ->
    Integer {- ^ Bit position to update -} ->
    SBit sym ->
    SEval sym (SWord sym)

  -- | Construct a word value from a finite sequence of bits.
  --   NOTE: this assumes that the sequence of bits is big-endian and finite, so the
  --   first element of the list will be the most significant bit.
  packWord ::
    sym ->
    [SBit sym] ->
    SEval sym (SWord sym)

  -- | Deconstruct a packed word value in to a finite sequence of bits.
  --   NOTE: this produces a list of bits that represent a big-endian word, so
  --   the most significant bit is the first element of the list.
  unpackWord ::
    sym ->
    SWord sym ->
    SEval sym [SBit sym]

  -- | Construct a packed word of the specified width from an integer value.
  wordFromInt ::
    sym ->
    Integer {- ^ bit-width -} ->
    SInteger sym ->
    SEval sym (SWord sym)

  -- | Concatenate the two given word values.
  --   NOTE: the first argument represents the more-significant bits
  joinWord ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SWord sym)

  -- | Take the most-significant bits, and return
  --   those bits and the remainder.  The first element
  --   of the pair is the most significant bits.
  --   The two integer sizes must sum to the length of the given word value.
  splitWord ::
    sym ->
    Integer {- ^ left width -} ->
    Integer {- ^ right width -} ->
    SWord sym ->
    SEval sym (SWord sym, SWord sym)

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
    SEval sym (SWord sym)

  wordOr ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SWord sym)

  wordAnd ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SWord sym)

  wordXor ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SWord sym)

  wordComplement ::
    sym ->
    SWord sym ->
    SEval sym (SWord sym)

  -- | 2's complement addition of packed words.  The arguments must have
  --   equal bit width, and the result is of the same width. Overflow is silently
  --   discarded.
  wordPlus ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SWord sym)

  -- | 2's complement subtraction of packed words.  The arguments must have
  --   equal bit width, and the result is of the same width. Overflow is silently
  --   discarded.
  wordMinus ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SWord sym)

  -- | 2's complement multiplication of packed words.  The arguments must have
  --   equal bit width, and the result is of the same width. The high bits of the
  --   multiplication are silently discarded.
  wordMult ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SWord sym)

  -- | 2's complement unsigned division of packed words.  The arguments must have
  --   equal bit width, and the result is of the same width.  It is illegal to
  --   call with a second argument concretely equal to 0.
  wordDiv ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SWord sym)

  -- | 2's complement unsigned modulus of packed words.  The arguments must have
  --   equal bit width, and the result is of the same width.  It is illegal to
  --   call with a second argument concretely equal to 0.
  wordMod ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SWord sym)

  -- | 2's complement signed division of packed words.  The arguments must have
  --   equal bit width, and the result is of the same width.  It is illegal to
  --   call with a second argument concretely equal to 0.
  wordSignedDiv ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SWord sym)

  -- | 2's complement signed modulus of packed words.  The arguments must have
  --   equal bit width, and the result is of the same width.  It is illegal to
  --   call with a second argument concretely equal to 0.
  wordSignedMod ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SWord sym)

  -- | Exponentiation of bitvectors.
  wordExp ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SWord sym)

  -- | 2's complement negation of bitvectors
  wordNegate ::
    sym ->
    SWord sym ->
    SEval sym (SWord sym)

  wordLg2 ::
    sym ->
    SWord sym ->
    SEval sym (SWord sym)

  wordEq ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SBit sym)

  wordSignedLessThan ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SBit sym)

  wordLessThan ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SBit sym)

  wordGreaterThan ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SBit sym)

  -- | Construct an integer value from the given packed word.
  wordToInt ::
    sym ->
    SWord sym ->
    SEval sym (SInteger sym)

  -- | Addition of unbounded integers.
  intPlus ::
    sym ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Negation of unbounded integers
  intNegate ::
    sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Subtraction of unbounded integers.
  intMinus ::
    sym ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Multiplication of unbounded integers.
  intMult ::
    sym ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Integer division, rounding down. It is illegal to
  --   call with a second argument concretely equal to 0.
  --   Same semantics as Haskell's @div@ operation.
  intDiv ::
    sym ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Integer modulus, with division rounding down. It is illegal to
  --   call with a second argument concretely equal to 0.
  --   Same semantics as Haskell's @mod@ operation.
  intMod ::
    sym ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Integer division, rounding toward zero. It is illegal to
  --   call with a second argument concretely equal to 0.
  --   Same semantics as Haskell's @quot@ operation.
  intDivRTZ :: 
    sym ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Integer modulus, with division rounding toward zero. It is illegal to
  --   call with a second argument concretely equal to 0.
  --   Same semantics as Haskell's @rem@ operation.
  intModRTZ :: 
    sym ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Integer exponentiation.  The second argument must be non-negative.
  intExp ::
    sym ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  intLg2 ::
    sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  intEq ::
    sym ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SBit sym)

  intLessThan ::
    sym ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SBit sym)

  intGreaterThan ::
    sym ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SBit sym)

  -- | Turn an integer into a value in Z_n
  intToIntMod ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Transform a Z_n value into an integer, ensuring the value is properly
  --   reduced modulo n
  intModToInt ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Addition of integers modulo n, for a concrete positive integer n.
  intModPlus ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Additive inverse of integers modulo n
  intModNegate ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Subtraction of integers modulo n, for a concrete positive integer n.
  intModMinus ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Multiplication of integers modulo n, for a concrete positive integer n.
  intModMult ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Division of integers modulo n, for a concrete positive integer n.
  --   NOTE: this is integer division on the initial segement of Z,
  --   and not the multiplictitive inverse in Z_p.
  intModDiv ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Modulus of integers modulo n, for a concrete positive integer n.
  --   NOTE: this is the modulus corresponding to integer division on the initial
  --   segement of Z, and not related to multiplictitive inverse in Z_p.
  intModMod ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Exponentation of integers modulo n
  intModExp ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  intModLg2 ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SEval sym (SInteger sym)

  intModEq ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SBit sym)

  intModLessThan ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SBit sym)

  intModGreaterThan ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SBit sym)

