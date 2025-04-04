{-# Language FlexibleContexts #-}
{-# Language TypeFamilies #-}
{-# Language ScopedTypeVariables #-}
module Cryptol.Backend
  ( Backend(..)
  , wordLen
  , sDelay
  , invalidIndex
  , cryUserError
  , cryNoPrimError
  , FPArith2
  , IndexDirection(..)

  , enumerateIntBits
  , enumerateIntBits'

    -- * Rationals
  , SRational(..)
  , intToRational
  , ratio
  , rationalAdd
  , rationalSub
  , rationalNegate
  , rationalMul
  , rationalRecip
  , rationalDivide
  , rationalFloor
  , rationalCeiling
  , rationalTrunc
  , rationalRoundAway
  , rationalRoundToEven
  , rationalEq
  , rationalLessThan
  , rationalGreaterThan
  , iteRational
  ) where

import qualified Control.Exception as X
import Control.Monad.IO.Class
import Data.Kind (Type)
import Data.Proxy(Proxy(..))

import Cryptol.Backend.FloatHelpers (BF)
import Cryptol.Backend.Monad
  ( EvalError(..), Unsupported(..), CallStack, pushCallFrame )
import Cryptol.ModuleSystem.Name(Name)
import Cryptol.Parser.Position
import Cryptol.TypeCheck.Solver.InfNat(Nat'(..),widthInteger)

data IndexDirection
  = IndexForward
  | IndexBackward

invalidIndex :: Backend sym => sym -> Integer -> SEval sym a
invalidIndex sym i = raiseError sym (InvalidIndex (Just i))

cryUserError :: Backend sym => sym -> String -> SEval sym a
cryUserError sym msg = raiseError sym (UserError msg)

cryNoPrimError :: Backend sym => sym -> Name -> SEval sym a
cryNoPrimError sym nm = raiseError sym (NoPrim nm)

{-# INLINE sDelay #-}
-- | Delay the given evaluation computation, returning a thunk
--   which will run the computation when forced.  Raise a loop
--   error if the resulting thunk is forced during its own evaluation.
sDelay :: Backend sym => sym -> SEval sym a -> SEval sym (SEval sym a)
sDelay sym m = sDelayFill sym m Nothing ""

-- | Representation of rational numbers.
--     Invariant: denominator is not 0
data SRational sym =
  SRational
  { sNum :: SInteger sym
  , sDenom :: SInteger sym
  }

intToRational :: Backend sym => sym -> SInteger sym -> SEval sym (SRational sym)
intToRational sym x = SRational x <$> (integerLit sym 1)

ratio :: Backend sym => sym -> SInteger sym -> SInteger sym -> SEval sym (SRational sym)
ratio sym n d =
  do pz  <- bitComplement sym =<< intEq sym d =<< integerLit sym 0
     assertSideCondition sym pz DivideByZero
     pure (SRational n d)

rationalRecip :: Backend sym => sym -> SRational sym -> SEval sym (SRational sym)
rationalRecip sym (SRational a b) = ratio sym b a

rationalDivide :: Backend sym => sym -> SRational sym -> SRational sym -> SEval sym (SRational sym)
rationalDivide sym x y = rationalMul sym x =<< rationalRecip sym y

rationalFloor :: Backend sym => sym -> SRational sym -> SEval sym (SInteger sym)
 -- NB, relies on integer division being round-to-negative-inf division
rationalFloor sym (SRational n d) = intDiv sym n d

rationalCeiling :: Backend sym => sym -> SRational sym -> SEval sym (SInteger sym)
rationalCeiling sym r = intNegate sym =<< rationalFloor sym =<< rationalNegate sym r

rationalTrunc :: Backend sym => sym -> SRational sym -> SEval sym (SInteger sym)
rationalTrunc sym r =
  do p <- rationalLessThan sym r =<< intToRational sym =<< integerLit sym 0
     cr <- rationalCeiling sym r
     fr <- rationalFloor sym r
     iteInteger sym p cr fr

rationalRoundAway :: Backend sym => sym -> SRational sym -> SEval sym (SInteger sym)
rationalRoundAway sym r =
  do p <- rationalLessThan sym r =<< intToRational sym =<< integerLit sym 0
     half <- SRational <$> integerLit sym 1 <*> integerLit sym 2
     cr <- rationalCeiling sym =<< rationalSub sym r half
     fr <- rationalFloor sym =<< rationalAdd sym r half
     iteInteger sym p cr fr

rationalRoundToEven :: Backend sym => sym -> SRational sym -> SEval sym (SInteger sym)
rationalRoundToEven sym r =
  do lo <- rationalFloor sym r
     hi <- intPlus sym lo =<< integerLit sym 1
     -- NB: `diff` will be nonnegative because `lo <= r`
     diff <- rationalSub sym r =<< intToRational sym lo
     half <- SRational <$> integerLit sym 1 <*> integerLit sym 2

     ite (rationalLessThan sym diff half) (pure lo) $
       ite (rationalGreaterThan sym diff half) (pure hi) $
         ite (isEven lo) (pure lo) (pure hi)

 where
 isEven x =
   do parity <- intMod sym x =<< integerLit sym 2
      intEq sym parity =<< integerLit sym 0

 ite x t e =
   do x' <- x
      case bitAsLit sym x' of
        Just True -> t
        Just False -> e
        Nothing ->
          do t' <- t
             e' <- e
             iteInteger sym x' t' e'


rationalAdd :: Backend sym => sym -> SRational sym -> SRational sym -> SEval sym (SRational sym)
rationalAdd sym (SRational a b) (SRational c d) =
  do ad <- intMult sym a d
     bc <- intMult sym b c
     bd <- intMult sym b d
     ad_bc <- intPlus sym ad bc
     pure (SRational ad_bc bd)

rationalSub :: Backend sym => sym -> SRational sym -> SRational sym -> SEval sym (SRational sym)
rationalSub sym (SRational a b) (SRational c d) =
  do ad <- intMult sym a d
     bc <- intMult sym b c
     bd <- intMult sym b d
     ad_bc <- intMinus sym ad bc
     pure (SRational ad_bc bd)

rationalNegate :: Backend sym => sym -> SRational sym -> SEval sym (SRational sym)
rationalNegate sym (SRational a b) =
  do aneg <- intNegate sym a
     pure (SRational aneg b)

rationalMul :: Backend sym => sym -> SRational sym -> SRational sym -> SEval sym (SRational sym)
rationalMul sym (SRational a b) (SRational c d) =
  do ac <- intMult sym a c
     bd <- intMult sym b d
     pure (SRational ac bd)

rationalEq :: Backend sym => sym -> SRational sym -> SRational sym -> SEval sym (SBit sym)
rationalEq sym (SRational a b) (SRational c d) =
  do ad <- intMult sym a d
     bc <- intMult sym b c
     intEq sym ad bc

normalizeSign :: Backend sym => sym -> SRational sym -> SEval sym (SRational sym)
normalizeSign sym (SRational a b) =
  do p <- intLessThan sym b =<< integerLit sym 0
     case bitAsLit sym p of
       Just False -> pure (SRational a b)
       Just True  ->
         do aneg <- intNegate sym a
            bneg <- intNegate sym b
            pure (SRational aneg bneg)
       Nothing ->
         do aneg <- intNegate sym a
            bneg <- intNegate sym b
            a' <- iteInteger sym p aneg a
            b' <- iteInteger sym p bneg b
            pure (SRational a' b')

rationalLessThan:: Backend sym => sym -> SRational sym -> SRational sym -> SEval sym (SBit sym)
rationalLessThan sym x y =
  do SRational a b <- normalizeSign sym x
     SRational c d <- normalizeSign sym y
     ad <- intMult sym a d
     bc <- intMult sym b c
     intLessThan sym ad bc

rationalGreaterThan:: Backend sym => sym -> SRational sym -> SRational sym -> SEval sym (SBit sym)
rationalGreaterThan sym = flip (rationalLessThan sym)

iteRational :: Backend sym => sym -> SBit sym -> SRational sym -> SRational sym -> SEval sym (SRational sym)
iteRational sym p (SRational a b) (SRational c d) =
  SRational <$> iteInteger sym p a c <*> iteInteger sym p b d

-- | Compute the list of bits in an integer in big-endian order.
--   The integer argument is a concrete upper bound for
--   the symbolic integer.
enumerateIntBits' :: Backend sym =>
  sym ->
  Integer ->
  SInteger sym ->
  SEval sym (Integer, [SBit sym])
enumerateIntBits' sym n idx =
  do let width = widthInteger n
     w <- wordFromInt sym width idx
     bs <- unpackWord sym w
     pure (width, bs)

-- | Compute the list of bits in an integer in big-endian order.
--   Fails if neither the sequence length nor the type value
--   provide an upper bound for the integer.
enumerateIntBits :: Backend sym =>
  sym ->
  Nat' ->
  SInteger sym ->
  SEval sym (Integer, [SBit sym])
enumerateIntBits sym (Nat n) idx = enumerateIntBits' sym n idx
enumerateIntBits _sym Inf _ = liftIO (X.throw (UnsupportedSymbolicOp "unbounded integer shifting"))

-- | This type class defines a collection of operations on bits, words and integers that
--   are necessary to define generic evaluator primitives that operate on both concrete
--   and symbolic values uniformly.
class MonadIO (SEval sym) => Backend sym where
  type SBit sym :: Type
  type SWord sym :: Type
  type SInteger sym :: Type
  type SFloat sym :: Type
  type SEval sym :: Type -> Type

  -- ==== Evaluation monad operations ====

  -- | Check if an operation is "ready", which means its
  --   evaluation will be trivial.
  isReady :: sym -> SEval sym a -> SEval sym (Maybe a)

  -- | Produce a thunk value which can be filled with its associated computation
  --   after the fact.  A preallocated thunk is returned, along with an operation to
  --   fill the thunk with the associated computation.
  --   This is used to implement recursive declaration groups.
  sDeclareHole :: sym -> String -> SEval sym (SEval sym a, SEval sym a -> SEval sym ())

  -- | Delay the given evaluation computation, returning a thunk
  --   which will run the computation when forced.  Run the 'retry'
  --   computation instead if the resulting thunk is forced during
  --   its own evaluation.
  sDelayFill :: sym -> SEval sym a -> Maybe (SEval sym a) -> String -> SEval sym (SEval sym a)

  -- | Begin evaluating the given computation eagerly in a separate thread
  --   and return a thunk which will await the completion of the given computation
  --   when forced.
  sSpark :: sym -> SEval sym a -> SEval sym (SEval sym a)

  -- | Push a call frame on to the current call stack while evaluating the given action
  sPushFrame :: sym -> Name -> Range -> SEval sym a -> SEval sym a
  sPushFrame sym nm rng m = sModifyCallStack sym (pushCallFrame nm rng) m

  -- | Use the given call stack while evaluating the given action
  sWithCallStack :: sym -> CallStack -> SEval sym a -> SEval sym a
  sWithCallStack sym stk m = sModifyCallStack sym (\_ -> stk) m

  -- | Apply the given function to the current call stack while evaluating the given action
  sModifyCallStack :: sym -> (CallStack -> CallStack) -> SEval sym a -> SEval sym a

  -- | Retrieve the current evaluation call stack
  sGetCallStack :: sym -> SEval sym CallStack

  -- | Merge the two given computations according to the predicate.
  mergeEval ::
     sym ->
     (SBit sym -> a -> a -> SEval sym a) {- ^ A merge operation on values -} ->
     SBit sym {- ^ The condition -} ->
     SEval sym a {- ^ The "then" computation -} ->
     SEval sym a {- ^ The "else" computation -} ->
     SEval sym a

  -- | Assert that a condition must hold, and indicate what sort of
  --   error is indicated if the condition fails.
  assertSideCondition :: sym -> SBit sym -> EvalError -> SEval sym ()

  -- | Indiciate that an error condition exists
  raiseError :: sym -> EvalError -> SEval sym a

  -- ==== Identifying literal values ====

  -- | Determine if this symbolic bit is a boolean literal
  bitAsLit :: sym -> SBit sym -> Maybe Bool

  -- | The number of bits in a word value.
  wordLen' :: proxy sym -> SWord sym -> Integer

  -- | Determine if this symbolic word is a literal.
  --   If so, return the bit width and value.
  wordAsLit :: sym -> SWord sym -> Maybe (Integer, Integer)

  -- | Attempt to render a word value as an ASCII character.  Return 'Nothing'
  --   if the character value is unknown (e.g., for symbolic values).
  wordAsChar :: sym -> SWord sym -> Maybe Char

  -- | Determine if this symbolic integer is a literal
  integerAsLit :: sym -> SInteger sym -> Maybe Integer

  -- | Determine if this symbolic floating-point value is a literal
  fpAsLit :: sym -> SFloat sym -> Maybe BF

  -- ==== Creating literal values ====

  -- | Construct a literal bit value from a boolean.
  bitLit :: sym -> Bool -> SBit sym

  -- | Construct a literal word value given a bit width and a value.
  wordLit ::
    sym ->
    Integer {- ^ Width -} ->
    Integer {- ^ Value -} ->
    SEval sym (SWord sym)

  -- | Construct a literal integer value from the given integer.
  integerLit ::
    sym ->
    Integer {- ^ Value -} ->
    SEval sym (SInteger sym)

  -- | Construct a floating point value from the given rational.
  fpLit ::
    sym ->
    Integer  {- ^ exponent bits -} ->
    Integer  {- ^ precision bits -} ->
    Rational {- ^ The rational -} ->
    SEval sym (SFloat sym)

  -- | Construct a floating point value from the given bit-precise
  --   floating-point representation.
  fpExactLit :: sym -> BF -> SEval sym (SFloat sym)

  -- ==== If/then/else operations ====
  iteBit :: sym -> SBit sym -> SBit sym -> SBit sym -> SEval sym (SBit sym)
  iteWord :: sym -> SBit sym -> SWord sym -> SWord sym -> SEval sym (SWord sym)
  iteInteger :: sym -> SBit sym -> SInteger sym -> SInteger sym -> SEval sym (SInteger sym)
  iteFloat :: sym -> SBit sym -> SFloat sym -> SFloat sym -> SEval sym (SFloat sym)

  -- ==== Bit operations ====
  bitEq  :: sym -> SBit sym -> SBit sym -> SEval sym (SBit sym)
  bitOr  :: sym -> SBit sym -> SBit sym -> SEval sym (SBit sym)
  bitAnd :: sym -> SBit sym -> SBit sym -> SEval sym (SBit sym)
  bitXor :: sym -> SBit sym -> SBit sym -> SEval sym (SBit sym)
  bitComplement :: sym -> SBit sym -> SEval sym (SBit sym)

  -- ==== Word operations ====

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

  -- | Bitwise OR
  wordOr ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SWord sym)

  -- | Bitwise AND
  wordAnd ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SWord sym)

  -- | Bitwise XOR
  wordXor ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SWord sym)

  -- | Bitwise complement
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

  -- | Shift a bitvector left by the specified amount.
  --   The shift amount is considered as an unsigned value.
  --   Shifting by more than the word length results in 0.
  wordShiftLeft ::
    sym ->
    SWord sym {- ^ value to shift -} ->
    SWord sym {- ^ amount to shift by -} ->
    SEval sym (SWord sym)

  -- | Shift a bitvector right by the specified amount.
  --   This is a logical shift, which shifts in 0 values
  --   on the left. The shift amount is considered as an
  --   unsigned value. Shifting by more than the word length
  --   results in 0.
  wordShiftRight ::
    sym ->
    SWord sym {- ^ value to shift -} ->
    SWord sym {- ^ amount to shift by -} ->
    SEval sym (SWord sym)

  -- | Shift a bitvector right by the specified amount.  This is an
  --   arithmetic shift, which shifts in copies of the high bit on the
  --   left. The shift amount is considered as an unsigned
  --   value. Shifting by more than the word length results in filling
  --   the bitvector with the high bit.
  wordSignedShiftRight ::
    sym ->
    SWord sym {- ^ value to shift -} ->
    SWord sym {- ^ amount to shift by -} ->
    SEval sym (SWord sym)

  wordRotateLeft ::
    sym ->
    SWord sym {- ^ value to rotate -} ->
    SWord sym {- ^ amount to rotate by -} ->
    SEval sym (SWord sym)

  wordRotateRight ::
    sym ->
    SWord sym {- ^ value to rotate -} ->
    SWord sym {- ^ amount to rotate by -} ->
    SEval sym (SWord sym)



  -- | 2's complement negation of bitvectors
  wordNegate ::
    sym ->
    SWord sym ->
    SEval sym (SWord sym)

  -- | Compute rounded-up log-2 of the input
  wordLg2 ::
    sym ->
    SWord sym ->
    SEval sym (SWord sym)

  -- | Test if two words are equal.  Arguments must have the same width.
  wordEq ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SBit sym)

  -- | Signed less-than comparison on words.  Arguments must have the same width.
  wordSignedLessThan ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SBit sym)

  -- | Unsigned less-than comparison on words.  Arguments must have the same width.
  wordLessThan ::
    sym ->
    SWord sym ->
    SWord sym ->
    SEval sym (SBit sym)

  -- | Unsigned greater-than comparison on words.  Arguments must have the same width.
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

  -- | Construct a signed integer value from the given packed word.
  wordToSignedInt ::
    sym ->
    SWord sym ->
    SEval sym (SInteger sym)

  -- ==== Integer operations ====

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

  -- | Equality comparison on integers
  intEq ::
    sym ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SBit sym)

  -- | Less-than comparison on integers
  intLessThan ::
    sym ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SBit sym)

  -- | Greater-than comparison on integers
  intGreaterThan ::
    sym ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SBit sym)


  -- ==== Operations on Z_n ====

  -- | Turn an integer into a value in Z_n
  intToZn ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Transform a Z_n value into an integer, ensuring the value is properly
  --   reduced modulo n
  znToInt ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Addition of integers modulo n, for a concrete positive integer n.
  znPlus ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Additive inverse of integers modulo n
  znNegate ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Subtraction of integers modulo n, for a concrete positive integer n.
  znMinus ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Multiplication of integers modulo n, for a concrete positive integer n.
  znMult ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- | Equality test of integers modulo n
  znEq ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SInteger sym ->
    SEval sym (SBit sym)

  -- | Multiplicative inverse in (Z n).
  --   PRECONDITION: the modulus is a prime
  znRecip ::
    sym ->
    Integer {- ^ modulus -} ->
    SInteger sym ->
    SEval sym (SInteger sym)

  -- == Float Operations ==
  fpEq          :: sym -> SFloat sym -> SFloat sym -> SEval sym (SBit sym)
  fpLessThan    :: sym -> SFloat sym -> SFloat sym -> SEval sym (SBit sym)
  fpGreaterThan :: sym -> SFloat sym -> SFloat sym -> SEval sym (SBit sym)

  fpLogicalEq   :: sym -> SFloat sym -> SFloat sym -> SEval sym (SBit sym)

  fpNaN    :: sym -> Integer {- ^ exponent bits -} -> Integer {- ^ precision bits -} -> SEval sym (SFloat sym)
  fpPosInf :: sym -> Integer {- ^ exponent bits -} -> Integer {- ^ precision bits -} -> SEval sym (SFloat sym)

  fpPlus, fpMinus, fpMult, fpDiv :: FPArith2 sym
  fpNeg, fpAbs :: sym -> SFloat sym -> SEval sym (SFloat sym)
  fpSqrt :: sym -> SWord sym -> SFloat sym -> SEval sym (SFloat sym)

  fpFMA :: sym -> SWord sym -> SFloat sym -> SFloat sym -> SFloat sym -> SEval sym (SFloat sym)

  fpIsZero, fpIsNeg, fpIsNaN, fpIsInf, fpIsNorm, fpIsSubnorm :: sym -> SFloat sym -> SEval sym (SBit sym)

  fpToBits :: sym -> SFloat sym -> SEval sym (SWord sym)
  fpFromBits ::
    sym ->
    Integer {- ^ exponent bits -} ->
    Integer {- ^ precision bits -} ->
    SWord sym ->
    SEval sym (SFloat sym)

  fpToInteger ::
    sym ->
    String {- ^ Name of the function for error reporting -} ->
    SWord sym {- ^ Rounding mode -} ->
    SFloat sym ->
    SEval sym (SInteger sym)

  fpFromInteger ::
    sym ->
    Integer         {- ^ exp width -} ->
    Integer         {- ^ prec width -} ->
    SWord sym       {- ^ rounding mode -} ->
    SInteger sym    {- ^ the integer to use -} ->
    SEval sym (SFloat sym)

  fpToRational ::
    sym ->
    SFloat sym ->
    SEval sym (SRational sym)

  fpFromRational ::
    sym ->
    Integer         {- ^ exp width -} ->
    Integer         {- ^ prec width -} ->
    SWord sym       {- ^ rounding mode -} ->
    SRational sym ->
    SEval sym (SFloat sym)

type FPArith2 sym =
  sym ->
  SWord sym ->
  SFloat sym ->
  SFloat sym ->
  SEval sym (SFloat sym)

wordLen :: forall sym. Backend sym => sym -> SWord sym -> Integer
wordLen _ x = wordLen' (Proxy :: Proxy sym) x
{-# INLINE wordLen #-}