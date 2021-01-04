-- |
-- Module      :  Cryptol.Testing.Random
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- This module generates random values for Cryptol types.

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TypeFamilies #-}
module Cryptol.Testing.Random
( Gen
, randomValue
, dumpableType
, testableType
, TestResult(..)
, isPass
, returnTests
, exhaustiveTests
, randomTests
, randomIntegerBoundedBelow
, randomIntegerBoundedAbove
) where

import qualified Control.Exception as X
import Control.Monad          (liftM2)
import Control.Monad.IO.Class (MonadIO(..))
import Data.Ratio             ((%))
import Data.List              (unfoldr, genericTake, genericIndex, genericReplicate)
import Data.Word              (Word8)
import qualified Data.Sequence as Seq

import System.Random          (split, random, randomR)
import System.Random.TF.Gen   (TFGen) 

import Cryptol.Backend        (Backend(..), SRational(..))
import Cryptol.Backend.Monad  (runEval,Eval,EvalErrorEx(..))
import Cryptol.Backend.Concrete
import Cryptol.Backend.SeqMap

import Cryptol.Eval.Type      (TValue(..))
import Cryptol.Eval.Value     (GenValue(..), WordValue(..),
                               ppValue, defaultPPOpts, fromVFun)
import Cryptol.Utils.Ident    (Ident)
import Cryptol.Utils.Panic    (panic)
import Cryptol.Utils.RecordMap

type Gen x = Word8 -> TFGen -> (SEval x (GenValue x), TFGen)


type Value = GenValue Concrete

{- | Apply a testable value to some randomly-generated arguments.
     Returns @Nothing@ if the function returned @True@, or
     @Just counterexample@ if it returned @False@.

    Please note that this function assumes that the generators match
    the supplied value, otherwise we'll panic.
 -}
runOneTest ::
  Value  {- ^ Function under test -} ->
  [Gen Concrete] {- ^ Argument generators -} ->
  Word8 {- ^ Size -} ->
  TFGen ->
  IO (TestResult, TFGen)
runOneTest fun argGens sz g0 = do
  let (args, g1) = foldr mkArg ([], g0) argGens
      mkArg argGen (as, g) = let (a, g') = argGen sz g in (a:as, g')
  args' <- runEval mempty (sequence args)
  result <- evalTest fun args'
  return (result, g1)

returnOneTest ::
  Value   {- ^ Function to be used to calculate tests -} ->
  [Gen Concrete] {- ^ Argument generators -} ->
  Word8 {- ^ Size -} ->
  TFGen {- ^ Initial random state -} ->
  IO ([Value], Value, TFGen) {- ^ Arguments, result, and new random state -}
returnOneTest fun argGens sz g0 =
  do let (args, g1) = foldr mkArg ([], g0) argGens
         mkArg argGen (as, g) = let (a, g') = argGen sz g in (a:as, g')
     args' <- runEval mempty (sequence args)
     result <- runEval mempty (go fun args')
     return (args', result, g1)
   where
     go f@VFun{} (v : vs) =
       do f' <- fromVFun Concrete f (pure v)
          go f' vs
     go VFun{} [] = panic "Cryptol.Testing.Random" ["Not enough arguments to function while generating tests"]
     go _ (_ : _) = panic "Cryptol.Testing.Random" ["Too many arguments to function while generating tests"]
     go v [] = return v


-- | Return a collection of random tests.
returnTests ::
  TFGen {- ^ The random generator state -} ->
  [Gen Concrete] {- ^ Generators for the function arguments -} ->
  Value {- ^ The function itself -} ->
  Int {- ^ How many tests? -} ->
  IO [([Value], Value)] {- ^ A list of pairs of random arguments and computed outputs -}
returnTests g gens fun num = go gens g 0
  where
    go args g0 n
      | n >= num = return []
      | otherwise =
        do let sz = fromIntegral (div (100 * (1 + n)) num)
           (inputs, output, g1) <- returnOneTest fun args sz g0
           more <- go args g1 (n + 1)
           return ((inputs, output) : more)

{- | Given a (function) type, compute generators for the function's
arguments. -}
dumpableType :: TValue -> Maybe [Gen Concrete]
dumpableType (TVFun t1 t2) =
   do g  <- randomValue Concrete t1
      as <- dumpableType t2
      return (g : as)
dumpableType ty =
   do (_ :: Gen Concrete) <- randomValue Concrete ty
      return []


{-# SPECIALIZE randomValue ::
  Concrete -> TValue -> Maybe (Gen Concrete)
  #-}

{- | A generator for values of the given type.  This fails if we are
given a type that lacks a suitable random value generator. -}
randomValue :: Backend sym => sym -> TValue -> Maybe (Gen sym)
randomValue sym ty =
  case ty of
    TVBit         -> Just (randomBit sym)
    TVInteger     -> Just (randomInteger sym)
    TVRational    -> Just (randomRational sym)
    TVIntMod m    -> Just (randomIntMod sym m)
    TVFloat e p   -> Just (randomFloat sym e p)
    TVSeq n TVBit -> Just (randomWord sym n)
    TVSeq n el ->
         do mk <- randomValue sym el
            return (randomSequence n mk)
    TVStream el ->
         do mk <- randomValue sym el
            return (randomStream mk)
    TVTuple els ->
         do mks <- mapM (randomValue sym) els
            return (randomTuple mks)
    TVRec fs ->
         do gs <- traverse (randomValue sym) fs
            return (randomRecord gs)
    TVNewtype _ _ fs ->
         do gs <- traverse (randomValue sym) fs
            return (randomRecord gs)
    TVArray{} -> Nothing
    TVFun{} -> Nothing
    TVAbstract{} -> Nothing
    TVGen{} -> Nothing

{-# INLINE randomBit #-}

-- | Generate a random bit value.
randomBit :: Backend sym => sym -> Gen sym
randomBit sym _ g =
  let (b,g1) = random g
  in (pure (VBit (bitLit sym b)), g1)

{-# INLINE randomSize #-}

randomSize :: Word8 -> Word8 -> TFGen -> (Word8, TFGen)
randomSize k n g
  | p == 1 = (n, g')
  | otherwise = randomSize k (n + 1) g'
  where (p, g') = randomR (1, k) g

{-# INLINE randomInteger #-}

-- | Generate a random integer value. The size parameter is assumed to
-- vary between 1 and 100, and we use it to generate smaller numbers
-- first.
randomInteger :: Backend sym => sym -> Gen sym
randomInteger sym w g =
  let (n, g1) = if w < 100 then (w, g) else randomSize 8 100 g
      (i, g2) = randomR (- 256^n, 256^n) g1
  in (VInteger <$> integerLit sym i, g2)

{-# INLINE randomIntMod #-}

randomIntegerBoundedBelow :: Backend sym => sym -> Integer -> Gen sym
randomIntegerBoundedBelow sym lo w g =
  let (n, g1) = if w < 100 then (w, g) else randomSize 8 100 g
      (i, g2) = randomR (0, 256^n) g1
  in (VInteger <$> integerLit sym (lo + i), g2)

{-# INLINE randomIntegerBoundedBelow #-}

randomIntegerBoundedAbove :: Backend sym => sym -> Integer -> Gen sym
randomIntegerBoundedAbove sym hi w g =
  let (n, g1) = if w < 100 then (w, g) else randomSize 8 100 g
      (i, g2) = randomR (-256^n, 0) g1
  in (VInteger <$> integerLit sym (hi + i), g2)

{-# INLINE randomIntegerBoundedAbove #-}

randomIntMod :: Backend sym => sym -> Integer -> Gen sym
randomIntMod sym modulus _ g =
  let (i, g') = randomR (0, modulus-1) g
  in (VInteger <$> integerLit sym i, g')

{-# INLINE randomRational #-}

randomRational :: Backend sym => sym -> Gen sym
randomRational sym w g =
  let (sz, g1) = if w <= 100 then (w, g) else randomSize 8 100 g
      (n, g2) = randomR (- 256^sz, 256^sz) g1
      (d, g3) = randomR ( 1, 256^sz) g2
   in (do n' <- integerLit sym n
          d' <- integerLit sym d
          pure (VRational (SRational n' d'))
       , g3)

{-# INLINE randomWord #-}

-- | Generate a random word of the given length (i.e., a value of type @[w]@)
-- The size parameter is assumed to vary between 1 and 100, and we use
-- it to generate smaller numbers first.
randomWord :: Backend sym => sym -> Integer -> Gen sym
randomWord sym w _sz g =
   let (val, g1) = randomR (0,2^w-1) g
   in (return $ VWord w (WordVal <$> wordLit sym w val), g1)

{-# INLINE randomStream #-}

-- | Generate a random infinite stream value.
randomStream :: Backend sym => Gen sym -> Gen sym
randomStream mkElem sz g =
  let (g1,g2) = split g
  in (pure $ VStream $ IndexSeqMap $ genericIndex (unfoldr (Just . mkElem sz) g1), g2)

{-# INLINE randomSequence #-}

{- | Generate a random sequence.  This should be used for sequences
other than bits.  For sequences of bits use "randomWord". -}
randomSequence :: Backend sym => Integer -> Gen sym -> Gen sym
randomSequence w mkElem sz g0 = do
  let (g1,g2) = split g0
  let f g = let (x,g') = mkElem sz g
             in seq x (Just (x, g'))
  let xs = Seq.fromList $ genericTake w $ unfoldr f g1
  let v  = VSeq w $ IndexSeqMap $ \i -> Seq.index xs (fromInteger i)
  seq xs (pure v, g2)

{-# INLINE randomTuple #-}

-- | Generate a random tuple value.
randomTuple :: Backend sym => [Gen sym] -> Gen sym
randomTuple gens sz = go [] gens
  where
  go els [] g = (pure $ VTuple (reverse els), g)
  go els (mkElem : more) g =
    let (v, g1) = mkElem sz g
    in seq v (go (v : els) more g1)

{-# INLINE randomRecord #-}

-- | Generate a random record value.
randomRecord :: Backend sym => RecordMap Ident (Gen sym) -> Gen sym
randomRecord gens sz g0 =
  let (g', m) = recordMapAccum mk g0 gens in (pure $ VRecord m, g')
  where
    mk g gen =
      let (v, g') = gen sz g
      in seq v (g', v)

randomFloat ::
  Backend sym =>
  sym ->
  Integer {- ^ Exponent width -} ->
  Integer {- ^ Precision width -} ->
  Gen sym
randomFloat sym e p w g =
  ( VFloat <$> fpLit sym e p (nu % de)
  , g3
  )
  where
  -- XXX: we never generat NaN
  -- XXX: Not sure that we need such big integers, we should probably
  -- use `e` and `p` as a guide.
  (n,  g1) = if w < 100 then (w, g) else randomSize 8 100 g
  (nu, g2) = randomR (- 256^n, 256^n) g1
  (de, g3) = randomR (1, 256^n) g2





-- | A test result is either a pass, a failure due to evaluating to
-- @False@, or a failure due to an exception raised during evaluation
data TestResult
  = Pass
  | FailFalse [Value]
  | FailError EvalErrorEx [Value]

isPass :: TestResult -> Bool
isPass Pass = True
isPass _    = False

-- | Apply a testable value to some arguments.
-- Note that this function assumes that the values come from a call to
-- `testableType` (i.e., things are type-correct). We run in the IO
-- monad in order to catch any @EvalError@s.
evalTest :: Value -> [Value] -> IO TestResult
evalTest v0 vs0 = run `X.catch` handle
  where
    run = do
      result <- runEval mempty (go v0 vs0)
      if result
        then return Pass
        else return (FailFalse vs0)
    handle e = return (FailError e vs0)

    go :: Value -> [Value] -> Eval Bool
    go f@VFun{} (v : vs) = do f' <- fromVFun Concrete f (pure v)
                              go f' vs
    go VFun{}   []       = panic "Not enough arguments while applying function"
                           []

    -- TODO deal with VGen....
    --go (VGen m) []

    go (VTuple []) []    = return True
    go (VBit b) []       = return b

    go v vs              = do vdoc    <- ppValue Concrete defaultPPOpts v
                              vsdocs  <- mapM (ppValue Concrete defaultPPOpts) vs
                              panic "Type error while running test" $
                               [ "Function:"
                               , show vdoc
                               , "Arguments:"
                               ] ++ map show vsdocs

{- | Given a (function) type, compute data necessary for
     random or exhaustive testing.

     The first returned component is a count of the number of
     possible input test vectors, if the input types are finite.
     The second component is a list of all the types of the function
     inputs.  The third component is a list of all input test vectors
     for exhaustive testing.  This will be empty unless the
     input types are finite.  The final argument is a list of generators
     for the inputs of the function.

     This function will return @Nothing@ if the input type does not
     eventually return @Bit@, or if we cannot compute a generator
     for one of the inputs.
-}
testableType ::
  TValue ->
  Maybe (Maybe Integer, [TValue], [[Value]], [Gen Concrete])
testableType (TVFun t1 t2) =
   do let sz = typeSize t1
      g <- randomValue Concrete t1
      (tot,ts,vss,gs) <- testableType t2
      let tot' = liftM2 (*) sz tot
      let vss' = [ v : vs | v <- typeValues t1, vs <- vss ]
      return (tot', t1:ts, vss', g:gs)

testableType (TVGen v) = testableType v
testableType (TVTuple []) = return (Just 1, [], [[]], [])
testableType TVBit = return (Just 1, [], [[]], [])

testableType _ = Nothing

{- | Given a fully-evaluated type, try to compute the number of values in it.
Returns `Nothing` for infinite types, user-defined types, polymorphic types,
and, currently, function spaces.  Of course, we can easily compute the
sizes of function spaces, but we can't easily enumerate their inhabitants. -}
typeSize :: TValue -> Maybe Integer
typeSize ty = case ty of
  TVBit -> Just 2
  TVInteger -> Nothing
  TVRational -> Nothing
  TVIntMod n -> Just n
  TVFloat{} -> Nothing -- TODO?
  TVArray{} -> Nothing
  TVStream{} -> Nothing
  TVSeq n el -> (^ n) <$> typeSize el
  TVTuple els -> product <$> mapM typeSize els
  TVRec fs -> product <$> traverse typeSize fs
  TVFun{} -> Nothing
  TVAbstract{} -> Nothing
  TVGen{} -> Nothing
  TVNewtype _ _ tbody -> typeSize (TVRec tbody)

{- | Returns all the values in a type.  Returns an empty list of values,
for types where 'typeSize' returned 'Nothing'. -}
typeValues :: TValue -> [Value]
typeValues ty =
  case ty of
    TVBit      -> [ VBit False, VBit True ]
    TVInteger  -> []
    TVRational -> []
    TVIntMod n -> [ VInteger x | x <- [ 0 .. (n-1) ] ]
    TVFloat{}  -> [] -- TODO?
    TVArray{}  -> []
    TVStream{} -> []
    TVSeq n TVBit ->
      [ VWord n (pure (WordVal (BV n x)))
      | x <- [ 0 .. 2^n - 1 ]
      ]
    TVSeq n el ->
      [ VSeq n (finiteSeqMap (map pure xs))
      | xs <- sequence (genericReplicate n (typeValues el))
      ]
    TVTuple ts ->
      [ VTuple (map pure xs)
      | xs <- sequence (map typeValues ts)
      ]
    TVRec fs ->
      [ VRecord (fmap pure xs)
      | xs <- traverse typeValues fs
      ]
    TVFun{} -> []
    TVAbstract{} -> []
    TVGen{} -> []

    TVNewtype _ _ tbody -> typeValues (TVRec tbody)

--------------------------------------------------------------------------------
-- Driver function

exhaustiveTests :: MonadIO m =>
  (Integer -> m ()) {- ^ progress callback -} ->
  Value {- ^ function under test -} ->
  [[Value]] {- ^ exhaustive set of test values -} ->
  m (TestResult, Integer)
exhaustiveTests ppProgress val = go 0
  where
  go !testNum [] = return (Pass, testNum)
  go !testNum (vs:vss) =
    do ppProgress testNum
       res <- liftIO (evalTest val vs)
       case res of
         Pass -> go (testNum+1) vss
         failure -> return (failure, testNum)

randomTests :: MonadIO m =>
  (Integer -> m ()) {- ^ progress callback -} ->
  Integer {- ^ Maximum number of tests to run -} ->
  Value {- ^ function under test -} ->
  [Gen Concrete] {- ^ input value generators -} ->
  TFGen {- ^ Inital random generator -} ->
  m (TestResult, Integer)
randomTests ppProgress maxTests val gens = go 0
  where
  go !testNum g
    | testNum >= maxTests = return (Pass, testNum)
    | otherwise =
      do ppProgress testNum
         let sz' = 1 + fromInteger (div (100 * testNum) maxTests)
         (res, g') <- liftIO (runOneTest val gens sz' g)
         case res of
           Pass -> go (testNum+1) g'
           failure -> return (failure, testNum)
