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
{-# LANGUAGE MultiWayIf #-}
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
, returnTests'
, exhaustiveTests
, randomTests
, randomTests'
) where

import qualified Control.Exception as X
import Control.Monad          (liftM2)
import Control.Monad.IO.Class (MonadIO(..))
import Data.Bits
import Data.List              (unfoldr, genericTake, genericIndex,
                               genericReplicate, mapAccumL)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Sequence as Seq
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import System.Random.TF.Gen
import System.Random.TF.Instances

import Cryptol.Backend        (Backend(..), SRational(..))
import Cryptol.Backend.FloatHelpers (floatFromBits)
import Cryptol.Backend.Monad  (runEval,Eval,EvalErrorEx(..))
import Cryptol.Backend.Concrete
import Cryptol.Backend.SeqMap (indexSeqMap)
import Cryptol.Backend.WordValue (wordVal)

import Cryptol.Eval(evalEnumCon)
import Cryptol.Eval.Type      ( TValue(..), TNominalTypeValue(..), ConInfo(..)
                              , isNullaryCon )
import Cryptol.Eval.Value     ( GenValue(..), ppValue, defaultPPOpts, fromVFun, mkSeq, unsafeMkFinSeq)
import Cryptol.TypeCheck.Solver.InfNat (widthInteger, Nat' (..))
import Cryptol.Utils.Ident    (Ident)
import Cryptol.Utils.Panic    (panic)
import Cryptol.Utils.RecordMap

type Gen g x = Integer -> g -> (SEval x (GenValue x), g)


type Value = GenValue Concrete

{- | Apply a testable value to some randomly-generated arguments.
     Returns @Nothing@ if the function returned @True@, or
     @Just counterexample@ if it returned @False@.

    Please note that this function assumes that the generators match
    the supplied value, otherwise we'll panic.
 -}
runOneTest :: RandomGen g
        => Value   -- ^ Function under test
        -> [Gen g Concrete] -- ^ Argument generators
        -> Integer -- ^ Size
        -> g
        -> IO (TestResult, g)
runOneTest fun argGens sz g0 = do
  let (args, g1) = foldr mkArg ([], g0) argGens
      mkArg argGen (as, g) = let (a, g') = argGen sz g in (a:as, g')
  args' <- runEval mempty (sequence args)
  result <- evalTest fun args'
  return (result, g1)

returnOneTest :: RandomGen g
           => Value    -- ^ Function to be used to calculate tests
           -> [Gen g Concrete] -- ^ Argument generators
           -> Integer -- ^ Size
           -> g -- ^ Initial random state
           -> IO ([Value], Value, g) -- ^ Arguments, result, and new random state
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

returnTests :: RandomGen g
         => g -- ^ The random generator state
         -> [Gen g Concrete] -- ^ Generators for the function arguments
         -> Value -- ^ The function itself
         -> Int -- ^ How many tests?
         -> IO [([Value], Value)] -- ^ A list of pairs of random arguments and computed outputs
                                       --   as well as the new state of the RNG
returnTests g gens fun num = fst <$> returnTests' g gens fun num

-- | Return a collection of random tests.
returnTests' :: RandomGen g
         => g -- ^ The random generator state
         -> [Gen g Concrete] -- ^ Generators for the function arguments
         -> Value -- ^ The function itself
         -> Int -- ^ How many tests?
         -> IO ([([Value], Value)], g) -- ^ A list of pairs of random arguments and computed outputs
                                       --   as well as the new state of the RNG
returnTests' g gens fun num = go gens g 0
  where
    go args g0 n
      | n >= num = return ([], g0)
      | otherwise =
        do let sz = toInteger (div (100 * (1 + n)) num)
           (inputs, output, g1) <- returnOneTest fun args sz g0
           (more, g2) <- go args g1 (n + 1)
           return ((inputs, output) : more, g2)

{- | Given a (function) type, compute generators for the function's
arguments. -}
dumpableType :: forall g. RandomGen g => TValue -> Maybe [Gen g Concrete]
dumpableType (TVFun t1 t2) =
   do g  <- randomValue Concrete t1
      as <- dumpableType t2
      return (g : as)
dumpableType ty =
   do (_ :: Gen g Concrete) <- randomValue Concrete ty
      return []


{-# SPECIALIZE randomValue ::
  RandomGen g => Concrete -> TValue -> Maybe (Gen g Concrete)
  #-}

{- | A generator for values of the given type.  This fails if we are
given a type that lacks a suitable random value generator. -}
randomValue :: (Backend sym, RandomGen g) => sym -> TValue -> Maybe (Gen g sym)
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
            return (randomSequence sym n el mk)
    TVStream el  ->
         do mk <- randomValue sym el
            return (randomStream mk)
    TVTuple els ->
         do mks <- mapM (randomValue sym) els
            return (randomTuple mks)
    TVRec fs ->
         do gs <- traverse (randomValue sym) fs
            return (randomRecord gs)

    TVNominal _ _ nval ->
      case nval of
        TVStruct fs ->
          do gs <- traverse (randomValue sym) fs
             return (randomRecord gs)
        TVEnum cons -> randomCon sym <$>
                          traverse (traverse (randomValue sym)) cons
        TVAbstract -> Nothing

    TVArray{} -> Nothing
    TVFun{} -> Nothing

{-# INLINE randomBit #-}

-- | Generate a random bit value.
randomBit :: (Backend sym, RandomGen g) => sym -> Gen g sym
randomBit sym _ g =
  let (b,g1) = random g
  in (pure (VBit (bitLit sym b)), g1)

{-# INLINE randomSize #-}

randomSize :: RandomGen g => Int -> Int -> g -> (Int, g)
randomSize k n g
  | p == 1 = (n, g')
  | otherwise = randomSize k (n + 1) g'
  where (p, g') = randomR (1, k) g

{-# INLINE randomInteger #-}

-- | Generate a random integer value. The size parameter is assumed to
-- vary between 1 and 100, and we use it to generate smaller numbers
-- first.
randomInteger :: (Backend sym, RandomGen g) => sym -> Gen g sym
randomInteger sym w g =
  let (n, g1) = if w < 100 then (fromInteger w, g) else randomSize 8 100 g
      (i, g2) = randomR (- 256^n, 256^n) g1
  in (VInteger <$> integerLit sym i, g2)

{-# INLINE randomIntMod #-}

randomIntMod :: (Backend sym, RandomGen g) => sym -> Integer -> Gen g sym
randomIntMod sym modulus _ g =
  let (i, g') = randomR (0, modulus-1) g
  in (VInteger <$> integerLit sym i, g')

{-# INLINE randomRational #-}

randomRational :: (Backend sym, RandomGen g) => sym -> Gen g sym
randomRational sym w g =
  let (sz, g1) = if w < 100 then (fromInteger w, g) else randomSize 8 100 g
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
randomWord :: (Backend sym, RandomGen g) => sym -> Integer -> Gen g sym
randomWord sym w _sz g =
   let (val, g1) = randomR (0,2^w-1) g
   in (VWord . wordVal <$> wordLit sym w val, g1)

{-# INLINE randomStream #-}

-- | Generate a random infinite stream value.
randomStream :: (Backend sym, RandomGen g) => Gen g sym -> Gen g sym
randomStream mkElem sz g =
  let (g1,g2) = split g
  in (pure $ VStream $ indexSeqMap $ genericIndex (unfoldr (Just . mkElem sz) g1), g2)

{-# INLINE randomSequence #-}

{- | Generate a random sequence.  This should be used for sequences
other than bits.  For sequences of bits use "randomWord". -}
randomSequence :: (Backend sym, RandomGen g) => sym -> Integer -> TValue -> Gen g sym -> Gen g sym
randomSequence sym w elty mkElem sz g0 = do
  let (g1,g2) = split g0
  let f g = let (x,g') = mkElem sz g
             in seq x (Just (x, g'))
  let xs = Seq.fromList $ genericTake w $ unfoldr f g1
  let v  = mkSeq sym (Nat w) elty $ indexSeqMap $ \i -> Seq.index xs (fromInteger i)
  seq xs (v, g2)

{-# INLINE randomTuple #-}

-- | Generate a random tuple value.
randomTuple :: (Backend sym, RandomGen g) => [Gen g sym] -> Gen g sym
randomTuple gens sz = go [] gens
  where
  go els [] g = (pure $ VTuple (reverse els), g)
  go els (mkElem : more) g =
    let (v, g1) = mkElem sz g
    in seq v (go (v : els) more g1)

{-# INLINE randomRecord #-}

-- | Generate a random record value.
randomRecord :: (Backend sym, RandomGen g) => RecordMap Ident (Gen g sym) -> Gen g sym
randomRecord gens sz g0 =
  let (g', m) = recordMapAccum mk g0 gens in (pure $ VRecord m, g')
  where
    mk g gen =
      let (v, g') = gen sz g
      in seq v (g', v)

-- | Generate a random constructor value belonging to an enum definition.
--
-- For the purposes of random testing, constructors with zero fields (i.e.,
-- nullary constructors) are less interesting than constructors with at least
-- one field (i.e., non-nullary constructors). For example, given
-- @enum Maybe a = Nothing | Just a@, we would like to generate more @Just@
-- values than @Nothing@ values. To ensure this, we employ the following
-- approach:
--
-- 1. If all constructors are nullary, then randomly pick one of these
--    constructors, where each constructor has an equal chance of being picked.
--
-- 2. If all constructors are non-nullary, then randomly pick one of these
--    constructors, where each constructor has an equal chance of being picked.
--    Then pick random values for each field in the constructor.
--
-- 3. Otherwise, pick a random number between 1 and 100. If the number is less
--    than or equal to 25, then randomly pick a nullary constructor. Otherwise,
--    randomly pick a non-nullary constructor. This biases the results so that
--    nullary constructors are only picked ~25% of the time.
randomCon ::
  forall sym g.
  (Backend sym, RandomGen g) =>
  sym ->
  Vector (ConInfo (Gen g sym)) ->
  Gen g sym
randomCon sym cons
    -- (1) from the Haddocks
  | null nonNullaryCons
  = randomCon' nullaryLen nullaryCons

    -- (2) from the Haddocks
  | null nullaryCons
  = randomCon' nonNullaryLen nonNullaryCons

    -- (3) from the Haddocks
  | otherwise
  = \sz g0 ->
      let (x :: Int, g1) = randomR (1, 100) g0 in
      if x <= 25
         then randomCon' nullaryLen nullaryCons sz g1
         else randomCon' nonNullaryLen nonNullaryCons sz g1
  where
    (nullaryLen,nullaryCons, nonNullaryLen, nonNullaryCons) =
       let check (!nullLen,nullary,!nonNullLen,nonNullary) i con
             | isNullaryCon con = ( 1+nullLen,(i,con) : nullary
                                  , nonNullLen, nonNullary)
             | otherwise        = (nullLen, nullary
                                  , 1+nonNullLen, (i,con) : nonNullary)
        in Vector.ifoldl' check (0,[],0,[]) cons

    randomCon' :: Int -> [(Int, ConInfo (Gen g sym))] -> Gen g sym
    randomCon' conLen cons' sz g0 =
      let (idx, g1) = randomR (0, conLen - 1) g0
          (num, con) = cons' !! idx
          (g2, !flds') =
            mapAccumL
              (\g gen ->
                let (v, g') = gen sz g in
                seq v (g', v))
              g1 (conFields con) in
      (($ flds') <$> evalEnumCon sym (conIdent con) num, g2)

randomFloat ::
  (Backend sym, RandomGen g) =>
  sym ->
  Integer {- ^ Exponent width -} ->
  Integer {- ^ Precision width -} ->
  Gen g sym
randomFloat sym e p w g0 =
    let sz = max 0 (min 100 w)
        ( x, g') = randomR (0, 10*(sz+1)) g0
     in if | x < 2    -> (VFloat <$> fpNaN sym e p, g')
           | x < 4    -> (VFloat <$> fpPosInf sym e p, g')
           | x < 6    -> (VFloat <$> (fpNeg sym =<< fpPosInf sym e p), g')
           | x < 8    -> (VFloat <$> fpLit sym e p 0, g')
           | x < 10   -> (VFloat <$> (fpNeg sym =<< fpLit sym e p 0), g')
           | x <= sz       -> genSubnormal g'  -- about 10% of the time
           | x <= 4*(sz+1) -> genBinary g'     -- about 40%
           | otherwise     -> genNormal (toInteger sz) g'  -- remaining ~50%

  where
    emax = bit (fromInteger e) - 1
    smax = bit (fromInteger p) - 1

    -- generates floats uniformly chosen from among all bitpatterns
    genBinary g =
      let (v, g1) = randomR (0, bit (fromInteger (e+p)) - 1) g
       in (VFloat <$> (fpFromBits sym e p =<< wordLit sym (e+p) v), g1)

    -- generates floats corresponding to subnormal values.  These are
    -- values with 0 biased exponent and nonzero mantissa.
    genSubnormal g =
      let (sgn, g1) = random g
          (v, g2)   = randomR (1, bit (fromInteger p) - 1) g1
       in (VFloat <$> ((if sgn then fpNeg sym else pure) =<< fpFromBits sym e p =<< wordLit sym (e+p) v), g2)

    -- generates floats where the exponent and mantissa are scaled by the size
    genNormal sz g =
      let (sgn, g1) = random g
          (ex,  g2) = randomR ((1-emax)*sz `div` 100, (sz*emax) `div` 100) g1
          (mag, g3) = randomR (1, max 1 ((sz*smax) `div` 100)) g2
          r  = fromInteger mag ^^ (ex - widthInteger mag)
          r' = if sgn then negate r else r
       in (VFloat <$> fpLit sym e p r', g3)


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
testableType :: RandomGen g =>
  TValue ->
  Maybe (Maybe Integer, [TValue], [[Value]], [Gen g Concrete])
testableType (TVFun t1 t2) =
   do let sz = typeSize t1
      g <- randomValue Concrete t1
      (tot,ts,vss,gs) <- testableType t2
      let tot' = liftM2 (*) sz tot
      let vss' = [ v : vs | v <- typeValues t1, vs <- vss ]
      return (tot', t1:ts, vss', g:gs)
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
  TVFloat e p -> Just (2 ^ (e+p))
  TVArray{} -> Nothing
  TVStream{} -> Nothing
  TVSeq n el -> (^ n) <$> typeSize el
  TVTuple els -> product <$> mapM typeSize els
  TVRec fs -> product <$> traverse typeSize fs
  TVFun{} -> Nothing
  TVNominal _ _ nv ->
    case nv of
      TVStruct tbody -> typeSize (TVRec tbody)
      TVEnum cons -> sum <$> mapM (conSize . conFields) cons
        where conSize = foldr (\t sz -> liftM2 (*) (typeSize t) sz) (Just 1)
      TVAbstract -> Nothing

{- | Returns all the values in a type.  Returns an empty list of values,
for types where 'typeSize' returned 'Nothing'. -}
typeValues :: TValue -> [Value]
typeValues ty =
  case ty of
    TVBit       -> [ VBit False, VBit True ]
    TVInteger   -> []
    TVRational  -> []
    TVIntMod n  -> [ VInteger x | x <- [ 0 .. (n-1) ] ]
    TVFloat e p -> [ VFloat (floatFromBits e p v) | v <- [0 .. 2^(e+p) - 1] ]
    TVArray{}   -> []
    TVStream{}  -> []
    TVSeq n TVBit ->
      [ VWord (wordVal (BV n x))
      | x <- [ 0 .. 2^n - 1 ]
      ]
    TVSeq n el ->
      [ VFinSeq (unsafeMkFinSeq Concrete n xs) -- safe, since the TVBit case is covered above
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
    TVNominal _ _ nv ->
      case nv of
        TVStruct tbody -> typeValues (TVRec tbody)
        TVEnum cons ->
          [ VEnum (toInteger tag) (IntMap.singleton tag con')
          | (tag,con) <- zip [0..] (Vector.toList cons)
          , vs        <- mapM typeValues (conFields con)
          , let con' = con { conFields = pure <$> vs }
          ]
        TVAbstract -> []

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

randomTests :: (MonadIO m, RandomGen g) =>
  (Integer -> m ()) {- ^ progress callback -} ->
  Integer {- ^ Maximum number of tests to run -} ->
  Value {- ^ function under test -} ->
  [Gen g Concrete] {- ^ input value generators -} ->
  g {- ^ Inital random generator -} ->
  m (TestResult, Integer)
randomTests ppProgress maxTests val gens g = fst <$> randomTests' ppProgress maxTests val gens g

randomTests' :: (MonadIO m, RandomGen g) =>
  (Integer -> m ()) {- ^ progress callback -} ->
  Integer {- ^ Maximum number of tests to run -} ->
  Value {- ^ function under test -} ->
  [Gen g Concrete] {- ^ input value generators -} ->
  g {- ^ Inital random generator -} ->
  m ((TestResult, Integer), g)
randomTests' ppProgress maxTests val gens = go 0
  where
  go !testNum g
    | testNum >= maxTests = return ((Pass, testNum), g)
    | otherwise =
      do ppProgress testNum
         let sz' = div (100 * (1 + testNum)) maxTests
         (res, g') <- liftIO (runOneTest val gens sz' g)
         case res of
           Pass -> go (testNum+1) g'
           failure -> return ((failure, testNum), g)
