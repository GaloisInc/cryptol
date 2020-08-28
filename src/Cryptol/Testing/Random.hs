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
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TypeFamilies #-}
module Cryptol.Testing.Random
  ( dumpableType
  , runTests
  , runOneTest
  , testableType
  , testableTypeGenerators
  , returnTests
  , isPass
  , evalTest
  , TestSpec(..)
  , TestReport(..)
  , TestResult(..)
  , randomV
  ) where

import qualified Control.Exception as X
import Control.Monad          (join, liftM2)
import Data.Ratio             ((%))
import Data.Bits              ( (.&.), shiftR )
import Data.List              (unfoldr, genericTake, genericIndex, genericReplicate)

import System.Random          (RandomGen, split, random, randomR)
import System.Random.TF.Gen   (seedTFGen)

import Cryptol.Eval.Backend   (Backend(..), SRational(..))
import Cryptol.Eval.Concrete.Value
import Cryptol.Eval.Monad     (ready,runEval,Eval,EvalError(..))
import Cryptol.Eval.Type      (TValue(..))
import Cryptol.Eval.Value     (GenValue(..), word, generateSeqMap, finiteSeqMap,
                               finiteSeqMap', unpackSeqMap')
import Cryptol.Eval.Generic   (zeroV)
import Cryptol.TypeCheck.Solver.InfNat (Nat'(..))

import Cryptol.Utils.Ident    (Ident)
import Cryptol.Utils.Panic    (panic)
import Cryptol.Utils.RecordMap

type Gen g sym = Integer -> g -> (SEval sym (GenValue sym), g)


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
  args' <- runEval (sequence args)
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
     args' <- runEval (sequence args)
     result <- runEval (go fun args')
     return (args', result, g1)
   where
     go (VFun f) (v : vs) = join (go <$> (f (ready v)) <*> pure vs)
     go (VFun _) [] = panic "Cryptol.Testing.Random" ["Not enough arguments to function while generating tests"]
     go _ (_ : _) = panic "Cryptol.Testing.Random" ["Too many arguments to function while generating tests"]
     go v [] = return v


-- | Return a collection of random tests.
returnTests :: RandomGen g
         => g -- ^ The random generator state
         -> [Gen g Concrete] -- ^ Generators for the function arguments
         -> Value -- ^ The function itself
         -> Int -- ^ How many tests?
         -> IO [([Value], Value)] -- ^ A list of pairs of random arguments and computed outputs
returnTests g gens fun num = go gens g 0
  where
    go args g0 n
      | n >= num = return []
      | otherwise =
        do let sz = toInteger (div (100 * (1 + n)) num)
           (inputs, output, g1) <- returnOneTest fun args sz g0
           more <- go args g1 (n + 1)
           return ((inputs, output) : more)

{- | Given a (function) type, compute generators for the function's
arguments. This is like 'testableTypeGenerators', but allows the result to be
any finite type instead of just @Bit@. -}
dumpableType :: forall g. RandomGen g => TValue -> Maybe [Gen g Concrete]
dumpableType ty =
  case ty of
    TVFun t1 t2 ->
      do g  <- randomValue Concrete t1
         as <- testableTypeGenerators t2
         return (g : as)
    _ ->
      do (_ :: Gen g Concrete) <- randomValue Concrete ty
         return []

{- | Given a (function) type, compute generators for
the function's arguments. Currently we do not support polymorphic functions.
In principle, we could apply these to random types, and test the results. -}
testableTypeGenerators :: RandomGen g => TValue -> Maybe [Gen g Concrete]
testableTypeGenerators ty =
  case ty of
    TVFun t1 t2 ->
      do g <- randomValue Concrete t1
         as <- testableTypeGenerators t2
         return (g:as)
    TVBit -> return []
    _ -> Nothing

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
    TVIntMod n    -> Just (randomIntMod sym n)
    TVFloat e p   -> Just (randomFloat sym e p)
    TVSeq n TVBit -> return (randomWord sym n)
    TVSeq n el    -> randomSequence sym n el <$> randomValue sym el
    TVStream el   -> randomStream sym el <$> randomValue sym el
    TVTuple ts    -> randomTuple <$> mapM (randomValue sym) ts
    TVRec fs      -> randomRecord <$> traverse (randomValue sym) fs
    TVArray{}     -> Nothing
    TVFun{}       -> Nothing
    TVAbstract{}  -> Nothing

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
   let (val, g1) = randomR (0,2^w - 1) g
    in (word sym w val, g1)

{-# INLINE randomStream #-}

-- | Generate a random infinite stream value.
randomStream :: (Backend sym, RandomGen g) => sym -> TValue -> Gen g sym -> Gen g sym
randomStream sym a mkElem sz g =
  let (g1,g2) = split g
      xs = (unfoldr (Just . mkElem sz) g1)
   in (VSeq Inf a <$> generateSeqMap sym (genericIndex xs), g2)

{-# INLINE randomSequence #-}

{- | Generate a random sequence.  This should be used for sequences
other than bits.  For sequences of bits use "randomWord". -}
randomSequence :: (Backend sym, RandomGen g) => sym -> Integer -> TValue -> Gen g sym -> Gen g sym
randomSequence sym w a mkElem sz g0 =
  let (g1,g2) = split g0
      f g = let (x,g') = mkElem sz g
             in seq x (Just (x, g'))
      xs = genericTake w $ unfoldr f g1
   in (VSeq (Nat w) a <$> finiteSeqMap sym xs, g2)

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

randomFloat ::
  (Backend sym, RandomGen g) =>
  sym ->
  Integer {- ^ Exponent width -} ->
  Integer {- ^ Precision width -} ->
  Gen g sym
randomFloat sym e p w g =
  ( VFloat <$> fpLit sym e p (nu % de)
  , g3
  )
  where
  -- XXX: we never generat NaN
  -- XXX: Not sure that we need such big integers, we should probably
  -- use `e` and `p` as a guide.
  (n,  g1) = if w < 100 then (fromInteger w, g) else randomSize 8 100 g
  (nu, g2) = randomR (- 256^n, 256^n) g1
  (de, g3) = randomR (1, 256^n) g2




-- Random Values ---------------------------------------------------------------

{-# SPECIALIZE randomV ::
  Concrete -> TValue -> Integer -> SEval Concrete (GenValue Concrete)
  #-}

-- | Produce a random value with the given seed. If we do not support
-- making values of the given type, return zero of that type.
-- TODO: do better than returning zero
randomV :: Backend sym => sym -> TValue -> Integer -> SEval sym (GenValue sym)
randomV sym ty seed =
  case randomValue sym ty of
    Nothing -> zeroV sym ty
    Just gen ->
      -- unpack the seed into four Word64s
      let mask64 = 0xFFFFFFFFFFFFFFFF
          unpack s = fromInteger (s .&. mask64) : unpack (s `shiftR` 64)
          [a, b, c, d] = take 4 (unpack seed)
      in fst $ gen 100 $ seedTFGen (a, b, c, d)


-- | A test result is either a pass, a failure due to evaluating to
-- @False@, or a failure due to an exception raised during evaluation
data TestResult
  = Pass
  | FailFalse [Value]
  | FailError EvalError [Value]

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
      result <- runEval (go v0 vs0)
      if result
        then return Pass
        else return (FailFalse vs0)
    handle e = return (FailError e vs0)

    go :: Value -> [Value] -> Eval Bool
    go (VFun f) (v : vs) = join (go <$> (f (ready v)) <*> return vs)
    go (VFun _) []       = panic "Not enough arguments while applying function"
                           []
    go (VBit b) []       = return b
    go _v _vs            = panic "Type error while running test" [] -- TODO, better?
{-
do vdoc    <- ppValue Concrete defaultPPOpts tp v
                              vsdocs  <- mapM (ppValue Concrete defaultPPOpts) vs
                              
                               [ "Function:"
                               , show vdoc
                               , "Arguments:"
                               ] ++ map show vsdocs
-}

{- | Given a (function) type, compute all possible inputs for it.
We also return the types of the arguments and
the total number of test (i.e., the length of the outer list. -}
testableType :: TValue -> Maybe (Maybe Integer, [TValue], [[Value]])
testableType ty =
  case ty of
    TVFun t1 t2 ->
      do let sz = typeSize t1
         (tot,ts,vss) <- testableType t2
         return (liftM2 (*) sz tot, t1:ts, [ v : vs | v <- typeValues t1, vs <- vss ])
    TVBit -> return (Just 1, [], [[]])
    _ -> Nothing

{- | Given a fully-evaluated type, try to compute the number of values in it.
Returns `Nothing` for infinite types, user-defined types, polymorphic types,
and, currently, function spaces.  Of course, we can easily compute the
sizes of function spaces, but we can't easily enumerate their inhabitants. -}
typeSize :: TValue -> Maybe Integer
typeSize ty =
  case ty of
    TVBit        -> Just 2
    TVIntMod n   -> Just n
    TVInteger    -> Nothing
    TVRational   -> Nothing
    TVFloat{}    -> Nothing -- TODO?
    TVSeq n el   -> (^ n) <$> typeSize el
    TVStream{}   -> Nothing
    TVFun{}      -> Nothing
    TVTuple ts   -> product <$> mapM typeSize ts
    TVRec fs     -> product <$> traverse typeSize fs
    TVAbstract{} -> Nothing
    TVArray{}    -> Nothing

{- | Returns all the values in a type.  Returns an empty list of values,
for types where 'typeSize' returned 'Nothing'. -}
typeValues :: TValue -> [Value]
typeValues ty =
  case ty of
    TVBit         -> [ VBit False, VBit True ]
    TVIntMod n    -> VInteger <$> [ 0 .. n-1 ]
    TVInteger     -> []
    TVRational    -> []
    TVFloat{}     -> [] -- TODO?
    TVSeq n TVBit -> [ VSeq (Nat n) TVBit (unpackSeqMap' (BV n x))
                     | x <- [ 0 .. 2^n - 1]
                     ]
    TVSeq n a     -> [ VSeq (Nat n) a (finiteSeqMap' (map ready xs))
                     | xs <- sequence (genericReplicate n (typeValues a))
                     ]
    TVStream{}    -> []

    TVTuple ts    -> [ VTuple (fmap ready xs)
                     | xs <- mapM typeValues ts
                     ]
    TVRec fs      -> [ VRecord (fmap ready xs)
                     | xs <- traverse typeValues fs
                     ]

    TVFun{}       -> []
    TVAbstract{}  -> []
    TVArray{}     -> []

--------------------------------------------------------------------------------
-- Driver function

data TestSpec m s = TestSpec {
    testFn :: Integer -> s -> m (TestResult, s)
  , testProp :: String -- ^ The property as entered by the user
  , testTotal :: Integer
  , testPossible :: Maybe Integer -- ^ Nothing indicates infinity
  , testRptProgress :: Integer -> Integer -> m ()
  , testClrProgress :: m ()
  , testRptFailure :: TestResult -> m ()
  , testRptSuccess :: m ()
  }

data TestReport = TestReport {
    reportResult :: TestResult
  , reportProp :: String -- ^ The property as entered by the user
  , reportTestsRun :: Integer
  , reportTestsPossible :: Maybe Integer
  }

runTests :: Monad m => TestSpec m s -> s -> m TestReport
runTests TestSpec {..} st0 = go 0 st0
  where
  go testNum _ | testNum >= testTotal = do
    testRptSuccess
    return $ TestReport Pass testProp testNum testPossible
  go testNum st =
   do testRptProgress testNum testTotal
      res <- testFn (div (100 * (1 + testNum)) testTotal) st
      testClrProgress
      case res of
        (Pass, st') -> do -- delProgress -- unnecessary?
          go (testNum + 1) st'
        (failure, _st') -> do
          testRptFailure failure
          return $ TestReport failure testProp testNum testPossible
