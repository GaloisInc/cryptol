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
module Cryptol.Testing.Random where

import qualified Control.Exception as X
import Control.Monad          (join, liftM2)
import Data.Bits              ( (.&.), shiftR )
import Data.List              (unfoldr, genericTake, genericIndex, genericReplicate)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Sequence as Seq

import System.Random          (RandomGen, split, random, randomR)
import System.Random.TF.Gen   (seedTFGen)

import Cryptol.Eval.Backend   (Backend(..), SRational(..))
import Cryptol.Eval.Concrete.Value
import Cryptol.Eval.Monad     (ready,runEval,EvalOpts,Eval,EvalError(..))
import Cryptol.Eval.Type      (TValue(..), tValTy)
import Cryptol.Eval.Value     (GenValue(..),SeqMap(..), WordValue(..),
                               ppValue, defaultPPOpts, finiteSeqMap)
import Cryptol.Eval.Generic   (zeroV)
import Cryptol.TypeCheck.AST  (Type(..), TCon(..), TC(..), tNoUser, tIsFun)
import Cryptol.TypeCheck.SimpType(tRebuild')

import Cryptol.Utils.Ident    (Ident)
import Cryptol.Utils.Panic    (panic)

type Gen g x = Integer -> g -> (SEval x (GenValue x), g)


{- | Apply a testable value to some randomly-generated arguments.
     Returns @Nothing@ if the function returned @True@, or
     @Just counterexample@ if it returned @False@.

    Please note that this function assumes that the generators match
    the supplied value, otherwise we'll panic.
 -}
runOneTest :: RandomGen g
        => EvalOpts   -- ^ how to evaluate things
        -> Value   -- ^ Function under test
        -> [Gen g Concrete] -- ^ Argument generators
        -> Integer -- ^ Size
        -> g
        -> IO (TestResult, g)
runOneTest evOpts fun argGens sz g0 = do
  let (args, g1) = foldr mkArg ([], g0) argGens
      mkArg argGen (as, g) = let (a, g') = argGen sz g in (a:as, g')
  args' <- runEval evOpts (sequence args)
  result <- evalTest evOpts fun args'
  return (result, g1)

returnOneTest :: RandomGen g
           => EvalOpts -- ^ How to evaluate things
           -> Value    -- ^ Function to be used to calculate tests
           -> [Gen g Concrete] -- ^ Argument generators
           -> Integer -- ^ Size
           -> g -- ^ Initial random state
           -> IO ([Value], Value, g) -- ^ Arguments, result, and new random state
returnOneTest evOpts fun argGens sz g0 =
  do let (args, g1) = foldr mkArg ([], g0) argGens
         mkArg argGen (as, g) = let (a, g') = argGen sz g in (a:as, g')
     args' <- runEval evOpts (sequence args)
     result <- runEval evOpts (go fun args')
     return (args', result, g1)
   where
     go (VFun f) (v : vs) = join (go <$> (f (ready v)) <*> pure vs)
     go (VFun _) [] = panic "Cryptol.Testing.Random" ["Not enough arguments to function while generating tests"]
     go _ (_ : _) = panic "Cryptol.Testing.Random" ["Too many arguments to function while generating tests"]
     go v [] = return v


-- | Return a collection of random tests.
returnTests :: RandomGen g
         => g -- ^ The random generator state
         -> EvalOpts -- ^ How to evaluate things
         -> [Gen g Concrete] -- ^ Generators for the function arguments
         -> Value -- ^ The function itself
         -> Int -- ^ How many tests?
         -> IO [([Value], Value)] -- ^ A list of pairs of random arguments and computed outputs
returnTests g evo gens fun num = go gens g 0
  where
    go args g0 n
      | n >= num = return []
      | otherwise =
        do let sz = toInteger (div (100 * (1 + n)) num)
           (inputs, output, g1) <- returnOneTest evo fun args sz g0
           more <- go args g1 (n + 1)
           return ((inputs, output) : more)

{- | Given a (function) type, compute generators for the function's
arguments. This is like 'testableTypeGenerators', but allows the result to be
any finite type instead of just @Bit@. -}
dumpableType :: forall g. RandomGen g => Type -> Maybe [Gen g Concrete]
dumpableType ty =
  case tIsFun ty of
    Just (t1, t2) ->
      do g  <- randomValue Concrete t1
         as <- testableTypeGenerators t2
         return (g : as)
    Nothing ->
      do (_ :: Gen g Concrete) <- randomValue Concrete ty
         return []

{- | Given a (function) type, compute generators for
the function's arguments. Currently we do not support polymorphic functions.
In principle, we could apply these to random types, and test the results. -}
testableTypeGenerators :: RandomGen g => Type -> Maybe [Gen g Concrete]
testableTypeGenerators ty =
  case tNoUser ty of
    TCon (TC TCFun) [t1,t2] ->
      do g  <- randomValue Concrete t1
         as <- testableTypeGenerators t2
         return (g : as)
    TCon (TC TCBit) [] -> return []
    _ -> Nothing


{-# SPECIALIZE randomValue ::
  RandomGen g => Concrete -> Type -> Maybe (Gen g Concrete)
  #-}

{- | A generator for values of the given type.  This fails if we are
given a type that lacks a suitable random value generator. -}
randomValue :: (Backend sym, RandomGen g) => sym -> Type -> Maybe (Gen g sym)
randomValue sym ty =
  case ty of
    TCon tc ts  ->
      case (tc, map (tRebuild' False) ts) of
        (TC TCBit, [])                        -> Just (randomBit sym)

        (TC TCInteger, [])                    -> Just (randomInteger sym)

        (TC TCRational, [])                   -> Just (randomRational sym)

        (TC TCIntMod, [TCon (TC (TCNum n)) []]) ->
          do return (randomIntMod sym n)

        (TC TCSeq, [TCon (TC TCInf) [], el])  ->
          do mk <- randomValue sym el
             return (randomStream mk)

        (TC TCSeq, [TCon (TC (TCNum n)) [], TCon (TC TCBit) []]) ->
            return (randomWord sym n)

        (TC TCSeq, [TCon (TC (TCNum n)) [], el]) ->
          do mk <- randomValue sym el
             return (randomSequence n mk)

        (TC (TCTuple _), els) ->
          do mks <- mapM (randomValue sym) els
             return (randomTuple mks)

        _ -> Nothing

    TVar _      -> Nothing
    TUser _ _ t -> randomValue sym t
    TRec fs     -> do gs <- traverse (randomValue sym) (Map.fromList fs)
                      return (randomRecord gs)

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
   in (return $ VWord w (WordVal <$> wordLit sym w val), g1)

{-# INLINE randomStream #-}

-- | Generate a random infinite stream value.
randomStream :: (Backend sym, RandomGen g) => Gen g sym -> Gen g sym
randomStream mkElem sz g =
  let (g1,g2) = split g
  in (pure $ VStream $ IndexSeqMap $ genericIndex (unfoldr (Just . mkElem sz) g1), g2)

{-# INLINE randomSequence #-}

{- | Generate a random sequence.  This should be used for sequences
other than bits.  For sequences of bits use "randomWord". -}
randomSequence :: (Backend sym, RandomGen g) => Integer -> Gen g sym -> Gen g sym
randomSequence w mkElem sz g0 = do
  let (g1,g2) = split g0
  let f g = let (x,g') = mkElem sz g
             in seq x (Just (x, g'))
  let xs = Seq.fromList $ genericTake w $ unfoldr f g1
  seq xs (pure $ VSeq w $ IndexSeqMap $ (Seq.index xs . fromInteger), g2)

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
randomRecord :: (Backend sym, RandomGen g) => Map Ident (Gen g sym) -> Gen g sym
randomRecord gens sz g0 =
  let (g', m) = Map.mapAccum mk g0 gens in (pure $ VRecord m, g')
  where
    mk g gen =
      let (v, g') = gen sz g
      in seq v (g', v)


-- Random Values ---------------------------------------------------------------

{-# SPECIALIZE randomV ::
  Concrete -> TValue -> Integer -> SEval Concrete (GenValue Concrete)
  #-}

-- | Produce a random value with the given seed. If we do not support
-- making values of the given type, return zero of that type.
-- TODO: do better than returning zero
randomV :: Backend sym => sym -> TValue -> Integer -> SEval sym (GenValue sym)
randomV sym ty seed =
  case randomValue sym (tValTy ty) of
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
evalTest :: EvalOpts -> Value -> [Value] -> IO TestResult
evalTest evOpts v0 vs0 = run `X.catch` handle
  where
    run = do
      result <- runEval evOpts (go v0 vs0)
      if result
        then return Pass
        else return (FailFalse vs0)
    handle e = return (FailError e vs0)

    go :: Value -> [Value] -> Eval Bool
    go (VFun f) (v : vs) = join (go <$> (f (ready v)) <*> return vs)
    go (VFun _) []       = panic "Not enough arguments while applying function"
                           []
    go (VBit b) []       = return b
    go v vs              = do vdoc    <- ppValue Concrete defaultPPOpts v
                              vsdocs  <- mapM (ppValue Concrete defaultPPOpts) vs
                              panic "Type error while running test" $
                               [ "Function:"
                               , show vdoc
                               , "Arguments:"
                               ] ++ map show vsdocs

{- | Given a (function) type, compute all possible inputs for it.
We also return the types of the arguments and
the total number of test (i.e., the length of the outer list. -}
testableType :: Type -> Maybe (Maybe Integer, [Type], [[Value]])
testableType ty =
  case tNoUser ty of
    TCon (TC TCFun) [t1,t2] ->
      do let sz = typeSize t1
         (tot,ts,vss) <- testableType t2
         return (liftM2 (*) sz tot, t1:ts, [ v : vs | v <- typeValues t1, vs <- vss ])
    TCon (TC TCBit) [] -> return (Just 1, [], [[]])
    _ -> Nothing

{- | Given a fully-evaluated type, try to compute the number of values in it.
Returns `Nothing` for infinite types, user-defined types, polymorphic types,
and, currently, function spaces.  Of course, we can easily compute the
sizes of function spaces, but we can't easily enumerate their inhabitants. -}
typeSize :: Type -> Maybe Integer
typeSize ty =
  case ty of
    TVar _      -> Nothing
    TUser _ _ t -> typeSize t
    TRec fs     -> product <$> mapM (typeSize . snd) fs
    TCon (TC tc) ts ->
      case (tc, ts) of
        (TCNum _, _)     -> Nothing
        (TCInf, _)       -> Nothing
        (TCBit, _)       -> Just 2
        (TCInteger, _)   -> Nothing
        (TCRational, _)  -> Nothing
        (TCIntMod, [sz]) -> case tNoUser sz of
                              TCon (TC (TCNum n)) _ -> Just n
                              _                     -> Nothing
        (TCIntMod, _)    -> Nothing
        (TCSeq, [sz,el]) -> case tNoUser sz of
                              TCon (TC (TCNum n)) _ -> (^ n) <$> typeSize el
                              _                     -> Nothing
        (TCSeq, _)       -> Nothing
        (TCFun, _)       -> Nothing
        (TCTuple _, els) -> product <$> mapM typeSize els
        (TCAbstract _, _) -> Nothing
        (TCNewtype _, _) -> Nothing

    TCon _ _ -> Nothing


{- | Returns all the values in a type.  Returns an empty list of values,
for types where 'typeSize' returned 'Nothing'. -}
typeValues :: Type -> [Value]
typeValues ty =
  case ty of
    TVar _      -> []
    TUser _ _ t -> typeValues t
    TRec fs     -> [ VRecord (fmap ready xs)
                   | xs <- sequence (fmap typeValues (Map.fromList fs))
                   ]
    TCon (TC tc) ts ->
      case tc of
        TCNum _     -> []
        TCInf       -> []
        TCBit       -> [ VBit False, VBit True ]
        TCInteger   -> []
        TCRational  -> []
        TCIntMod    ->
          case map tNoUser ts of
            [ TCon (TC (TCNum n)) _ ] | 0 < n ->
              [ VInteger x | x <- [ 0 .. n - 1 ] ]
            _ -> []
        TCSeq       ->
          case map tNoUser ts of
            [ TCon (TC (TCNum n)) _, TCon (TC TCBit) [] ] ->
              [ VWord n (ready (WordVal (BV n x))) | x <- [ 0 .. 2^n - 1 ] ]

            [ TCon (TC (TCNum n)) _, t ] ->
              [ VSeq n (finiteSeqMap Concrete (map ready xs))
              | xs <- sequence $ genericReplicate n
                               $ typeValues t ]
            _ -> []


        TCFun       -> []  -- We don't generate function values.
        TCTuple _   -> [ VTuple (map ready xs)
                       | xs <- sequence (map typeValues ts)
                       ]
        TCAbstract _ -> []
        TCNewtype _ -> []

    TCon _ _ -> []

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
