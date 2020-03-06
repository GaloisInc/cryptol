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
{-# LANGUAGE ScopedTypeVariables #-}
module Cryptol.Testing.Random where

import Cryptol.Eval.Monad     (ready,runEval,EvalOpts,io)
import Cryptol.Eval.Value     (Value,GenValue(..),SeqMap(..), WordValue(..), BitWord(..))
import qualified Cryptol.Testing.Concrete as Conc
import Cryptol.TypeCheck.AST  (Type(..), TCon(..), TC(..), tNoUser, tIsFun)
import Cryptol.TypeCheck.SimpType(tRebuild')

import Cryptol.Utils.Ident    (Ident)
import Cryptol.Utils.Panic    (panic)

import Control.Monad          (join)
import Data.List              (unfoldr, genericTake, genericIndex)
import System.Random          (RandomGen, split, random, randomR)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Sequence as Seq

type Gen g x = Integer -> g -> (IO (GenValue x), g)


{- | Apply a testable value to some randomly-generated arguments.
     Returns @Nothing@ if the function returned @True@, or
     @Just counterexample@ if it returned @False@.

    Please note that this function assumes that the generators match
    the supplied value, otherwise we'll panic.
 -}
runOneTest :: RandomGen g
        => EvalOpts   -- ^ how to evaluate things
        -> Value   -- ^ Function under test
        -> [Gen g ()] -- ^ Argument generators
        -> Integer -- ^ Size
        -> g
        -> IO (Conc.TestResult, g)
runOneTest evOpts fun argGens sz g0 = do
  let (args, g1) = foldr mkArg ([], g0) argGens
      mkArg argGen (as, g) = let (a, g') = argGen sz g in (a:as, g')
  args' <- sequence args
  result <- Conc.runOneTest evOpts fun args'
  return (result, g1)

returnOneTest :: RandomGen g
           => EvalOpts -- ^ How to evaluate things
           -> Value    -- ^ Function to be used to calculate tests
           -> [Gen g ()] -- ^ Argument generators
           -> Integer -- ^ Size
           -> g -- ^ Initial random state
           -> IO ([Value], Value, g) -- ^ Arguments, result, and new random state
returnOneTest evOpts fun argGens sz g0 =
  do let (args, g1) = foldr mkArg ([], g0) argGens
         mkArg argGen (as, g) = let (a, g') = argGen sz g in (a:as, g')
     args' <- sequence args
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
         -> [Gen g ()] -- ^ Generators for the function arguments
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
arguments. This is like 'testableType', but allows the result to be
any finite type instead of just @Bit@. -}
dumpableType :: forall g. RandomGen g => Type -> Maybe [Gen g ()]
dumpableType ty =
  case tIsFun ty of
    Just (t1, t2) ->
      do g  <- randomValue () t1
         as <- testableType t2
         return (g : as)
    Nothing ->
      do (_ :: Gen g ()) <- randomValue () ty
         return []

{- | Given a (function) type, compute generators for
the function's arguments. Currently we do not support polymorphic functions.
In principle, we could apply these to random types, and test the results. -}
testableType :: RandomGen g => Type -> Maybe [Gen g ()]
testableType ty =
  case tNoUser ty of
    TCon (TC TCFun) [t1,t2] ->
      do g  <- randomValue () t1
         as <- testableType t2
         return (g : as)
    TCon (TC TCBit) [] -> return []
    _ -> Nothing


{- | A generator for values of the given type.  This fails if we are
given a type that lacks a suitable random value generator. -}
randomValue :: (BitWord sym, RandomGen g) => sym -> Type -> Maybe (Gen g sym)
randomValue sym ty =
  case ty of
    TCon tc ts  ->
      case (tc, map (tRebuild' False) ts) of
        (TC TCBit, [])                        -> Just (randomBit sym)

        (TC TCInteger, [])                    -> Just (randomInteger sym)

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

-- | Generate a random bit value.
randomBit :: (BitWord sym, RandomGen g) => sym -> Gen g sym
randomBit sym _ g =
  let (b,g1) = random g
  in (VBit <$> bitLit sym b, g1)

randomSize :: RandomGen g => Int -> Int -> g -> (Int, g)
randomSize k n g
  | p == 1 = (n, g')
  | otherwise = randomSize k (n + 1) g'
  where (p, g') = randomR (1, k) g

-- | Generate a random integer value. The size parameter is assumed to
-- vary between 1 and 100, and we use it to generate smaller numbers
-- first.
randomInteger :: (BitWord sym, RandomGen g) => sym -> Gen g sym
randomInteger sym w g =
  let (n, g1) = if w < 100 then (fromInteger w, g) else randomSize 8 100 g
      (i, g2) = randomR (- 256^n, 256^n) g1
  in (VInteger <$> integerLit sym i, g2)

randomIntMod :: (BitWord sym, RandomGen g) => sym -> Integer -> Gen g sym
randomIntMod sym modulus _ g =
  let (i, g') = randomR (0, modulus-1) g
  in (VInteger <$> integerLit sym i, g')

-- | Generate a random word of the given length (i.e., a value of type @[w]@)
-- The size parameter is assumed to vary between 1 and 100, and we use
-- it to generate smaller numbers first.
randomWord :: (BitWord sym, RandomGen g) => sym -> Integer -> Gen g sym
randomWord sym w _sz g =
   let (val, g1) = randomR (0,2^w-1) g
   in (return $ VWord w (WordVal <$> io (wordLit sym w val)), g1)

-- | Generate a random infinite stream value.
randomStream :: RandomGen g => Gen g sym -> Gen g sym
randomStream mkElem sz g =
  let (g1,g2) = split g
  in (pure $ VStream $ IndexSeqMap $ genericIndex (map io (unfoldr (Just . mkElem sz) g1)), g2)

{- | Generate a random sequence.  This should be used for sequences
other than bits.  For sequences of bits use "randomWord". -}
randomSequence :: RandomGen g => Integer -> Gen g sym -> Gen g sym
randomSequence w mkElem sz g0 = do
  let (g1,g2) = split g0
  let f g = let (x,g') = mkElem sz g
             in seq x (Just (io x, g'))
  let xs = Seq.fromList $ genericTake w $ unfoldr f g1
  seq xs (pure $ VSeq w $ IndexSeqMap $ (Seq.index xs . fromInteger), g2)

-- | Generate a random tuple value.
randomTuple :: RandomGen g => [Gen g sym] -> Gen g sym
randomTuple gens sz = go [] gens
  where
  go els [] g = (pure $ VTuple (reverse els), g)
  go els (mkElem : more) g =
    let (v, g1) = mkElem sz g
    in seq v (go (io v : els) more g1)

-- | Generate a random record value.
randomRecord :: RandomGen g => Map Ident (Gen g sym) -> Gen g sym
randomRecord gens sz g0 =
  let (g', m) = Map.mapAccum mk g0 gens in (pure $ VRecord m, g')
  where
    mk g gen =
      let (v, g') = gen sz g
      in seq v (g', io v)
