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
module Cryptol.Testing.Random where

import Cryptol.Eval.Monad     (ready,runEval,EvalOpts)
import Cryptol.Eval.Value     (BV(..),Value,GenValue(..),SeqMap(..), WordValue(..), BitWord(..))
import qualified Cryptol.Testing.Concrete as Conc
import Cryptol.TypeCheck.AST  (Type(..),TCon(..),TC(..),tNoUser)
import Cryptol.TypeCheck.SimpType(tRebuild')

import Cryptol.Utils.Ident    (Ident)
import Cryptol.Utils.Panic    (panic)
import Cryptol.Utils.PP       (pp)

import Control.Monad          (forM,join)
import Data.List              (unfoldr, genericTake, genericIndex)
import System.Random          (RandomGen, split, random, randomR)
import qualified Data.Sequence as Seq

type Gen g b w i = Integer -> g -> (GenValue b w i, g)


{- | Apply a testable value to some randomly-generated arguments.
     Returns `Nothing` if the function returned `True`, or
     `Just counterexample` if it returned `False`.

    Please note that this function assumes that the generators match
    the supplied value, otherwise we'll panic.
 -}
runOneTest :: RandomGen g
        => EvalOpts   -- ^ how to evaluate things
        -> Value   -- ^ Function under test
        -> [Gen g Bool BV Integer] -- ^ Argument generators
        -> Integer -- ^ Size
        -> g
        -> IO (Conc.TestResult, g)
runOneTest evOpts fun argGens sz g0 = do
  let (args, g1) = foldr mkArg ([], g0) argGens
      mkArg argGen (as, g) = let (a, g') = argGen sz g in (a:as, g')
  result <- Conc.runOneTest evOpts fun args
  return (result, g1)

returnOneTest :: RandomGen g
           => EvalOpts -- ^ How to evaluate things
           -> Value    -- ^ Function to be used to calculate tests
           -> [Gen g Bool BV Integer] -- ^ Argument generators
           -> Integer -- ^ Size
           -> g -- ^ Initial random state
           -> IO ([Value], Value, g) -- ^ Arguments, result, and new random state
returnOneTest evOpts fun argGens sz g0 =
  do let (args, g1) = foldr mkArg ([], g0) argGens
         mkArg argGen (as, g) = let (a, g') = argGen sz g in (a:as, g')
     result <- runEval evOpts (go fun args)
     return (args, result, g1)
   where
     go (VFun f) (v : vs) = join (go <$> (f (ready v)) <*> pure vs)
     go (VFun _) [] = panic "Not enough arguments to function while generating tests" []
     go v@(VBit _) [] = return v
     go v@(VSeq _ _) [] = return v
     go v@(VWord _ _) [] = return v
     go v@(VRecord _) [] = return v
     go v@(VTuple _) [] = return v
     go _ _ = panic "Cryptol.Testing.Random" ["Unsupported return value for testing"]


-- | Return a collection of random tests.
returnTests :: RandomGen g
         => g -- ^ The random generator state
         -> EvalOpts -- ^ How to evaluate things
         -> Type -- ^ The type of the function for which tests are to be generated
         -> Value -- ^ The function itself
         -> Int -- ^ How many tests?
         -> IO [([Value], Value)] -- ^ A list of pairs of random arguments and computed outputs
returnTests g evo ty fun num =
    case argGens ty of
      Nothing -> panic "Cryptol.Testing.Random" ["Can't generate test inputs for type", show (pp ty)]
      Just args ->
        do go args g 0
  where
    go args g0 n
      | n >= num = return []
      | otherwise =
        do let sz = toInteger (div (100 * (1 + n)) num)
           (inputs, output, g1) <- returnOneTest evo fun args sz g0
           more <- go args g1 (n + 1)
           return ((inputs, output) : more)

    argGens t =
      case tNoUser t of
        TCon (TC TCFun) [t1, t2] ->
          (:) <$> randomValue t1 <*> argGens t2
        _ -> pure []


{- | Given a (function) type, compute generators for
the function's arguments. Currently we do not support polymorphic functions.
In principle, we could apply these to random types, and test the results. -}
testableType :: RandomGen g => Type -> Maybe [Gen g Bool BV Integer]
testableType ty =
  case tNoUser ty of
    TCon (TC TCFun) [t1,t2] ->
      do g  <- randomValue t1
         as <- testableType t2
         return (g : as)
    TCon (TC TCBit) [] -> return []
    _ -> Nothing


{- | A generator for values of the given type.  This fails if we are
given a type that lacks a suitable random value generator. -}
randomValue :: (BitWord b w i, RandomGen g) => Type -> Maybe (Gen g b w i)
randomValue ty =
  case ty of
    TCon tc ts  ->
      case (tc, map (tRebuild' False) ts) of
        (TC TCBit, [])                        -> Just randomBit

        (TC TCInteger, [])                    -> Just randomInteger

        (TC TCIntMod, [TCon (TC (TCNum n)) []]) ->
          do return (randomIntMod n)

        (TC TCSeq, [TCon (TC TCInf) [], el])  ->
          do mk <- randomValue el
             return (randomStream mk)

        (TC TCSeq, [TCon (TC (TCNum n)) [], TCon (TC TCBit) []]) ->
            return (randomWord n)

        (TC TCSeq, [TCon (TC (TCNum n)) [], el]) ->
          do mk <- randomValue el
             return (randomSequence n mk)

        (TC (TCTuple _), els) ->
          do mks <- mapM randomValue els
             return (randomTuple mks)

        _ -> Nothing

    TVar _      -> Nothing
    TUser _ _ t -> randomValue t
    TRec fs     -> do gs <- forM fs $ \(l,t) -> do g <- randomValue t
                                                   return (l,g)
                      return (randomRecord gs)

-- | Generate a random bit value.
randomBit :: (BitWord b w i, RandomGen g) => Gen g b w i
randomBit _ g =
  let (b,g1) = random g
  in (VBit (bitLit b), g1)

randomSize :: RandomGen g => Int -> Int -> g -> (Int, g)
randomSize k n g
  | p == 1 = (n, g')
  | otherwise = randomSize k (n + 1) g'
  where (p, g') = randomR (1, k) g

-- | Generate a random integer value. The size parameter is assumed to
-- vary between 1 and 100, and we use it to generate smaller numbers
-- first.
randomInteger :: (BitWord b w i, RandomGen g) => Gen g b w i
randomInteger w g =
  let (n, g1) = if w < 100 then (fromInteger w, g) else randomSize 8 100 g
      (x, g2) = randomR (- 256^n, 256^n) g1
  in (VInteger (integerLit x), g2)

randomIntMod :: (BitWord b w i, RandomGen g) => Integer -> Gen g b w i
randomIntMod modulus _ g =
  let (x, g') = randomR (0, modulus-1) g
  in (VInteger (integerLit x), g')

-- | Generate a random word of the given length (i.e., a value of type @[w]@)
-- The size parameter is assumed to vary between 1 and 100, and we use
-- it to generate smaller numbers first.
randomWord :: (BitWord b w i, RandomGen g) => Integer -> Gen g b w i
randomWord w _sz g =
   let (val, g1) = randomR (0,2^w-1) g
   in (VWord w (ready (WordVal (wordLit w val))), g1)

-- | Generate a random infinite stream value.
randomStream :: RandomGen g => Gen g b w i -> Gen g b w i
randomStream mkElem sz g =
  let (g1,g2) = split g
  in (VStream $ IndexSeqMap $ genericIndex (map ready (unfoldr (Just . mkElem sz) g1)), g2)

{- | Generate a random sequence.  This should be used for sequences
other than bits.  For sequences of bits use "randomWord". -}
randomSequence :: RandomGen g => Integer -> Gen g b w i -> Gen g b w i
randomSequence w mkElem sz g0 = do
  let (g1,g2) = split g0
  let f g = let (x,g') = mkElem sz g
             in seq x (Just (ready x, g'))
  let xs = Seq.fromList $ genericTake w $ unfoldr f g1
  seq xs (VSeq w $ IndexSeqMap $ (Seq.index xs . fromInteger), g2)

-- | Generate a random tuple value.
randomTuple :: RandomGen g => [Gen g b w i] -> Gen g b w i
randomTuple gens sz = go [] gens
  where
  go els [] g = (VTuple (reverse els), g)
  go els (mkElem : more) g =
    let (v, g1) = mkElem sz g
    in seq v (go (ready v : els) more g1)

-- | Generate a random record value.
randomRecord :: RandomGen g => [(Ident, Gen g b w i)] -> Gen g b w i
randomRecord gens sz = go [] gens
  where
  go els [] g = (VRecord (reverse els), g)
  go els ((l,mkElem) : more) g =
    let (v, g1) = mkElem sz g
    in seq v (go ((l,ready v) : els) more g1)


