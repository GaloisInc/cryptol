{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MultiWayIf #-}

-- infers instances such as KnownNat n => KnownNat (n + n)
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE LambdaCase #-}

module Cryptol.TypeCheck.Solver.Numeric.Sampling.Sampling where

import Control.Monad
import GHC.Real
import Data.Maybe
import qualified Data.List as L
import Data.Proxy
import GHC.TypeNats
import qualified Data.Vector.Sized as V
import Data.Finite
import System.Random.TF.Gen (RandomGen)
import Cryptol.Testing.Random (Gen)
import Cryptol.TypeCheck.Type
import Cryptol.TypeCheck.Solver.InfNat
import Control.Monad.State as State
import Data.Vector.Sized as V

import qualified Cryptol.TypeCheck.Solver.Numeric.Sampling.Exp as Exp
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Exp
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Base
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Q
import qualified Cryptol.TypeCheck.Solver.InfNat as Nat'
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Constraints

{-
Sample constraints
1. Collect upper bounds on each var
2. Sampling procedure:
  1. Evaluate each var in order, statefully keeping track of evaluations so far
  2. To evaluate a var:
    - if it's already been evaluated, use that value
    - if it's not been evaluated and it's assigned to an expression 
-}
sample :: forall g. RandomGen g => SomeConstraints Nat' -> Gen g (TParam, Type)
sample someCon = case someCon of
  SomeConstraints con -> sample' con


sample' :: forall g n. (RandomGen g, KnownNat n) => Constraints n Nat' -> Gen g (TParam, Type)
sample' = undefined
  where
    collectRanges :: Constraints n Nat' -> Vector n (Range n)
    collectRanges = undefined

    getRange :: Finite n -> StateT (Vector n (Range n)) (GenM g) (Range n)
    getRange i = gets (`V.index` i)

    evalVar :: Finite n -> StateT (Vector n (Range n)) (GenM g) Nat'
    evalVar i = do
      range <- getRange i
      v <- case range of
        Range es -> Prelude.minimum <$> evalExp `traverse` es
        Fixed e -> evalExp e
      modify (V.// [(i, Fixed $ fromConstant v)])
      pure v

    evalExp :: Exp n Nat' -> StateT (Vector n (Range n)) (GenM g) Nat'
    evalExp (Exp as c) = do
      -- 1. Evaluate all the vars with positive nonzero coefficients
      -- 2. Evaluate all the vars with negative nonzero coefficients, in an 
      --    order while updating their range each time and weighting by number 
      --    of possibilities after choice is made.

      as <- V.foldM
        -- `e` starts off as the sum of positive terms, then progressively gets 
        --    subtracted from by each negative valeu that is sampled
        -- `as` is the new vector being built up
        (\(e, as) (i, a) ->
          if | a >  0 -> pure undefined
             | a <  0 -> pure undefined
             | otherwise {- a == 0 -} -> pure (e, as) 
        )
        (undefined :: Exp n Nat', V.replicate _)
        (generate id `V.zip` as)
        :: StateT (Vector n (Range n)) (GenM g) (Exp n Nat', Vector n a)


      -- -- FIX: this naive approach doesn't work with negative values
      -- -- vars with nonzero coefficients need to be evaluated
      -- (c +) <$> 
      --   V.foldM
      --     (\v (i, a) -> (v +) . (a *) <$> 
      --       if a == 0 
      --         then pure 0 -- vars with zero coefficients neen not be evaluated yet
      --         else evalVar i)
      --     0
      --     (generate id `V.zip` as)
      
      undefined
      

data Range n = Range [Exp n Nat'] | Fixed (Exp n Nat')