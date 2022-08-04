{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Cryptol.TypeCheck.Solver.Numeric.Sampling.Sampling where

import Control.Monad
import Control.Monad.State as State
import Cryptol.Testing.Random (Gen)
import Cryptol.TypeCheck.Solver.InfNat
import qualified Cryptol.TypeCheck.Solver.InfNat as Nat'
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Base
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Constraints as Cons
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Exp
import qualified Cryptol.TypeCheck.Solver.Numeric.Sampling.Exp as Exp
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Q
import Cryptol.TypeCheck.Solver.Numeric.Sampling.System as Sys
import Cryptol.TypeCheck.Type
import qualified Data.List as L
import Data.Maybe
import Data.Vector (Vector)
import qualified Data.Vector as V
import GHC.Real
import System.Random.TF.Gen (TFGen)
import System.Random.TF.Instances (Random (randomR))
import Cryptol.TypeCheck.Solver.Numeric.Sampling.SolvedConstraints (SolvedConstraints)
import qualified Cryptol.TypeCheck.Solver.Numeric.Sampling.SolvedConstraints as SolCons

data Range = UpperBounds [Exp Nat'] | Single (Exp Nat')

{-
Sample solved constraints
1. Collect upper bounds on each var
2. Sampling procedure:
  1. Sample each var in order, statefully keeping track of samplings so far
  2. To sample a var: If it's `Range` is `Single` then the variable's value is
    equal to the sampling of the one expression, so sample that expression. If
    it's `Range` is `UpperBounds` then sample each upper-bounding expression
    then sample a value (TODO: how to weight choice) between `0` and the minimum
    of the sampled upper-bounding values. Then update the variable's `Range` to
    be `Single` of the value just sampled for it.
-}

-- TODO: make use of `fin` type constraint
sample :: SolvedConstraints Nat' -> SamplingM (Vector Integer)
sample solcons = do
  debug $ "breakpoint Numeric.Sampling.Sampling:1"
  let nVars = SolCons.countVars solcons
      vars = V.generate nVars Var

  debug $ "nVars = " ++ show nVars

  let solsys = SolCons.solsys solcons

  -- collect the range of each var
  rngs <- do
    let getRange :: Var -> Vector Range -> Range
        getRange i rngs = rngs V.! unVar i

        setSingle :: Var -> Exp Nat' -> Vector Range -> Vector Range
        setSingle i e = (V.// [(unVar i, Single e)])

        addUpperBound :: Var -> Exp Nat' -> Vector Range -> Vector Range
        addUpperBound i e rngs = case getRange i rngs of
          UpperBounds bnds -> rngs V.// [(unVar i, UpperBounds (e : bnds))]
          Single _ -> rngs -- upper bounding an equality is a nullop
    V.foldM
      ( \rngs (i, mb_e) -> do
          debug $ "breakpoint Numeric.Sampling.Sampling:2"
          debug $ "i   = " ++ show i
          debug $ "mb_e = " ++ show mb_e
          case mb_e of
            -- register equ for `xi = e` if there are subtractions in `e`,
            -- then register those upper bounds
            Just e@(Exp as c) -> do
              rngs <- pure $ setSingle i e rngs
              let iNegs = Var <$> V.findIndices (< 0) as -- vars in neg terms
              -- e' starts off with only pos non-0 terms, then bounds each
              -- neg term iteratively by subtracting from e' e.g. an example
              -- sequence of iterations:
              --    e  = x + y - z - w
              --    e' := x + y
              --    z <= e' = x + y
              --    e' <- x + y - z
              --    w <= e' = x + y - z
              let e' = (\a -> if a > 0 then a else 0) <$> e
              pure . snd $
                foldr
                  ( \i' (e', rngs) ->
                      ( -- re-include negative term of var i'
                        e' Exp.// [(i', e Exp.! i')],
                        -- upper bound var i' by current e'
                        addUpperBound i' e' rngs
                      )
                  )
                  (e', rngs)
                  iNegs
            -- if variable is free, then just upper bounded by inf by
            -- default
            Nothing -> pure rngs
      )
      (V.replicate nVars (UpperBounds [Exp.fromConstant nVars Inf]))
      (V.generate nVars Var `V.zip` solsys)

  -- sample all the vars
  do
    let liftR :: (TFGen -> (a, TFGen)) -> SamplingM a
        liftR = undefined
      
        getRange :: Var -> StateT (Vector Range) SamplingM Range
        getRange i = gets (V.! unVar i)

        sampleNat' :: Nat' -> SamplingM Nat'
        sampleNat' Inf = Nat <$> liftR (randomR (0, 10)) -- TODO: actually, sample exp dist up to MAX_INT
        sampleNat' (Nat n) = Nat <$> liftR (randomR (0, n))

        sampleVar :: Var -> StateT (Vector Range) SamplingM Nat'
        sampleVar i = do
          range <- getRange i
          -- sample from `Range`
          val <- case range of
            UpperBounds es -> do
              -- upper bound
              n <- minimum <$> sampleExp `traverse` es
              lift $ sampleNat' n -- TODO: weight choices
            Single e -> sampleExp e
          -- update `Range` to be `xi = val`
          modify (V.// [(unVar i, Single $ fromConstant nVars val)])
          --
          pure val

        sampleExp :: Exp Nat' -> StateT (Vector Range) SamplingM Nat'
        sampleExp (Exp as c) =
          -- only sampleuates terms that have non-0 coeff
          (c +) . V.sum
            <$> ( \(i, a) ->
                    if a /= 0
                      then sampleVar i
                      else pure 0
                )
            `traverse` (vars `V.zip` as)

    -- sample all the vars
    vals <- evalStateT (sampleVar `traverse` vars) rngs
    debug $ "breakpoint Numeric.Sampling.Sampling:3"
    

    -- cast to Integer
    let fromNat' :: Nat' -> Integer
        fromNat' Inf = integer_max
        fromNat' (Nat n) = n
    debug $ "breakpoint Numeric.Sampling.Sampling:4"
    pure $ fromNat' <$> vals