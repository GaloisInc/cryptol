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
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant pure" #-}

module Cryptol.TypeCheck.Solver.Numeric.Sampling.Sampling where

import Control.Monad
import Control.Monad.Except (ExceptT, MonadError (throwError))
import Control.Monad.State as State
import Cryptol.Testing.Random (Gen)
import Cryptol.TypeCheck.PP (pretty)
import Cryptol.TypeCheck.Solver.InfNat
import qualified Cryptol.TypeCheck.Solver.InfNat as Nat'
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Base
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Constraints as Cons
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Exp (Exp (..), Var (..))
import qualified Cryptol.TypeCheck.Solver.Numeric.Sampling.Exp as Exp
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Q
import Cryptol.TypeCheck.Solver.Numeric.Sampling.SolvedConstraints (SolvedConstraints)
import qualified Cryptol.TypeCheck.Solver.Numeric.Sampling.SolvedConstraints as SolCons
import Cryptol.TypeCheck.Solver.Numeric.Sampling.System as Sys
import Cryptol.TypeCheck.Type
import qualified Data.List as L
import Data.Maybe
import Data.Vector (Vector)
import qualified Data.Vector as V
import GHC.Real
import System.Random.TF.Gen (TFGen)
import System.Random.TF.Instances (Random (randomR))

data Range
  = -- upper-bounded by expressions
    UpperBounded [Exp Nat']
  | -- equal to an expression, and upper-bounded by expressions
    EqualAndUpperBounded (Exp Nat') [Exp Nat']
  | -- already sampled
    Fixed Nat'
  deriving (Show)

{-
Sample solved constraints
1. Collect upper bounds on each var
2. Sampling procedure:
  1. Sample each var in order, statefully keeping track of samplings so far
  2. To sample a var: If it's `Range` is `EqualAndUpperBounded` then the variable's value is
    equal to the sampling of the one expression, so sample that expression.

    -- TODO: talk about how EqualAndUpperBounded can be upperbounded too

    If it's `Range` is `UpperBounded` then sample each upper-bounding expression
    then sample a value (TODO: how to weight choice) between `0` and the minimum
    of the sampled upper-bounding values. Then update the variable's `Range` to
    be `EqualAndUpperBounded` of the value just sampled for it.
-}

-- TODO: make use of `fin` type constraint
sample :: SolvedConstraints Nat' -> SamplingM (Vector Integer)
sample solcons = do
  debug $ "breakpoint Numeric.Sampling.Sampling:1"
  let nVars = SolCons.countVars solcons
      vars = V.generate nVars Var

  debug $ "nVars = " ++ show nVars

  let solsys = SolCons.solsys solcons

  let initRanges = V.replicate nVars (UpperBounded [Exp.fromConstant nVars Inf])

  vals <- flip evalStateT initRanges do
    let getRange :: Var -> StateT (Vector Range) SamplingM Range
        getRange i = gets (V.! unVar i)

    let setEqual :: Var -> Exp Nat' -> StateT (Vector Range) SamplingM ()
        -- setEqual i e = (V.// [(unVar i, EqualAndUpperBounded e [])])
        setEqual i e =
          getRange i >>= \case
            UpperBounded bs -> modify (V.// [(unVar i, EqualAndUpperBounded e bs)])
            EqualAndUpperBounded _ _ -> throwError $ SamplingError "sample" "A variable was solved for more than once, which should never result from Gaussian elimination."
            Fixed _ -> throwError $ SamplingError "sample" "Attempted to `setEqual` a `Fixed` range variable"

    let addUpperBounds :: Var -> [Exp Nat'] -> StateT (Vector Range) SamplingM ()
        addUpperBounds i bs' =
          getRange i >>= \case
            UpperBounded bs -> modify (V.// [(unVar i, UpperBounded (bs <> bs'))])
            -- FIX: if x = y and x is bounded by 3, then this will ignore that
            -- bound, and so y can be assigned to 10 and then x will also be 10
            EqualAndUpperBounded e bs -> modify (V.// [(unVar i, EqualAndUpperBounded e (bs <> bs'))])
            -- can't upper-bound something that's already fixed...
            -- TODO: this shouldn't happen!
            -- TODO: should this be an error?
            Fixed _ -> pure ()

    let setFixed :: Var -> Nat' -> StateT (Vector Range) SamplingM ()
        setFixed i n' = modify (V.// [(unVar i, Fixed n')])

        divNat' :: Nat' -> Nat' -> Nat'
        Inf `divNat'` Inf = Nat 1
        Inf `divNat'` Nat n | n > 0 = Inf
        Inf `divNat'` Nat n | n < 0 = error "Attempted to divide Inf by a negative."
        Inf `divNat'` Nat n = error "Attempted to divide Inf by zero."
        Nat n `divNat'` Inf = Nat 0
        Nat n1 `divNat'` Nat n2 = Nat (n1 `div` n2)

    -- accumulate ranges
    V.mapM_
      ( \(i, mb_e) -> do
          -- debug $ "breakpoint Numeric.Sampling.Sampling:2"
          -- debug $ "i   = " ++ show i
          -- debug $ "mb_e = " ++ show mb_e
          case mb_e of
            Just e@(Exp as c) -> do
              -- We need to account for the upper bounds on `xi` when
              -- determining the upper bounds on the positive terms in `e`.
              bs <-
                getRange i >>= \case
                  UpperBounded bs -> pure bs
                  EqualAndUpperBounded _ _ -> throwError $ SamplingError "sample" "A variable has a `EqualAndUpperBounded` range before handling its equation during the upper-bounding pass."
                  Fixed _ -> throwError $ SamplingError "sample" "A variable has a `Fixed` range during the upper-bounding pass."
              --
              -- positive-coefficient and negative-coefficient variables
              let iPtvs = Var <$> V.findIndices (0 <) as
                  iNegs = Var <$> V.findIndices (0 >) as
              --
              -- Suppose we have
              --
              --   x = 2y + 3z + (-4)u + (-5)v <= 10
              --
              -- First, upper-bound all of the positive-coefficient variables
              -- like so:
              --
              --    y <= 10/2
              --    z <= (10 - 2y)/3
              --
              -- Second, upper-bound all of the negative-coefficient variables
              -- like so:
              --
              --    u <= (2y + 3z)/4
              --    v <= (2y + 3z - 4u)/5
              --
              -- upper-bound ptv-coeff vars
              --
              lift $ debug' 2 $ "as = " ++ show (V.toList as)
              foldM_
                ( \bs i' -> do
                    let ai' = e Exp.! i'
                    lift $ debug' 2 $ "i' = " ++ show i
                    lift $ debug' 2 $ "ai' = " ++ show ai'
                    lift $ debug' 2 $ "bs = " ++ show bs
                    lift $ debug' 2 $ "upper-bounding " ++ show i' ++ " by " ++ show (fmap (`divNat'` ai') <$> bs)
                    addUpperBounds i' (fmap (`divNat'` ai') <$> bs)
                    pure $ fmap (+ negate (Exp.extractTerm i' e)) bs
                )
                bs
                iPtvs
              -- upper-bound neg-coeff vars
              foldM_
                ( \e' i' -> do
                    let ai' = e Exp.! i'
                    lift $ debug' 2 $ "upper-bounding " ++ show i' ++ " by " ++ show ((`divNat'` ai') <$> e')
                    addUpperBounds i' [(`divNat'` ai') <$> e']
                    pure $ e' - Exp.single nVars ai' i'
                )
                e
                iNegs
              -- addd equality
              setEqual i e
            -- OLD
            {-
              rs <- pure $ setEqual i e rs
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
                  ( \i' (e', rs) ->
                      ( -- re-include negative term of var i'
                        e' Exp.// [(i', e Exp.! i')],
                        -- upper bound var i' by current e'
                        -- TODO: doesn't account for coeff of xi', need to divide by that
                        addUpperBound i' e' rs
                      )
                  )
                  (e', rs)
                  iNegs
            -- if variable is free, then just upper bounded by inf by
            -- default
            -}
            Nothing -> pure ()
      )
      (V.generate nVars Var `V.zip` solsys)

    do
      rs <- get
      lift $ debug' 1 $ "rs =\n" ++ unlines (("  " ++) . show <$> V.toList rs)
      throwError $ SamplingError "sample" "BREAK"

    -- sample all the vars
    let liftR :: (TFGen -> (a, TFGen)) -> StateT (Vector Range) SamplingM a
        liftR k = do
          (a, g) <- lift $ gets k
          lift $ put g
          pure a

    let sampleNat' :: Nat' -> StateT (Vector Range) SamplingM Nat'
        sampleNat' Inf = Nat <$> liftR (randomR (0, 10)) -- TODO: actually, sample exp dist up to MAX_INT
        sampleNat' (Nat n) = Nat <$> liftR (randomR (0, n))

        minimumUpperBound :: [Exp Nat'] -> StateT (Vector Range) SamplingM Nat'
        minimumUpperBound [] = pure Inf
        minimumUpperBound bs = minimum <$> (sampleExp Inf `traverse` bs)

        sampleVar :: Var -> StateT (Vector Range) SamplingM Nat'
        sampleVar i = do
          lift . debug' 1 $ "sampling var: " ++ show i
          range <- getRange i
          lift . debug' 1 $ "       range: " ++ show range
          -- sample from `Range`
          val <- case range of
            UpperBounded bs -> do
              -- upper bound
              n <- minimumUpperBound bs
              -- TODO: weight choices
              sampleNat' n
            EqualAndUpperBounded e bs -> do
              -- upper bound
              n <- minimumUpperBound bs
              -- TODO: weight choices
              sampleExp n e
            Fixed n -> pure n
          -- set xi := val
          setFixed i val
          lift . debug' 1 $ "               ==>" ++ show val
          --
          pure val

        -- sample an expression that is upper bounded by a constant
        sampleExp :: Nat' -> Exp Nat' -> StateT (Vector Range) SamplingM Nat'
        sampleExp n (Exp as c) = do
          lift . debug' 1 $ "sampling exp: " ++ show (Exp as c)
          -- only sampleuates terms that have non-0 coeff
          (c +)
            . V.sum
            <$> ( \(i, a) ->
                    if a /= 0
                      then sampleVar i
                      else pure 0
                )
            `traverse` (vars `V.zip` as)

    vals <- sampleVar `traverse` vars
    pure vals
  -- sample all the vars
  -- vals <- evalStateT (sampleVar `traverse` vars) rs
  debug $ "breakpoint Numeric.Sampling.Sampling:3"

  -- cast to Integer
  let fromNat' :: Nat' -> Integer
      fromNat' Inf = integer_max
      fromNat' (Nat n) = n
  debug $ "breakpoint Numeric.Sampling.Sampling:4"
  pure $ fromNat' <$> vals
