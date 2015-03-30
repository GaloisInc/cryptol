{-# LANGUAGE TupleSections #-}
-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Evaluate test cases and handle exceptions appropriately

module Cryptol.Testing.Eval where

import Cryptol.Eval.Error
import Cryptol.Eval.Value
import Cryptol.Utils.Panic (panic)

import qualified Control.Exception as X

-- | A test result is either a pass, a failure due to evaluating to
-- @False@, or a failure due to an exception raised during evaluation
data TestResult
  = Pass
  | FailFalse [Value]
  | FailError EvalError [Value]

-- | Apply a testable value to some arguments.
-- Note that this function assumes that the values come from a call to
-- `testableType` (i.e., things are type-correct). We run in the IO
-- monad in order to catch any @EvalError@s.
runOneTest :: Value -> [Value] -> IO TestResult
runOneTest v0 vs0 = run `X.catch` handle
  where
    run = do
      result <- X.evaluate (go v0 vs0)
      if result
        then return Pass
        else return (FailFalse vs0)
    handle e = return (FailError e vs0)

    go :: Value -> [Value] -> Bool
    go (VFun f) (v : vs) = go (f v) vs
    go (VFun _) []       = panic "Not enough arguments while applying function"
                           []
    go (VBit b) []       = b
    go v vs              = panic "Type error while running test" $
                           [ "Function:"
                           , show $ ppValue defaultPPOpts v
                           , "Arguments:"
                           ] ++ map (show . ppValue defaultPPOpts) vs
