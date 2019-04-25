-- |
-- Module      :  Cryptol.Testing.Concrete
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE RecordWildCards #-}
module Cryptol.Testing.Concrete where

import Control.Monad (join, liftM2)

import Cryptol.Eval.Monad
import Cryptol.Eval.Value
import Cryptol.TypeCheck.AST
import Cryptol.Utils.Panic (panic)

import qualified Control.Exception as X
import Data.List(genericReplicate)

import Prelude ()
import Prelude.Compat

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
runOneTest :: EvalOpts -> Value -> [Value] -> IO TestResult
runOneTest evOpts v0 vs0 = run `X.catch` handle
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
    go v vs              = do vdoc    <- ppValue defaultPPOpts v
                              vsdocs  <- mapM (ppValue defaultPPOpts) vs
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
    TRec fs     -> [ VRecord xs
                   | xs <- sequence [ [ (f,ready v) | v <- typeValues t ]
                                    | (f,t) <- fs ]
                   ]
    TCon (TC tc) ts ->
      case tc of
        TCNum _     -> []
        TCInf       -> []
        TCBit       -> [ VBit False, VBit True ]
        TCInteger   -> []
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
              [ VSeq n (finiteSeqMap (map ready xs))
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
