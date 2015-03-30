-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

module Cryptol.Testing.Exhaust where

import qualified Cryptol.Testing.Eval as Eval
import Cryptol.TypeCheck.AST
import Cryptol.Eval.Value

import Data.List(genericReplicate)

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative((<$>))
#endif

{- | Given a (function) type, compute all possible inputs for it.
We also return the total number of test (i.e., the length of the outer list. -}
testableType :: Type -> Maybe (Integer, [[Value]])
testableType ty =
  case tNoUser ty of
    TCon (TC TCFun) [t1,t2] ->
      do sz        <- typeSize t1
         (tot,vss) <- testableType t2
         return (sz * tot, [ v : vs | v <- typeValues t1, vs <- vss ])
    TCon (TC TCBit) [] -> return (1, [[]])
    _ -> Nothing

{- | Apply a testable value to some arguments.
    Please note that this function assumes that the values come from
    a call to `testableType` (i.e., things are type-correct)
 -}
runOneTest :: Value -> [Value] -> IO Eval.TestResult
runOneTest = Eval.runOneTest

{- | Given a fully-evaluated type, try to compute the number of values in it.
Returns `Nothing` for infinite types, user-defined types, polymorhic types,
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
        (TCSeq, [sz,el]) -> case tNoUser sz of
                              TCon (TC (TCNum n)) _ -> (^ n) <$> typeSize el
                              _                     -> Nothing
        (TCSeq, _)       -> Nothing
        (TCFun, _)       -> Nothing
        (TCTuple _, els) -> product <$> mapM typeSize els
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
                   | xs <- sequence [ [ (f,v) | v <- typeValues t ]
                                    | (f,t) <- fs ]
                   ]
    TCon (TC tc) ts ->
      case (tc, ts) of
        (TCNum _, _)     -> []
        (TCInf, _)       -> []
        (TCBit, _)       -> [ VBit False, VBit True ]
        (TCSeq, ts1)     ->
            case map tNoUser ts1 of
              [ TCon (TC (TCNum n)) _, TCon (TC TCBit) [] ] ->
                  [ VWord (BV n x) | x <- [ 0 .. 2^n - 1 ] ]

              [ TCon (TC (TCNum n)) _, t ] ->
                  [ VSeq False xs | xs <- sequence $ genericReplicate n
                                                   $ typeValues t ]
              _ -> []


        (TCFun, _)       -> []  -- We don't generate function values.
        (TCTuple _, els) -> [ VTuple xs | xs <- sequence (map typeValues els)]
        (TCNewtype _, _) -> []

    TCon _ _ -> []


