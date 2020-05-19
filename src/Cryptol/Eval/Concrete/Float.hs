{-# Language BlockArguments #-}
{-# Language OverloadedStrings #-}
-- | Concrete evaluations for floating point primitives.
module Cryptol.Eval.Concrete.Float where

import Data.Map(Map)
import qualified Data.Map as Map
import LibBF

import Cryptol.Utils.Ident(Ident, floatPrimIdent)
import Cryptol.Utils.Panic(panic)
import Cryptol.TypeCheck.Solver.InfNat(Nat'(..))
import Cryptol.Eval.Value
import Cryptol.Eval.Concrete.FloatHelpers
import Cryptol.Eval.Concrete.Value

floatPrims :: Concrete -> Map Ident Value
floatPrims sym = Map.fromList [ (floatPrimIdent i,v) | (i,v) <- table ]
  where
  (~>) = (,)
  table =
    [ "fpNaN"     ~> nlam \_ -> nlam \_ -> VFloat bfNaN
    , "fpPosInf"  ~> nlam \_ -> nlam \_ -> VFloat bfPosInf
    , "fpNeg"     ~> nlam \_ -> nlam \_ -> flam \x -> pure $ VFloat $ bfNeg x

    , "fpAdd"     ~> binArith sym bfAdd
    , "fpSub"     ~> binArith sym bfSub
    , "fpMul"     ~> binArith sym bfMul
    , "fpDiv"     ~> binArith sym bfDiv
    ]

ilam :: (Integer -> Value) -> Value
ilam f = nlam \n ->
  case n of
    Nat i -> f i
    Inf   -> panic "ilam" [ "Unexpected `inf`" ]

binArith ::
  Concrete ->
  (BFOpts -> BigFloat -> BigFloat -> (BigFloat, Status)) ->
  Value
binArith sym fun =
  ilam \e ->
  ilam \p ->
  wlam sym \r ->
  pure $ flam \x ->
  pure $ flam \y ->
  do opts <- floatOpts sym e p (bvVal r)
     VFloat <$> checkStatus sym (fun opts x y)




