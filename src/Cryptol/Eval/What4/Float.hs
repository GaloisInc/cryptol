{-# Language BlockArguments #-}
{-# Language OverloadedStrings #-}
-- | Floating point primitives for the What4 backend.
module Cryptol.Eval.What4.Float (floatPrims) where

import Data.Map(Map)
import qualified Data.Map as Map
import qualified What4.Interface as W4
import Control.Monad.IO.Class

import Cryptol.TypeCheck.Solver.InfNat(Nat'(..))
import Cryptol.Eval.Value
import Cryptol.Eval.Generic
import Cryptol.Eval.What4.Value
import qualified Cryptol.Eval.What4.SFloat as W4
import Cryptol.Utils.Ident(PrimIdent, floatPrim)

-- | Table of floating point primitives
floatPrims :: W4.IsExprBuilder sym => What4 sym -> Map PrimIdent (Value sym)
floatPrims sym4@(What4 sym) =
  Map.fromList [ (floatPrim i,v) | (i,v) <- nonInfixTable ]
  where
  (~>) = (,)

  nonInfixTable =
    [ "fpNaN"       ~> fpConst (W4.fpNaN sym)
    , "fpPosInf"    ~> fpConst (W4.fpPosInf sym)
    , "fpFromBits"  ~> ilam \e -> ilam \p -> wlam sym4 \w ->
                       VFloat <$> liftIO (W4.fpFromBinary sym e p w)
    , "fpNeg"       ~> ilam \_ -> ilam \_ -> flam \x ->
                       VFloat <$> liftIO (W4.fpNeg sym x)
    , "fpAdd"       ~> fpBinArithV sym4 fpPlus
    , "fpSub"       ~> fpBinArithV sym4 fpMinus
    , "fpMul"       ~> fpBinArithV sym4 fpMult
    , "fpDiv"       ~> fpBinArithV sym4 fpDiv
    ]



-- | A helper for definitng floating point constants.
fpConst ::
  W4.IsExprBuilder sym =>
  (Integer -> Integer -> IO (W4.SFloat sym)) ->
  Value sym
fpConst mk =
     ilam \ e ->
 VNumPoly \ ~(Nat p) ->
 VFloat <$> liftIO (mk e p)


