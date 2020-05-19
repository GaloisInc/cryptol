{-# Language BlockArguments #-}
{-# Language OverloadedStrings #-}
module Cryptol.Eval.What4.FloatPrims (floatPrims) where

import Data.Map(Map)
import qualified Data.Map as Map
import What4.Interface(IsExprBuilder)
import Control.Monad.IO.Class

import Cryptol.TypeCheck.Solver.InfNat(Nat'(..))
import Cryptol.Eval.Value hiding (SFloat)
import Cryptol.Eval.What4.Value
import Cryptol.Eval.What4.SFloat
import Cryptol.Utils.Ident(Ident, floatPrimIdent)

floatPrims :: IsExprBuilder sym => What4 sym -> Map Ident (Value sym)
floatPrims (What4 sym) = Map.fromList [ (floatPrimIdent i,v) | (i,v) <- table ]
  where
  (~>) = (,)

  table =
    [ "fpNaN" ~> fpConst (fpNaN sym)
    ]



fpConst ::
  IsExprBuilder sym =>
  (Integer -> Integer -> IO (SFloat sym)) ->
  Value sym
fpConst mk =
     nlam \ ~(Nat e) ->
 VNumPoly \ ~(Nat p) ->
 VFloat <$> liftIO (mk e p)


