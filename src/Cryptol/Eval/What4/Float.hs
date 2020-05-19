{-# Language BlockArguments #-}
{-# Language OverloadedStrings #-}
-- | Floating point primitives for the What4 backend.
module Cryptol.Eval.What4.Float (floatPrims) where

import Data.Map(Map)
import qualified Data.Map as Map
import What4.Interface(IsExprBuilder)
import Control.Monad.IO.Class

import Cryptol.TypeCheck.Solver.InfNat(Nat'(..))
import Cryptol.Eval.Value hiding (SFloat)
import Cryptol.Eval.What4.Value
import Cryptol.Eval.What4.SFloat
import Cryptol.Utils.Ident(Ident, floatPrimIdent)

-- | Table of floating point primitives
floatPrims :: IsExprBuilder sym => What4 sym -> Map Ident (Value sym)
floatPrims (What4 sym) = Map.fromList [ (floatPrimIdent i,v) | (i,v) <- table ]
  where
  (~>) = (,)

  table =
    [ "fpNaN"     ~> fpConst (fpNaN sym)
    , "fpPosInf"  ~> fpConst (fpPosInf sym)
    ]


-- | A helper for definitng floating point constants.
fpConst ::
  IsExprBuilder sym =>
  (Integer -> Integer -> IO (SFloat sym)) ->
  Value sym
fpConst mk =
     nlam \ ~(Nat e) ->
 VNumPoly \ ~(Nat p) ->
 VFloat <$> liftIO (mk e p)


