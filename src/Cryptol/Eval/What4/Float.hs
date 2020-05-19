{-# Language BlockArguments #-}
{-# Language OverloadedStrings #-}
-- | Floating point primitives for the What4 backend.
module Cryptol.Eval.What4.Float (floatPrims) where

import Data.Map(Map)
import qualified Data.Map as Map
import qualified What4.Interface as W4
import Control.Monad.IO.Class
import Control.Exception(throwIO)

import Cryptol.TypeCheck.Solver.InfNat(Nat'(..))
import Cryptol.Eval.Monad(EvalError(..))
import Cryptol.Eval.Value hiding (SFloat)
import Cryptol.Eval.What4.Value
import Cryptol.Eval.What4.SFloat
import Cryptol.Utils.Ident(Ident, floatPrimIdent)

-- | Table of floating point primitives
floatPrims :: W4.IsExprBuilder sym => What4 sym -> Map Ident (Value sym)
floatPrims sym4@(What4 sym) =
  Map.fromList [ (floatPrimIdent i,v) | (i,v) <- table ]
  where
  (~>) = (,)

  table =
    [ "fpNaN"     ~> fpConst (fpNaN sym)
    , "fpPosInf"  ~> fpConst (fpPosInf sym)
    , "fpNeg"     ~> nlam \_ -> nlam \_ -> flam \x ->
                     VFloat <$> liftIO (fpNeg sym x)
    , "fpAdd"     ~> fpArtih2 sym4 fpAdd
    , "fpSub"     ~> fpArtih2 sym4 fpSub
    , "fpMul"     ~> fpArtih2 sym4 fpMul
    , "fpDiv"     ~> fpArtih2 sym4 fpDiv
    ]



-- | A helper for definitng floating point constants.
fpConst ::
  W4.IsExprBuilder sym =>
  (Integer -> Integer -> IO (SFloat sym)) ->
  Value sym
fpConst mk =
     nlam \ ~(Nat e) ->
 VNumPoly \ ~(Nat p) ->
 VFloat <$> liftIO (mk e p)

-- | A function that takes a rounding mode as a parameter
rm_lam ::
  W4.IsExprBuilder sym =>
  What4 sym ->
  (W4.RoundingMode -> W4Eval sym (Value sym)) ->
  Value sym
rm_lam sym f = wlam sym \v ->
  case wordAsLit sym v of
    Just (_w,i) ->
      case i of
        0 -> f W4.RNE
        1 -> f W4.RNA
        2 -> f W4.RTP
        3 -> f W4.RTN
        4 -> f W4.RTZ
        x -> raiseError sym (BadRoundingMode x)
    _ -> liftIO $ throwIO $ UnsupportedSymbolicOp "rounding mode."


-- | Binary arithmetic with a rounding mode.
fpArtih2 ::
  W4.IsExprBuilder sym =>
  What4 sym ->
  (SFloatBinArith sym) ->
  Value sym
fpArtih2 sym4@(What4 sym) fun =
  nlam \_ -> nlam \_ -> rm_lam sym4 \r ->
  pure $ flam \x ->
  pure $ flam \y -> VFloat <$> liftIO (fun sym r x y)



