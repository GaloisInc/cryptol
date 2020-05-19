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
floatPrims :: W4.IsSymExprBuilder sym => What4 sym -> Map PrimIdent (Value sym)
floatPrims sym@(What4 w4sym _) =
  Map.fromList [ (floatPrim i,v) | (i,v) <- nonInfixTable ]
  where
  (~>) = (,)

  nonInfixTable =
    [ "fpNaN"       ~> fpConst (W4.fpNaN w4sym)
    , "fpPosInf"    ~> fpConst (W4.fpPosInf w4sym)
    , "fpFromBits"  ~> ilam \e -> ilam \p -> wlam sym \w ->
                       VFloat <$> liftIO (W4.fpFromBinary w4sym e p w)
    , "fpToBits"    ~> ilam \e -> ilam \p -> flam \x ->
                       pure $ VWord (e+p)
                            $ WordVal <$> liftIO (W4.fpToBinary w4sym x)
    , "=.="         ~> ilam \_ -> ilam \_ -> flam \x -> pure $ flam \y ->
                       VBit <$> liftIO (W4.fpEq w4sym x y)
    , "fpIsFinite"  ~> ilam \_ -> ilam \_ -> flam \x ->
                       VBit <$> liftIO do inf <- W4.fpIsInf w4sym x
                                          nan <- W4.fpIsNaN w4sym x
                                          weird <- W4.orPred w4sym inf nan
                                          W4.notPred w4sym weird

    , "fpAdd"       ~> fpBinArithV sym fpPlus
    , "fpSub"       ~> fpBinArithV sym fpMinus
    , "fpMul"       ~> fpBinArithV sym fpMult
    , "fpDiv"       ~> fpBinArithV sym fpDiv

    , "fpFromRational" ~>
       ilam \e -> ilam \p -> wlam sym \r -> pure $ lam \x ->
       do rat <- fromVRational <$> x
          VFloat <$> fpCvtFromRational sym e p r rat

    , "fpToRational" ~>
       ilam \_e -> ilam \_p -> flam \fp ->
       VRational <$> fpCvtToRational sym fp
    ]



-- | A helper for definitng floating point constants.
fpConst ::
  W4.IsSymExprBuilder sym =>
  (Integer -> Integer -> IO (W4.SFloat sym)) ->
  Value sym
fpConst mk =
     ilam \ e ->
 VNumPoly \ ~(Nat p) ->
 VFloat <$> liftIO (mk e p)


