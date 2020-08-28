{-# Language BlockArguments #-}
{-# Language OverloadedStrings #-}
-- | Floating point primitives for the What4 backend.
module Cryptol.Eval.What4.Float (floatPrims) where

import Data.Map(Map)
import qualified Data.Map as Map
import qualified What4.Interface as W4
import Control.Monad.IO.Class

import Cryptol.TypeCheck.Solver.InfNat(Nat'(..))
import Cryptol.Eval.Type (TValue(..))
import Cryptol.Eval.Value
import Cryptol.Eval.Generic
import Cryptol.Eval.What4.Value
import qualified Cryptol.Eval.What4.SFloat as W4
import Cryptol.Utils.Ident(PrimIdent, floatPrim)

-- | Table of floating point primitives
floatPrims :: W4.IsSymExprBuilder sym => What4 sym -> Map PrimIdent (Value sym)
floatPrims sym4@(What4 sym) =
  Map.fromList [ (floatPrim i,v) | (i,v) <- nonInfixTable ]
  where
  (~>) = (,)

  nonInfixTable =
    [ "fpNaN"       ~> fpConst (W4.fpNaN sym)
    , "fpPosInf"    ~> fpConst (W4.fpPosInf sym)
    , "fpFromBits"  ~> ilam \e -> ilam \p -> wlam sym4 \w ->
                       VFloat <$> liftIO (W4.fpFromBinary sym e p w)
    , "fpToBits"    ~> ilam \e -> ilam \p -> flam \x ->
                       VSeq (Nat (e+p)) TVBit <$> (unpackSeqMap sym4 =<< liftIO (W4.fpToBinary sym x))
    , "=.="         ~> ilam \_ -> ilam \_ -> flam \x -> pure $ flam \y ->
                       VBit <$> liftIO (W4.fpEq sym x y)
    , "fpIsFinite"  ~> ilam \_ -> ilam \_ -> flam \x ->
                       VBit <$> liftIO do inf <- W4.fpIsInf sym x
                                          nan <- W4.fpIsNaN sym x
                                          weird <- W4.orPred sym inf nan
                                          W4.notPred sym weird

    , "fpAdd"       ~> fpBinArithV sym4 fpPlus
    , "fpSub"       ~> fpBinArithV sym4 fpMinus
    , "fpMul"       ~> fpBinArithV sym4 fpMult
    , "fpDiv"       ~> fpBinArithV sym4 fpDiv

    , "fpFromRational" ~>
       ilam \e -> ilam \p -> wlam sym4 \r -> pure $ lam \x ->
       do rat <- fromVRational <$> x
          VFloat <$> fpCvtFromRational sym4 e p r rat

    , "fpToRational" ~>
       ilam \_e -> ilam \_p -> flam \fp ->
       VRational <$> fpCvtToRational sym4 fp
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


