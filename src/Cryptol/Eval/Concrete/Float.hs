{-# Language BlockArguments #-}
{-# Language OverloadedStrings #-}
-- | Concrete evaluations for floating point primitives.
module Cryptol.Eval.Concrete.Float where

import Data.Map(Map)
import Data.Ratio((%),numerator,denominator)
import qualified Data.Map as Map
import LibBF

import Cryptol.Utils.Ident(PrimIdent, floatPrim)
import Cryptol.Eval.Value
import Cryptol.Eval.Generic
import Cryptol.Eval.Concrete.Value
import Cryptol.Eval.Backend(SRational(..))
import Cryptol.Eval.Concrete.FloatHelpers



floatPrims :: Concrete -> Map PrimIdent Value
floatPrims sym = Map.fromList [ (floatPrim i,v) | (i,v) <- nonInfixTable ]
  where
  (~>) = (,)
  nonInfixTable =
    [ "fpNaN"       ~> ilam \e -> ilam \p ->
                        VFloat BF { bfValue = bfNaN
                                  , bfExpWidth = e, bfPrecWidth = p }

    , "fpPosInf"    ~> ilam \e -> ilam \p ->
                       VFloat BF { bfValue = bfPosInf
                                 , bfExpWidth = e, bfPrecWidth = p }

    , "fpFromBits"  ~> ilam \e -> ilam \p -> wlam sym \bv ->
                       pure $ VFloat $ floatFromBits e p $ bvVal bv

    , "fpToBits"    ~> ilam \e -> ilam \p -> flam \x ->
                       word sym (e + p)
                            $ floatToBits e p
                            $ bfValue x
    , "=.="         ~> ilam \_ -> ilam \_ -> flam \x -> pure $ flam \y ->
                       pure $ VBit
                            $ bitLit sym
                            $ bfCompare (bfValue x) (bfValue y) == EQ

    , "fpIsFinite"  ~> ilam \_ -> ilam \_ -> flam \x ->
                       pure $ VBit $ bitLit sym $ bfIsFinite $ bfValue x

      -- From Backend class
    , "fpAdd"      ~> fpBinArithV sym fpPlus
    , "fpSub"      ~> fpBinArithV sym fpMinus
    , "fpMul"      ~> fpBinArithV sym fpMult
    , "fpDiv"      ~> fpBinArithV sym fpDiv

    , "fpFromRational" ~>
      ilam \e -> ilam \p -> wlam sym \r -> pure $ lam \x ->
        do rat <- fromVRational <$> x
           VFloat <$> do mode <- fpRoundMode sym r
                         pure $ floatFromRational e p mode
                              $ sNum rat % sDenom rat
    , "fpToRational" ~>
      ilam \_e -> ilam \_p -> flam \fp ->
      case floatToRational "fpToRational" fp of
        Left err -> raiseError sym err
        Right r  -> pure $
                      VRational
                        SRational { sNum = numerator r, sDenom = denominator r }
    ]


