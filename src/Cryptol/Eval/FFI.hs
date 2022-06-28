{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase     #-}

module Cryptol.Eval.FFI where

import           Cryptol.Backend
import           Cryptol.Backend.Monad
import           Cryptol.Backend.WordValue
import           Cryptol.Eval.Prims
import           Cryptol.Eval.Value

foreignPrim :: Backend sym => sym -> SForeignImpl sym -> Prim sym
foreignPrim sym impl = PStrict \case
  VWord 64 wv -> PPrim $
    VWord 64 . wordVal <$> (asWordVal sym wv >>= sCallForeign sym impl)
  _           -> evalPanic "foreignPrim" ["Argument is not a 64-bit word"]
