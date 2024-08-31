{-# Language CPP #-}
-- | Export builders for Cryptols values
module Cryptol.Backend.FFI.Export where

#ifdef FFI_ENABLED

#include "cry_ffi.h"

import Foreign
import Foreign.C.Types(CSize(..))
import Cryptol.Eval.Type(TValue)
import Cryptol.Backend.FFI.ValImport
import Cryptol.Backend.FFI.ValExport


foreign export ccall cry_bool :: Export Word8
foreign import ccall "&cry_bool" cry_bool_addr :: FunPtr (Export Word8)

foreign export ccall cry_small_uint :: Export Word64
foreign import ccall "&cry_small_uint" cry_small_uint_addr :: FunPtr (Export Word64)

foreign export ccall cry_small_sint :: Export Int64
foreign import ccall "&cry_small_sint" cry_small_sint_addr :: FunPtr (Export Int64)

foreign export ccall cry_large_int :: LargeIntFun
foreign import ccall "&cry_large_int" cry_large_int_addr :: FunPtr LargeIntFun

foreign export ccall cry_sign :: Export Word8
foreign import ccall "&cry_sign" cry_sign_addr :: FunPtr (Export Word8)

foreign export ccall cry_tag :: Export CSize
foreign import ccall "&cry_tag" cry_tag_addr :: FunPtr (Export CSize)


runImporter ::
  TValue ->
  (Ptr cryValImporter -> IO ()) ->
  IO (Either ImporterErrorMessage Value)
runBuilder ty k =
  allocaBytes #{size struct CryValImporter } $ \obj ->
  do self <- cryNewValueBuilder ty 
     #{poke struct CryValImporter, self}               obj self
     #{poke struct CryValImporter, send_bool}          obj cry_bool_addr
     #{poke struct CryValImporter, send_small_uint}    obj cry_small_uint_addr
     #{poke struct CryValImporter, send_small_sint}    obj cry_small_sint_addr
     #{poke struct CryValImporter, send_tag}           obj cry_tag_addr
     #{poke struct CryValImporter, send_new_large_int} obj cry_large_int_addr
     #{poke struct CryValImporter, send_sign}          obj cry_sign_addr
     k obj
     cryFinishBuilder self

#else

runBuilder ::
  TValue ->
  (Ptr cryValBuilder -> IO ()) ->
  IO (Either ImporterErrorMessage Value)
runBuilder _ty _k = pure (Left FFINotEnabled)

#endif