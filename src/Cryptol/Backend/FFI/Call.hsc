{-# Language CPP #-}
-- | Calling a foreign function
module Cryptol.Backend.FFI.Call where

#ifdef FFI_ENABLED

#include "cry_ffi.h"

import Foreign
import Foreign.C.Types(CSize(..))
import Cryptol.Eval.Type(TValue)
import Cryptol.Backend.FFI.ValImport
import Cryptol.Backend.FFI.ValExport


foreign export ccall cry_bool :: Import Word8
foreign import ccall "&cry_bool" cry_bool_addr :: FunPtr (Import Word8)

foreign export ccall cry_small_uint :: Import Word64
foreign import ccall "&cry_small_uint" cry_small_uint_addr :: FunPtr (Import Word64)

foreign export ccall cry_small_sint :: Import Int64
foreign import ccall "&cry_small_sint" cry_small_sint_addr :: FunPtr (Import Int64)

foreign export ccall cry_large_int :: LargeIntFun
foreign import ccall "&cry_large_int" cry_large_int_addr :: FunPtr LargeIntFun

foreign export ccall cry_sign :: Import Word8
foreign import ccall "&cry_sign" cry_sign_addr :: FunPtr (Import Word8)

foreign export ccall cry_tag :: Import CSize
foreign import ccall "&cry_tag" cry_tag_addr :: FunPtr (Import CSize)

foreign export ccall cry_recv_u8 :: Export Word8
foreign import ccall "&cry_recv_u8" cry_recv_u8_addr :: FunPtr (Export Word8)

foreign export ccall cry_recv_u64 :: Export Word64
foreign import ccall "&cry_recv_u64" cry_recv_u64_addr :: FunPtr (Export Word64)

foreign export ccall cry_recv_u64_digits :: Export Word64
foreign import ccall "&cry_recv_u64_digits" cry_recv_u64_digits_addr :: FunPtr (Export Word64)



runFFI ::
  [ExportVal] {-^ Reversed, see `exportValues` -} ->
  TValue      {-^ Type of result -} ->
  (Ptr cryValExporter -> Ptr cryValImporter -> IO ()) {- ^ Foreign function -} ->
  IO (Either ImportErrorMessage Value) {- ^ Result of call, or an error -}
runFFI args ty k =
  allocaBytes #{size struct CryValImporter} $ \robj ->
  allocaBytes #{size struct CryValExporter} $ \aobj ->
  
  do expS <- cryStartExport args
     #{poke struct CryValExporter, self}            aobj expS
     #{poke struct CryValExporter, recv_u8}         aobj cry_recv_u8_addr
     #{poke struct CryValExporter, recv_u64}        aobj cry_recv_u64_addr
     #{poke struct CryValExporter, recv_u64_digits} aobj cry_recv_u64_digits_addr
     impS <- cryStartImport ty 
     #{poke struct CryValImporter, self}               robj impS
     #{poke struct CryValImporter, send_bool}          robj cry_bool_addr
     #{poke struct CryValImporter, send_small_uint}    robj cry_small_uint_addr
     #{poke struct CryValImporter, send_small_sint}    robj cry_small_sint_addr
     #{poke struct CryValImporter, send_tag}           robj cry_tag_addr
     #{poke struct CryValImporter, send_new_large_int} robj cry_large_int_addr
     #{poke struct CryValImporter, send_sign}          robj cry_sign_addr
     k aobj robj
     cryEndExport expS
     cryFinishImport impS

#else

runFFI ::
  [ExportVal] ->
  TValue ->
  (Ptr cryValExporter -> Ptr cryValBuilder -> IO ()) ->
  IO (Either ImportErrorMessage Value)
runFFI _args _ty _k = pure (Left FFINotEnabled)

#endif