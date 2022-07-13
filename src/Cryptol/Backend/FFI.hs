{-# LANGUAGE BlockArguments            #-}
{-# LANGUAGE CPP                       #-}
{-# LANGUAGE DeriveAnyClass            #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeSynonymInstances      #-}

-- We need some instances that the unix package doesn't define
{-# OPTIONS_GHC -Wno-orphans #-}

module Cryptol.Backend.FFI
#ifdef FFI_ENABLED
  ( ForeignSrc
  , ForeignImpl
  , loadForeignSrc
  , loadForeignImpl
  , FFIType
  , callForeignImpl
  )
#endif
  where

#ifdef FFI_ENABLED

import           Control.DeepSeq
import           Control.Exception
import           Control.Monad
import           Data.Bifunctor
import           Data.IORef
import           Data.Word
import           Foreign.Concurrent
import           Foreign.ForeignPtr         (ForeignPtr, withForeignPtr)
import           Foreign.LibFFI
import           Foreign.Ptr
import           GHC.Generics
import           System.FilePath            ((-<.>))
import           System.IO.Error
import           System.Posix.DynamicLinker

import           Cryptol.Backend.FFI.Error

-- | A 'ForeignSrc' consists of a handle to the dynamically loaded library and
-- a reference count for the number of foreign functions from the library that
-- are still in memory.
-- When all references to the foreign functions are garbage collected the
-- library will be closed by the 'ForeignPtr' finalizer in 'loadForeignImpl'.
data ForeignSrc = ForeignSrc
  { foreignLib  :: !ForeignLib
  , foreignRefs :: !(IORef Word) }

type ForeignLib = DL

deriving instance Generic ForeignLib
deriving instance NFData ForeignLib

loadForeignSrc :: FilePath -> IO (Either FFILoadError ForeignSrc)
loadForeignSrc = loadForeignLib >=> traverse \foreignLib -> do
  foreignRefs <- newIORef 0
  pure ForeignSrc {..}

loadForeignLib :: FilePath -> IO (Either FFILoadError ForeignLib)
#ifdef darwin_HOST_OS
loadForeignLib path =
  (Right <$> open "dylib") `catchIOError` \e1 ->
    (Right <$> open "so") `catchIOError` \e2 ->
      pure $ Left $ CantLoadFFISrc path $
        displayException e1 ++ "\n" ++ displayException e2
#else
loadForeignLib path =
  tryLoad (CantLoadFFISrc path) $ open "so"
#endif
  where
  open ext = dlopen (path -<.> ext) [RTLD_NOW]

unloadForeignLib :: ForeignLib -> IO ()
unloadForeignLib = dlclose

data ForeignImpl = forall a. ForeignImpl (ForeignPtr a)

loadForeignImpl :: ForeignSrc -> String -> IO (Either FFILoadError ForeignImpl)
loadForeignImpl ForeignSrc {..} name = tryLoad (CantLoadFFIImpl name) do
  ptr <- castFunPtrToPtr <$> loadForeignFunPtr foreignLib name
  atomicModifyIORef' foreignRefs (\n -> (succ n, ()))
  ForeignImpl <$> newForeignPtr ptr do
    n <- atomicModifyIORef' foreignRefs (\n -> let n' = pred n in (n', n'))
    when (n == 0) $ unloadForeignLib foreignLib

loadForeignFunPtr :: ForeignLib -> String -> IO (FunPtr a)
loadForeignFunPtr = dlsym

tryLoad :: (String -> FFILoadError) -> IO a -> IO (Either FFILoadError a)
tryLoad err = fmap (first $ err . displayException) . tryIOError

class FFIType a where
  ffiArg :: a -> Arg
  ffiRet :: RetType a

instance FFIType Word8 where
  ffiArg = argWord8
  ffiRet = retWord8

instance FFIType Word16 where
  ffiArg = argWord16
  ffiRet = retWord16

instance FFIType Word32 where
  ffiArg = argWord32
  ffiRet = retWord32

instance FFIType Word64 where
  ffiArg = argWord64
  ffiRet = retWord64

callForeignImpl :: forall a b.
  (FFIType a, FFIType b) => ForeignImpl -> a -> IO b
callForeignImpl (ForeignImpl fp) x = withForeignPtr fp \p ->
  callFFI (castPtrToFunPtr p) (ffiRet @b) [ffiArg x]

#endif
