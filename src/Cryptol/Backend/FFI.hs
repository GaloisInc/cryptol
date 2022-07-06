{-# LANGUAGE BlockArguments            #-}
{-# LANGUAGE CPP                       #-}
{-# LANGUAGE DeriveAnyClass            #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE TypeSynonymInstances      #-}

-- We need some instances that the unix package doesn't define
{-# OPTIONS_GHC -Wno-orphans #-}

#ifdef FFI_ENABLED

module Cryptol.Backend.FFI
  ( ForeignSrc
  , ForeignImpl
  , loadForeignSrc
  , loadForeignImpl
  , callForeignImpl
  ) where

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

data ForeignImpl = forall a. ForeignImpl (ForeignPtr a)

loadForeignSrc :: FilePath -> IO (Either FFILoadError ForeignSrc)
loadForeignSrc path = tryLoad (CantLoadFFISrc path) do
  foreignLib <- loadForeignLib path
  foreignRefs <- newIORef 0
  pure ForeignSrc {..}

loadForeignLib :: FilePath -> IO ForeignLib
loadForeignLib path = dlopen (path -<.> "so") [RTLD_NOW]

unloadForeignLib :: ForeignLib -> IO ()
unloadForeignLib = dlclose

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

callForeignImpl :: ForeignImpl -> Word64 -> IO Word64
callForeignImpl (ForeignImpl fp) x = withForeignPtr fp \p ->
  callFFI (castPtrToFunPtr p) retWord64 [argWord64 x]

#else

module Cryptol.Backend.FFI where

#endif
