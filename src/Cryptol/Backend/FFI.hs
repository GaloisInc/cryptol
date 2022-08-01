{-# LANGUAGE BlockArguments            #-}
{-# LANGUAGE CPP                       #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeApplications          #-}

-- | The implementation of loading and calling external functions from shared
-- libraries. Currently works on Unix only.
module Cryptol.Backend.FFI
#ifdef FFI_ENABLED
  ( ForeignSrc
  , loadForeignSrc
  , ForeignImpl
  , loadForeignImpl
  , FFIArg
  , FFIRet
  , SomeFFIArg (..)
  , callForeignImpl
  )
#endif
  where

#ifdef FFI_ENABLED

import           Control.Exception
import           Control.Monad
import           Data.Bifunctor
import           Data.Word
import           Foreign                    hiding (newForeignPtr)
import           Foreign.C.Types
import           Foreign.Concurrent
import           Foreign.LibFFI
import           System.FilePath            ((-<.>))
import           System.IO.Error
import           System.Posix.DynamicLinker

import           Cryptol.Backend.FFI.Error

-- | A source from which we can retrieve implementations of foreign functions.
--
-- This is implemented as a 'ForeignPtr' wrapper around the pointer returned by
-- 'dlopen', where the destructor calls 'dlclose' when the library is no longer
-- needed. We keep references to the 'ForeignPtr' in each foreign function that
-- is in the evaluation environment, so when the Cryptol module is unloaded, the
-- shared library will be closed too.
newtype ForeignSrc = ForeignSrc (ForeignPtr ())

-- | Load a 'ForeignSrc' for the given __Cryptol__ file path. The file path of
-- the shared library that we try to load is the same as the Cryptol file path
-- except with a platform specific extension.
loadForeignSrc :: FilePath -> IO (Either FFILoadError ForeignSrc)
loadForeignSrc = loadForeignLib >=> traverse \ptr ->
  ForeignSrc <$> newForeignPtr ptr (unloadForeignLib ptr)

loadForeignLib :: FilePath -> IO (Either FFILoadError (Ptr ()))
#ifdef darwin_HOST_OS
-- On Darwin, try loading .dylib first, and if that fails try .so
loadForeignLib path =
  (Right <$> open "dylib") `catchIOError` \e1 ->
    (Right <$> open "so") `catchIOError` \e2 ->
      pure $ Left $ CantLoadFFISrc path $
        displayException e1 ++ "\n" ++ displayException e2
#else
-- On other platforms, use .so
loadForeignLib path =
  tryLoad (CantLoadFFISrc path) $ open "so"
#endif
  where -- RTLD_NOW so we can make sure that the symbols actually exist at
        -- module loading time
        open ext = undl <$> dlopen (path -<.> ext) [RTLD_NOW]

unloadForeignLib :: Ptr () -> IO ()
unloadForeignLib = dlclose . DLHandle

-- | An implementation of a foreign function.
data ForeignImpl = ForeignImpl
  { foreignImplFun :: FunPtr ()
    -- | We don't need this to call the function but we want to keep the library
    -- around as long as we still have a function from it so that the destructor
    -- isn't called too early.
  , foreignImplLib :: ForeignPtr ()
  }

-- | Load a 'ForeignImpl' with the given name from the given 'ForeignSrc'.
loadForeignImpl :: ForeignSrc -> String -> IO (Either FFILoadError ForeignImpl)
loadForeignImpl (ForeignSrc foreignImplLib) name =
  withForeignPtr foreignImplLib \lib ->
    tryLoad (CantLoadFFIImpl name) do
      foreignImplFun <- loadForeignFunPtr lib name
      pure ForeignImpl {..}

loadForeignFunPtr :: Ptr () -> String -> IO (FunPtr ())
loadForeignFunPtr = dlsym . DLHandle

tryLoad :: (String -> FFILoadError) -> IO a -> IO (Either FFILoadError a)
tryLoad err = fmap (first $ err . displayException) . tryIOError

-- | Types which can be converted into libffi arguments.
--
-- The Storable constraint is so that we can put them in arrays.
class Storable a => FFIArg a where
  ffiArg :: a -> Arg

instance FFIArg Word8 where
  ffiArg = argWord8

instance FFIArg Word16 where
  ffiArg = argWord16

instance FFIArg Word32 where
  ffiArg = argWord32

instance FFIArg Word64 where
  ffiArg = argWord64

instance FFIArg CFloat where
  ffiArg = argCFloat

instance FFIArg CDouble where
  ffiArg = argCDouble

instance FFIArg (Ptr a) where
  ffiArg = argPtr

instance FFIArg CSize where
  ffiArg = argCSize

-- | Types which can be returned from libffi.
--
-- The Storable constraint is so that we can put them in arrays.
class Storable a => FFIRet a where
  ffiRet :: RetType a

instance FFIRet Word8 where
  ffiRet = retWord8

instance FFIRet Word16 where
  ffiRet = retWord16

instance FFIRet Word32 where
  ffiRet = retWord32

instance FFIRet Word64 where
  ffiRet = retWord64

instance FFIRet CFloat where
  ffiRet = retCFloat

instance FFIRet CDouble where
  ffiRet = retCDouble

instance FFIRet () where
  ffiRet = retVoid

-- | Existential wrapper around a 'FFIArg'.
data SomeFFIArg = forall a. FFIArg a => SomeFFIArg a

-- | Call a 'ForeignImpl' with the given arguments. The type parameter decides
-- how the return value should be converted into a Haskell value.
callForeignImpl :: forall a. FFIRet a => ForeignImpl -> [SomeFFIArg] -> IO a
callForeignImpl ForeignImpl {..} xs = withForeignPtr foreignImplLib \_ ->
  callFFI foreignImplFun (ffiRet @a) $ map toArg xs
  where toArg (SomeFFIArg x) = ffiArg x

#endif
