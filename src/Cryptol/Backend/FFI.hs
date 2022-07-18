{-# LANGUAGE BlockArguments            #-}
{-# LANGUAGE CPP                       #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeApplications          #-}

module Cryptol.Backend.FFI
#ifdef FFI_ENABLED
  ( ForeignSrc
  , ForeignImpl
  , loadForeignSrc
  , loadForeignImpl
  , FFIType
  , SomeFFIType (..)
  , callForeignImpl
  )
#endif
  where

#ifdef FFI_ENABLED

import           Control.Exception
import           Control.Monad
import           Data.Bifunctor
import           Data.Word
import           Foreign.C.Types
import           Foreign.Concurrent
import           Foreign.ForeignPtr         (ForeignPtr, withForeignPtr)
import           Foreign.LibFFI
import           Foreign.Ptr
import           System.FilePath            ((-<.>))
import           System.IO.Error
import           System.Posix.DynamicLinker

import           Cryptol.Backend.FFI.Error

newtype ForeignSrc = ForeignSrc (ForeignPtr ())

loadForeignSrc :: FilePath -> IO (Either FFILoadError ForeignSrc)
loadForeignSrc = loadForeignLib >=> traverse \ptr ->
  -- Set up the destructor to automatically close the library when there are no
  -- more references to it
  ForeignSrc <$> newForeignPtr ptr (unloadForeignLib ptr)

loadForeignLib :: FilePath -> IO (Either FFILoadError (Ptr ()))
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
  where open ext = undl <$> dlopen (path -<.> ext) [RTLD_NOW]

unloadForeignLib :: Ptr () -> IO ()
unloadForeignLib = dlclose . DLHandle

data ForeignImpl = ForeignImpl
  { foreignImplFun :: FunPtr ()
    -- We don't need this to call the function but we want to keep the library
    -- around as long as we still have a function from it so that the destructor
    -- isn't called too early
  , foreignImplLib :: ForeignPtr ()
  }

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

instance FFIType CFloat where
  ffiArg = argCFloat
  ffiRet = retCFloat

instance FFIType CDouble where
  ffiArg = argCDouble
  ffiRet = retCDouble

data SomeFFIType = forall a. FFIType a => SomeFFIType a

callForeignImpl :: forall a. FFIType a => ForeignImpl -> [SomeFFIType] -> IO a
callForeignImpl ForeignImpl {..} xs = withForeignPtr foreignImplLib \_ ->
  callFFI foreignImplFun (ffiRet @a) $ map toArg xs
  where toArg (SomeFFIType x) = ffiArg x

#endif
