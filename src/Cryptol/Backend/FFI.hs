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

data SomeFFIArg = forall a. FFIArg a => SomeFFIArg a

callForeignImpl :: forall a. FFIRet a => ForeignImpl -> [SomeFFIArg] -> IO a
callForeignImpl ForeignImpl {..} xs = withForeignPtr foreignImplLib \_ ->
  callFFI foreignImplFun (ffiRet @a) $ map toArg xs
  where toArg (SomeFFIArg x) = ffiArg x

#endif
