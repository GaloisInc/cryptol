{-# LANGUAGE BlockArguments            #-}
{-# LANGUAGE CPP                       #-}
{-# LANGUAGE DeriveAnyClass            #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeApplications          #-}

-- | The implementation of loading and calling external functions from shared
-- libraries.
module Cryptol.Backend.FFI
  ( ForeignSrc
  , getForeignSrcPath
  , loadForeignSrc
  , unloadForeignSrc
  , foreignLibPath
#ifdef FFI_ENABLED
  , ForeignImpl
  , loadForeignImpl
  , FFIArg
  , FFIRet
  , SomeFFIArg (..)
  , callForeignImpl
#endif
  )
  where

import           Control.DeepSeq

import           Cryptol.Backend.FFI.Error

#ifdef FFI_ENABLED

import           Control.Concurrent.MVar
import           Control.Exception
import           Control.Monad
import           Data.Bifunctor
import           Data.Word
import           Foreign                    hiding (newForeignPtr)
import           Foreign.C.Types
import           Foreign.Concurrent
import           Foreign.LibFFI
import           System.FilePath            ((-<.>))
import           System.Directory(doesFileExist)
import           System.IO.Error
import           System.Info(os)

#if defined(mingw32_HOST_OS)
import           System.Win32.DLL
#else
import           System.Posix.DynamicLinker
#endif

import           Cryptol.Utils.Panic

#else

import           GHC.Generics

#endif

#ifdef FFI_ENABLED

-- | A source from which we can retrieve implementations of foreign functions.
data ForeignSrc = ForeignSrc
  { -- | The file path of the 'ForeignSrc'.
    foreignSrcPath   :: FilePath
    -- | The 'ForeignPtr' wraps the pointer returned by 'dlopen', where the
    -- finalizer calls 'dlclose' when the library is no longer needed. We keep
    -- references to the 'ForeignPtr' in each foreign function that is in the
    -- evaluation environment, so that the shared library will stay open as long
    -- as there are references to it.
  , foreignSrcFPtr   :: ForeignPtr ()
    -- | We support explicit unloading of the shared library so we keep track of
    -- if it has already been unloaded, and if so the finalizer does nothing.
    -- This is updated atomically when the library is unloaded.
  , foreignSrcLoaded :: MVar Bool }

instance Show ForeignSrc where
  show = show . foreignSrcFPtr

instance NFData ForeignSrc where
  rnf ForeignSrc {..} = foreignSrcFPtr `seq` foreignSrcLoaded `deepseq` ()

-- | Get the file path of the 'ForeignSrc'.
getForeignSrcPath :: ForeignSrc -> Maybe FilePath
getForeignSrcPath = Just . foreignSrcPath

-- | Load a 'ForeignSrc' for the given __Cryptol__ file path. The file path of
-- the shared library that we try to load is the same as the Cryptol file path
-- except with a platform specific extension.
loadForeignSrc :: FilePath -> IO (Either FFILoadError ForeignSrc)
loadForeignSrc = loadForeignLib >=> traverse \(foreignSrcPath, ptr) -> do
  foreignSrcLoaded <- newMVar True
  foreignSrcFPtr <- newForeignPtr ptr (unloadForeignSrc' foreignSrcLoaded ptr)
  pure ForeignSrc {..}


-- | Given the path to a Cryptol module, compute the location of
-- the shared library we'd like to load.
foreignLibPath :: FilePath -> IO (Maybe FilePath)
foreignLibPath path =
  search
    case os of
      "mingw32" -> ["dll"]
      "darwin"  -> ["dylib","so"]
      _         -> ["so"]

  where
  search es =
    case es of
      [] -> pure Nothing
      e : more ->
        do let p = path -<.> e
           yes <- doesFileExist p
           if yes then pure (Just p) else search more


loadForeignLib :: FilePath -> IO (Either FFILoadError (FilePath, Ptr ()))
loadForeignLib path =
  do mb <- foreignLibPath path
     case mb of
       Nothing      -> pure (Left (CantLoadFFISrc path "File not found"))
       Just libPath -> tryLoad (CantLoadFFISrc path) (open libPath)

  where open libPath = do
#if defined(mingw32_HOST_OS)
          ptr <- loadLibrary libPath
#else
          -- RTLD_NOW so we can make sure that the symbols actually exist at
          -- module loading time
          ptr <- undl <$> dlopen libPath [RTLD_NOW]
#endif
          pure (libPath, ptr)

-- | Explicitly unload a 'ForeignSrc' immediately instead of waiting for the
-- garbage collector to do it. This can be useful if you want to immediately
-- load the same library again to pick up new changes.
--
-- The 'ForeignSrc' __must not__ be used in any way after this is called,
-- including calling 'ForeignImpl's loaded from it.
unloadForeignSrc :: ForeignSrc -> IO ()
unloadForeignSrc ForeignSrc {..} = withForeignPtr foreignSrcFPtr $
  unloadForeignSrc' foreignSrcLoaded

unloadForeignSrc' :: MVar Bool -> Ptr () -> IO ()
unloadForeignSrc' loaded lib = modifyMVar_ loaded \l -> do
  when l $ unloadForeignLib lib
  pure False

unloadForeignLib :: Ptr () -> IO ()
#if defined(mingw32_HOST_OS)
unloadForeignLib = freeLibrary
#else
unloadForeignLib = dlclose . DLHandle
#endif

withForeignSrc :: ForeignSrc -> (Ptr () -> IO a) -> IO a
withForeignSrc ForeignSrc {..} f = withMVar foreignSrcLoaded
  \case
    True -> withForeignPtr foreignSrcFPtr f
    False ->
      panic "[FFI] withForeignSrc" ["Use of foreign library after unload"]

-- | An implementation of a foreign function.
data ForeignImpl = ForeignImpl
  { foreignImplFun :: FunPtr ()
    -- | We don't need this to call the function but we want to keep the library
    -- around as long as we still have a function from it so that it isn't
    -- unloaded too early.
  , foreignImplSrc :: ForeignSrc
  }

-- | Load a 'ForeignImpl' with the given name from the given 'ForeignSrc'.
loadForeignImpl :: ForeignSrc -> String -> IO (Either FFILoadError ForeignImpl)
loadForeignImpl foreignImplSrc name =
  withForeignSrc foreignImplSrc \lib ->
    tryLoad (CantLoadFFIImpl name) do
      foreignImplFun <- loadForeignFunPtr lib name
      pure ForeignImpl {..}

loadForeignFunPtr :: Ptr () -> String -> IO (FunPtr ())
#if defined(mingw32_HOST_OS)
loadForeignFunPtr source symbol = do
  addr <- getProcAddress source symbol
  pure $ castPtrToFunPtr addr
#else
loadForeignFunPtr = dlsym . DLHandle
#endif

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
callForeignImpl ForeignImpl {..} xs = withForeignSrc foreignImplSrc \_ ->
  callFFI foreignImplFun (ffiRet @a) $ map toArg xs
  where toArg (SomeFFIArg x) = ffiArg x

#else

data ForeignSrc = ForeignSrc deriving (Show, Generic, NFData)

getForeignSrcPath :: ForeignSrc -> Maybe FilePath
getForeignSrcPath _ = Nothing

loadForeignSrc :: FilePath -> IO (Either FFILoadError ForeignSrc)
loadForeignSrc _ = pure $ Right ForeignSrc

unloadForeignSrc :: ForeignSrc -> IO ()
unloadForeignSrc _ = pure ()

foreignLibPath :: FilePath -> IO (Maybe FilePath)
foreignLibPath _ = pure Nothing

#endif
