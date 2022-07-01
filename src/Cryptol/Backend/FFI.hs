{-# LANGUAGE DeriveAnyClass            #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE TypeSynonymInstances      #-}

-- We need some instances that the unix package doesn't define
{-# OPTIONS_GHC -Wno-orphans #-}

module Cryptol.Backend.FFI
  ( ForeignSrc
  , ForeignImpl
  , FFILoadError (..)
  , loadForeignSrc
  , unloadForeignSrc
  , loadForeignImpl
  , callForeignImpl
  ) where

import           Control.DeepSeq
import           Control.Exception
import           Data.Bifunctor
import           Data.Word
import           Foreign.LibFFI
import           Foreign.Ptr
import           GHC.Generics
import           System.FilePath            ((-<.>))
import           System.IO.Error
import           System.Posix.DynamicLinker

import           Cryptol.Utils.PP

type ForeignSrc = DL

deriving instance Generic ForeignSrc
deriving instance NFData ForeignSrc

data ForeignImpl = forall a. ForeignImpl (FunPtr a)

data FFILoadError
  = CantLoadFFISrc
    FilePath -- ^ Path to cryptol module
    String   -- ^ Error message
  | CantLoadFFIImpl
    String   -- ^ Function name
    String   -- ^ Error message
  deriving (Show, Generic, NFData)

instance PP FFILoadError where
  ppPrec _ e = case e of
    CantLoadFFISrc path msg ->
      hang (text "Could not load foreign source for module located at"
            <+> text path <.> colon)
         4 (text msg)
    CantLoadFFIImpl name msg ->
      hang (text "Could not load foreign implementation for binding"
            <+> text name <.> colon)
         4 (text msg)

loadForeignSrc :: FilePath -> IO (Either FFILoadError ForeignSrc)
loadForeignSrc path =
  tryLoad (CantLoadFFISrc path) $ dlopen (path -<.> "so") [RTLD_NOW]

unloadForeignSrc :: ForeignSrc -> IO ()
unloadForeignSrc = dlclose

loadForeignImpl :: ForeignSrc -> String -> IO (Either FFILoadError ForeignImpl)
loadForeignImpl src name =
  tryLoad (CantLoadFFIImpl name) $ ForeignImpl <$> dlsym src name

tryLoad :: (String -> FFILoadError) -> IO a -> IO (Either FFILoadError a)
tryLoad err = fmap (first $ err . displayException) . tryIOError

callForeignImpl :: ForeignImpl -> Word64 -> IO Word64
callForeignImpl (ForeignImpl p) x = callFFI p retWord64 [argWord64 x]
