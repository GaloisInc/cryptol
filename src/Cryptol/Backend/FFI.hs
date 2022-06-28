{-# LANGUAGE DeriveAnyClass            #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE TypeSynonymInstances      #-}

-- We need some instances that the unix package doesn't define
{-# OPTIONS_GHC -Wno-orphans #-}

module Cryptol.Backend.FFI where

import           Control.DeepSeq
import           Data.Word
import           Foreign.LibFFI
import           Foreign.Ptr
import           GHC.Generics
import           System.FilePath
import           System.Posix.DynamicLinker

type ForeignSrc = DL

deriving instance Generic ForeignSrc
deriving instance NFData ForeignSrc

loadForeignSrc :: FilePath -> IO ForeignSrc
loadForeignSrc path = dlopen (path -<.> "so") [RTLD_NOW]

unloadForeignSrc :: ForeignSrc -> IO ()
unloadForeignSrc = dlclose

data ForeignImpl = forall a. ForeignImpl (FunPtr a)

loadForeignImpl :: ForeignSrc -> String -> IO ForeignImpl
loadForeignImpl src = fmap ForeignImpl . dlsym src

callForeignImpl :: ForeignImpl -> Word64 -> IO Word64
callForeignImpl (ForeignImpl p) x = callFFI p retWord64 [argWord64 x]
