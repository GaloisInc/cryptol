{-# LANGUAGE DeriveAnyClass  #-}
{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE RecordWildCards #-}

module Cryptol.TypeCheck.FFI where

import           Control.DeepSeq
import           GHC.Generics

import           Cryptol.TypeCheck.Type

data FFIRep
  = FFIBool
  | FFIWord Integer FFIWordSize
  deriving (Show, Generic, NFData)

data FFIWordSize
  = FFIWord8
  | FFIWord16
  | FFIWord32
  | FFIWord64
  deriving (Show, Generic, NFData)

data FFIFunRep = FFIFunRep
  { ffiArgRep :: FFIRep
  , ffiRetRep :: FFIRep
  } deriving (Show, Generic, NFData)

toFFIFunRep :: Schema -> Maybe FFIFunRep
toFFIFunRep (Forall [] [] (TCon (TC TCFun) [argType, retType])) = do
  ffiArgRep <- toFFIRep argType
  ffiRetRep <- toFFIRep retType
  pure FFIFunRep {..}
toFFIFunRep _ = Nothing

toFFIRep :: Type -> Maybe FFIRep
toFFIRep (TCon (TC TCBit) []) = Just FFIBool
toFFIRep (TCon (TC TCSeq) [TCon (TC (TCNum n)) [], TCon (TC TCBit) []])
  | n <= 8 = word FFIWord8
  | n <= 16 = word FFIWord16
  | n <= 32 = word FFIWord32
  | n <= 64 = word FFIWord64
  where word = Just . FFIWord n
toFFIRep _ = Nothing
