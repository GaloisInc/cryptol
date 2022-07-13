{-# LANGUAGE DeriveAnyClass  #-}
{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE RecordWildCards #-}

module Cryptol.TypeCheck.FFI where

import           Control.DeepSeq
import           GHC.Generics

import           Cryptol.TypeCheck.Type

data FFIRep
  = FFIBool
  | FFIWord8 Integer
  | FFIWord16 Integer
  | FFIWord32 Integer
  | FFIWord64 Integer
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
  | n <= 8 = Just $ FFIWord8 n
  | n <= 16 = Just $ FFIWord16 n
  | n <= 32 = Just $ FFIWord32 n
  | n <= 64 = Just $ FFIWord64 n
toFFIRep _ = Nothing
