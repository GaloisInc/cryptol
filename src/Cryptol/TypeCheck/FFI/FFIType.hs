{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric  #-}

module Cryptol.TypeCheck.FFI.FFIType where

import           Control.DeepSeq
import           GHC.Generics

import           Cryptol.TypeCheck.Type
import           Cryptol.Utils.Ident
import           Cryptol.Utils.RecordMap

data FFIFunType = FFIFunType
  { ffiTParams  :: [TParam]
  , ffiArgTypes :: [FFIType]
  , ffiRetType  :: FFIType }
  deriving (Show, Generic, NFData)

data FFIType
  = FFIBool
  | FFIBasic FFIBasicType
  | FFIArray Type FFIBasicType
  | FFITuple [FFIType]
  | FFIRecord (RecordMap Ident FFIType)
  deriving (Show, Generic, NFData)

data FFIBasicType
  = FFIWord Integer FFIWordSize
  | FFIFloat Integer Integer FFIFloatSize
  deriving (Show, Generic, NFData)

data FFIWordSize
  = FFIWord8
  | FFIWord16
  | FFIWord32
  | FFIWord64
  deriving (Show, Generic, NFData)

data FFIFloatSize
  = FFIFloat32
  | FFIFloat64
  deriving (Show, Generic, NFData)
