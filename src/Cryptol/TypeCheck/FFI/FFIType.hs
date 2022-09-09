{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric  #-}
{-# LANGUAGE Safe  #-}

-- | This module defines a nicer intermediate representation of Cryptol types
-- allowed for the FFI, which the typechecker generates then stores in the AST.
-- This way the FFI evaluation code does not have to examine the raw type
-- signatures again.
module Cryptol.TypeCheck.FFI.FFIType where

import           Control.DeepSeq
import           GHC.Generics

import           Cryptol.TypeCheck.Type
import           Cryptol.Utils.Ident
import           Cryptol.Utils.RecordMap

-- | Type of a foreign function.
data FFIFunType = FFIFunType
  { -- | Note: any type variables within this function type must be bound here.
    ffiTParams  :: [TParam]
  , ffiArgTypes :: [FFIType]
  , ffiRetType  :: FFIType }
  deriving (Show, Generic, NFData)

-- | Type of a value that can be passed to or returned from a foreign function.
data FFIType
  = FFIBool
  | FFIBasic FFIBasicType
  -- | [n][m][p]T --> FFIArray [n, m, p] T
  | FFIArray [Type] FFIBasicType
  | FFITuple [FFIType]
  | FFIRecord (RecordMap Ident FFIType)
  deriving (Show, Generic, NFData)

-- | Types which can be elements of FFI arrays.
data FFIBasicType
  = FFIWord
      Integer     -- ^ The size of the Cryptol type
      FFIWordSize -- ^ The machine word size that it corresponds to
  | FFIFloat
      Integer      -- ^ Exponent
      Integer      -- ^ Precision
      FFIFloatSize -- ^ The machine float size that it corresponds to
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
