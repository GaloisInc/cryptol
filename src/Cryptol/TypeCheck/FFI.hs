{-# LANGUAGE DeriveAnyClass  #-}
{-# LANGUAGE DeriveGeneric   #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns    #-}

module Cryptol.TypeCheck.FFI where

import           Control.DeepSeq
import           GHC.Generics

import           Cryptol.TypeCheck.SimpType
import           Cryptol.TypeCheck.Type

data FFIType
  = FFIBool
  | FFIBasic FFIBasicType
  | FFIArray Int FFIBasicType
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

data FFIFunType = FFIFunType
  { ffiArgTypes :: [FFIType]
  , ffiRetType  :: FFIType
  } deriving (Show, Generic, NFData)

toFFIFunType :: Schema -> Maybe FFIFunType
toFFIFunType (Forall [] [] t) = go $ tRebuild' False t
  where go (TCon (TC TCFun) [argType, retType]) = do
          arg <- toFFIType argType
          case go retType of
            Just ffiFunType -> Just ffiFunType
              { ffiArgTypes = arg : ffiArgTypes ffiFunType }
            Nothing -> do
              ffiRetType <- toFFIType retType
              Just FFIFunType { ffiArgTypes = [arg], .. }
        go _ = Nothing
toFFIFunType _ = Nothing

toFFIType :: Type -> Maybe FFIType
toFFIType (TCon (TC TCBit) []) = Just FFIBool
toFFIType (toFFIBasicType -> Just t) = Just $ FFIBasic t
toFFIType (TCon (TC TCSeq) [TCon (TC (TCNum n)) [], toFFIBasicType -> Just t])
  | n <= toInteger (maxBound :: Int) = Just $ FFIArray (fromInteger n) t
toFFIType _ = Nothing

toFFIBasicType :: Type -> Maybe FFIBasicType
toFFIBasicType (TCon (TC TCSeq) [TCon (TC (TCNum n)) [], TCon (TC TCBit) []])
  | n <= 8 = word FFIWord8
  | n <= 16 = word FFIWord16
  | n <= 32 = word FFIWord32
  | n <= 64 = word FFIWord64
  where word = Just . FFIWord n
toFFIBasicType
  (TCon (TC TCFloat) [TCon (TC (TCNum e)) [], TCon (TC (TCNum p)) []])
  | e == 8, p == 24 = float FFIFloat32
  | e == 11, p == 53 = float FFIFloat64
  where float = Just . FFIFloat e p
toFFIBasicType _ = Nothing
