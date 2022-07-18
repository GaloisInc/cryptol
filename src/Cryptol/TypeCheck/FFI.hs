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

data FFIFunRep = FFIFunRep
  { ffiArgReps :: [FFIRep]
  , ffiRetRep  :: FFIRep
  } deriving (Show, Generic, NFData)

toFFIFunRep :: Schema -> Maybe FFIFunRep
toFFIFunRep (Forall [] [] t) = go t
  where go (TCon (TC TCFun) [argType, retType]) = do
          arg <- toFFIRep argType
          case go retType of
            Just funRep -> Just funRep { ffiArgReps = arg : ffiArgReps funRep }
            Nothing -> do
              ffiRetRep <- toFFIRep retType
              Just FFIFunRep { ffiArgReps = [arg], .. }
        go _ = Nothing
toFFIFunRep _ = Nothing

toFFIRep :: Type -> Maybe FFIRep
toFFIRep (TCon (TC TCBit) []) = Just FFIBool
toFFIRep (TCon (TC TCSeq) [TCon (TC (TCNum n)) [], TCon (TC TCBit) []])
  | n <= 8 = word FFIWord8
  | n <= 16 = word FFIWord16
  | n <= 32 = word FFIWord32
  | n <= 64 = word FFIWord64
  where word = Just . FFIWord n
toFFIRep (TCon (TC TCFloat) [TCon (TC (TCNum e)) [], TCon (TC (TCNum p)) []])
  | e == 8, p == 24 = float FFIFloat32
  | e == 11, p == 53 = float FFIFloat64
  where float = Just . FFIFloat e p
toFFIRep _ = Nothing
