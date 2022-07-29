{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Cryptol.TypeCheck.FFI.Error where

import           Control.DeepSeq
import           GHC.Generics

import           Cryptol.TypeCheck.PP
import           Cryptol.TypeCheck.Subst
import           Cryptol.TypeCheck.Type

data FFITypeError = FFITypeError Type FFITypeErrorReason
  deriving (Show, Generic, NFData)

data FFITypeErrorReason
  = FFIBadWordSize
  | FFIBadFloatSize
  | FFIBadArrayType
  | FFIBadComponentTypes [FFITypeError]
  | FFIBadType
  | FFINotFunction
  deriving (Show, Generic, NFData)

instance TVars FFITypeError where
  apSubst su (FFITypeError t r) = FFITypeError !$ apSubst su t !$ apSubst su r

instance TVars FFITypeErrorReason where
  apSubst su r = case r of
    FFIBadWordSize            -> r
    FFIBadFloatSize           -> r
    FFIBadArrayType           -> r
    FFIBadComponentTypes errs -> FFIBadComponentTypes !$ apSubst su errs
    FFIBadType                -> r
    FFINotFunction            -> r

instance FVS FFITypeError where
  fvs (FFITypeError t r) = fvs (t, r)

instance FVS FFITypeErrorReason where
  fvs r = case r of
    FFIBadWordSize            -> mempty
    FFIBadFloatSize           -> mempty
    FFIBadArrayType           -> mempty
    FFIBadComponentTypes errs -> fvs errs
    FFIBadType                -> mempty
    FFINotFunction            -> mempty

instance PP (WithNames FFITypeError) where
  ppPrec _ (WithNames (FFITypeError t r) names) =
    nest 2 $ "Type unsupported for FFI:" $$
      vcat
        [ ppWithNames names t
        , "Due to:"
        , ppWithNames names r ]

instance PP (WithNames FFITypeErrorReason) where
  ppPrec _ (WithNames r names) = case r of
    FFIBadWordSize -> vcat
      [ "Unsupported word size"
      , "Only words of up to 64 bits are supported" ]
    FFIBadFloatSize -> vcat
      [ "Unsupported Float format"
      , "Only Float32 and Float64 are supported" ]
    FFIBadArrayType -> vcat
      [ "Unsupported sequence element type"
      , "Only words or floats are supported as the element type of sequences" ]
    FFIBadComponentTypes errs -> indent 2 $ vcat $ map (ppWithNames names) errs
    FFIBadType -> vcat
      [ "Only Bit, words, floats, sequences of words or floats,"
      , "or structs or tuples of the above are supported as FFI"
      , "argument or return types"]
    FFINotFunction -> "FFI binding must be a function"
