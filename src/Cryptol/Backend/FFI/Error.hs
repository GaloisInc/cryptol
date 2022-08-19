{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric  #-}
{-# LANGUAGE Trustworthy  #-}

-- | Errors from dynamic loading of shared libraries for FFI.
module Cryptol.Backend.FFI.Error where

import           Control.DeepSeq
import           GHC.Generics

import           Cryptol.Utils.PP

data FFILoadError
  = CantLoadFFISrc
    FilePath -- ^ Path to cryptol module
    String   -- ^ Error message
  | CantLoadFFIImpl
    String   -- ^ Function name
    String   -- ^ Error message
  deriving (Show, Generic, NFData)

instance PP FFILoadError where
  ppPrec _ e =
    case e of
      CantLoadFFISrc path msg ->
        hang (text "Could not load foreign source for module located at"
              <+> text path <.> colon)
          4 (text msg)
      CantLoadFFIImpl name msg ->
        hang (text "Could not load foreign implementation for binding"
              <+> text name <.> colon)
          4 (text msg)
