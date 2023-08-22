{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Safe  #-}

-- | Errors from dynamic loading of shared libraries for FFI.
module Cryptol.Backend.FFI.Error where

import           Control.DeepSeq
import           GHC.Generics

import           Cryptol.Utils.PP
import           Cryptol.ModuleSystem.Name

data FFILoadError
  = CantLoadFFISrc
    FilePath -- ^ Path to cryptol module
    String   -- ^ Error message
  | CantLoadFFIImpl
    String   -- ^ Function name
    String   -- ^ Error message
  | FFIDuplicates [Name]
  | FFIInFunctor  Name
  deriving (Show, Generic, NFData)

instance PP FFILoadError where
  ppPrec _ e =
    case e of
      CantLoadFFISrc path msg ->
        hang ("Could not load foreign source for module located at"
              <+> text path <.> colon)
          4 (text msg)
      CantLoadFFIImpl name _msg ->
        "Could not load foreign implementation for binding" <+> text name
        -- We don't print the OS error message for more consistent test output
        -- hang ("Could not load foreign implementation for binding"
        --       <+> text name <.> colon)
        --   4 (text _msg)
      FFIDuplicates xs ->
        hang "Multiple foreign declarations with the same name:"
           4 (backticks (pp (nameIdent (head xs))) <+>
                 "defined at" <+> align (vcat (map (pp . nameLoc) xs)))
      FFIInFunctor x ->
        hang (pp (nameLoc x) <.> ":")
          4 "Foreign declaration" <+> backticks (pp (nameIdent x)) <+>
                "may not appear in a parameterized module."
