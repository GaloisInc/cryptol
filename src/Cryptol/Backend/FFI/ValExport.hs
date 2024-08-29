module Cryptol.Backend.FFI.ValExport where

import Foreign

import Cryptol.Eval.Value


data ExpVal =
    EVBool !Bool
  | EVInteger !Integer
  | EVWord !Integer !Integer