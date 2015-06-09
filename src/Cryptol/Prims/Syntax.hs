-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

module Cryptol.Prims.Syntax
  ( TFun(..), tBinOpPrec, tfunNames
  ) where

import           Cryptol.ModuleSystem.Name (QName,Name(Name),mkUnqual)
import           Cryptol.Utils.PP
import qualified Data.Map as Map


-- | Built-in types.
data TFun

  = TCAdd                 -- ^ @ : Num -> Num -> Num @
  | TCSub                 -- ^ @ : Num -> Num -> Num @
  | TCMul                 -- ^ @ : Num -> Num -> Num @
  | TCDiv                 -- ^ @ : Num -> Num -> Num @
  | TCMod                 -- ^ @ : Num -> Num -> Num @
  | TCLg2                 -- ^ @ : Num -> Num @
  | TCExp                 -- ^ @ : Num -> Num -> Num @
  | TCWidth               -- ^ @ : Num -> Num @
  | TCMin                 -- ^ @ : Num -> Num -> Num @
  | TCMax                 -- ^ @ : Num -> Num -> Num @

  -- Computing the lengths of explicit enumerations
  | TCLenFromThen         -- ^ @ : Num -> Num -> Num -> Num@
    -- Example: @[ 1, 5 .. ] :: [lengthFromThen 1 5 b][b]@

  | TCLenFromThenTo       -- ^ @ : Num -> Num -> Num -> Num@
    -- Example: @[ 1, 5 .. 9 ] :: [lengthFromThenTo 1 5 9][b]@

    deriving (Show, Eq, Ord, Bounded, Enum)


tBinOpPrec :: Map.Map TFun (Assoc,Int)
tBinOpPrec  = mkMap t_table
  where
  mkMap t = Map.fromList [ (op,(a,n)) | ((a,ops),n) <- zip t [1..] , op <- ops ]

  -- lowest to highest
  t_table =
    [ (LeftAssoc,   [ TCAdd, TCSub ])
    , (LeftAssoc,   [ TCMul, TCDiv, TCMod ])
    , (RightAssoc,  [ TCExp ])
    ]

tfunNames :: Map.Map QName TFun
tfunNames  = Map.fromList
  [ tprim "+"                TCAdd
  , tprim "-"                TCSub
  , tprim "*"                TCMul
  , tprim "/"                TCDiv
  , tprim "%"                TCMod
  , tprim "^^"               TCExp
  , tprim "lg2"              TCLg2
  , tprim "width"            TCWidth
  , tprim "min"              TCMin
  , tprim "max"              TCMax
  , tprim "lengthFromThen"   TCLenFromThen
  , tprim "lengthFromThenTo" TCLenFromThenTo
  ]
  where
  tprim n p = (mkUnqual (Name n), p)

instance PP TFun where
  ppPrec _ tcon =
    case tcon of
      TCAdd             -> text "+"
      TCSub             -> text "-"
      TCMul             -> text "*"
      TCDiv             -> text "/"
      TCMod             -> text "%"
      TCLg2             -> text "lg2"
      TCExp             -> text "^^"
      TCWidth           -> text "width"
      TCMin             -> text "min"
      TCMax             -> text "max"

      TCLenFromThen     -> text "lengthFromThen"
      TCLenFromThenTo   -> text "lengthFromThenTo"
