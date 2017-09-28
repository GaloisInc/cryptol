-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
module Cryptol.Prims.Syntax
  ( TFun(..), tBinOpPrec, tfunNames
  ) where

import           Cryptol.Parser.Name (PName,mkUnqual)
import           Cryptol.Utils.Ident (packIdent,packInfix)
import           Cryptol.Utils.PP
import qualified Data.Map as Map

import GHC.Generics (Generic)
import Control.DeepSeq

-- | Built-in types.
data TFun

  = TCAdd                 -- ^ @ : Num -> Num -> Num @
  | TCSub                 -- ^ @ : Num -> Num -> Num @
  | TCMul                 -- ^ @ : Num -> Num -> Num @
  | TCDiv                 -- ^ @ : Num -> Num -> Num @
  | TCMod                 -- ^ @ : Num -> Num -> Num @
  | TCExp                 -- ^ @ : Num -> Num -> Num @
  | TCWidth               -- ^ @ : Num -> Num @
  | TCMin                 -- ^ @ : Num -> Num -> Num @
  | TCMax                 -- ^ @ : Num -> Num -> Num @
  | TCCeilDiv             -- ^ @ : Num -> Num -> Num @
  | TCCeilMod             -- ^ @ : Num -> Num -> Num @

  -- Computing the lengths of explicit enumerations
  | TCLenFromThen         -- ^ @ : Num -> Num -> Num -> Num@
    -- Example: @[ 1, 5 .. ] :: [lengthFromThen 1 5 b][b]@

  | TCLenFromThenTo       -- ^ @ : Num -> Num -> Num -> Num@
    -- Example: @[ 1, 5 .. 9 ] :: [lengthFromThenTo 1 5 9][b]@

    deriving (Show, Eq, Ord, Bounded, Enum, Generic, NFData)

tBinOpPrec :: Map.Map TFun (Assoc,Int)
tBinOpPrec  = mkMap t_table
  where
  mkMap t = Map.fromList [ (op,(a,n)) | ((a,ops),n) <- zip t [1..] , op <- ops ]

  -- lowest to highest
  t_table =
    [ (LeftAssoc,   [ TCAdd, TCSub ])
    , (LeftAssoc,   [ TCMul, TCDiv, TCMod, TCCeilDiv, TCCeilMod ])
    , (RightAssoc,  [ TCExp ])
    ]

-- | Type functions, with their arity and function constructor.
tfunNames :: Map.Map PName (Int,TFun)
tfunNames  = Map.fromList
  [ tinfix  "+"                2 TCAdd
  , tinfix  "-"                2 TCSub
  , tinfix  "*"                2 TCMul
  , tinfix  "/"                2 TCDiv
  , tinfix  "%"                2 TCMod
  , tinfix  "^^"               2 TCExp
  , tprefix "width"            1 TCWidth
  , tprefix "min"              2 TCMin
  , tprefix "max"              2 TCMax
  , tprefix "/^"               2 TCCeilDiv
  , tprefix "%^"               2 TCCeilMod
  , tprefix "lengthFromThen"   3 TCLenFromThen
  , tprefix "lengthFromThenTo" 3 TCLenFromThenTo
  ]
  where

  tprefix n a p = (mkUnqual (packIdent n), (a,p))
  tinfix  n a p = (mkUnqual (packInfix n), (a,p))

instance PPName TFun where
  ppNameFixity f = Map.lookup f tBinOpPrec

  ppPrefixName TCAdd     = text "(+)"
  ppPrefixName TCSub     = text "(-)"
  ppPrefixName TCMul     = text "(*)"
  ppPrefixName TCDiv     = text "(/)"
  ppPrefixName TCMod     = text "(%)"
  ppPrefixName TCExp     = text "(^^)"
  ppPrefixName TCCeilDiv = text "(/^)"
  ppPrefixName TCCeilMod = text "(%^)"
  ppPrefixName f         = pp f

  ppInfixName TCAdd     = text "+"
  ppInfixName TCSub     = text "-"
  ppInfixName TCMul     = text "*"
  ppInfixName TCDiv     = text "/"
  ppInfixName TCMod     = text "%"
  ppInfixName TCExp     = text "^^"
  ppInfixName TCCeilDiv = text "/^"
  ppInfixName TCCeilMod = text "%^"
  ppInfixName f         = error $ "Not a prefix type function: " ++ show (pp f)

instance PP TFun where
  ppPrec _ tcon =
    case tcon of
      TCAdd             -> text "+"
      TCSub             -> text "-"
      TCMul             -> text "*"
      TCDiv             -> text "/"
      TCMod             -> text "%"
      TCExp             -> text "^^"
      TCWidth           -> text "width"
      TCMin             -> text "min"
      TCMax             -> text "max"
      TCCeilDiv         -> text "/^"
      TCCeilMod         -> text "%^"

      TCLenFromThen     -> text "lengthFromThen"
      TCLenFromThenTo   -> text "lengthFromThenTo"
