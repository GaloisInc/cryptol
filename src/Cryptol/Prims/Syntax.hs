-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

module Cryptol.Prims.Syntax
  ( TFun(..)
  , ECon(..)
  , eBinOpPrec
  , tBinOpPrec
  , ppPrefix

  , primNames
  ) where

import           Cryptol.ModuleSystem.Name (QName,Name(Name),mkUnqual)
import           Cryptol.Utils.PP
import           Cryptol.Utils.Panic (panic)
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



-- | Built-in constants.
data ECon

  = ECTrue
  | ECFalse

  | ECDemote -- ^ Converts a numeric type into its corresponding value.

  -- Arith
  | ECPlus | ECMinus | ECMul | ECDiv | ECMod
  | ECExp | ECLg2 | ECNeg

  -- Cmp
  | ECLt | ECGt | ECLtEq | ECGtEq | ECEq | ECNotEq
  | ECFunEq | ECFunNotEq
  | ECMin | ECMax

  -- Logic
  | ECAnd | ECOr | ECXor | ECCompl | ECZero
  | ECShiftL | ECShiftR | ECRotL | ECRotR

  -- Sequences
  | ECCat  | ECSplitAt
  | ECJoin | ECSplit
  | ECReverse | ECTranspose

  | ECAt | ECAtRange | ECAtBack | ECAtRangeBack

  -- Static word sequences
  | ECFromThen | ECFromTo | ECFromThenTo

  -- Infinite word sequences
  | ECInfFrom | ECInfFromThen

  -- Run-time error
  | ECError

  -- Polynomials
  | ECPMul | ECPDiv | ECPMod

  -- Random values
  | ECRandom
    deriving (Eq,Ord,Show,Bounded,Enum)


eBinOpPrec :: Map.Map ECon  (Assoc,Int)
tBinOpPrec :: Map.Map TFun  (Assoc,Int)

(eBinOpPrec, tBinOpPrec) = (mkMap e_table, mkMap t_table)
  where
  mkMap t = Map.fromList [ (op,(a,n)) | ((a,ops),n) <- zip t [0..] , op <- ops ]

  -- lowest to highest
  e_table =
    [ (LeftAssoc,  [ ECOr  ])
    , (LeftAssoc,  [ ECXor ])
    , (LeftAssoc,  [ ECAnd ])

    , (NonAssoc,   [ ECEq, ECNotEq, ECFunEq, ECFunNotEq ])
    , (NonAssoc,   [ ECLt, ECGt, ECLtEq, ECGtEq ])

    , (RightAssoc, [ ECCat ])
    , (LeftAssoc,  [ ECShiftL, ECShiftR, ECRotL, ECRotR ])

    , (LeftAssoc,  [ ECPlus, ECMinus ])
    , (LeftAssoc,  [ ECMul, ECDiv, ECMod ])
    , (RightAssoc, [ ECExp ])

    , (LeftAssoc,  [ ECAt, ECAtRange, ECAtBack, ECAtRangeBack ])
    ]

  t_table =
    [ (LeftAssoc,   [ TCAdd, TCSub ])
    , (LeftAssoc,   [ TCMul, TCDiv, TCMod ])
    , (RightAssoc,  [ TCExp ])
    ]


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


primNames :: Map.Map QName ECon
primDocs  :: Map.Map ECon  QName

(primNames,primDocs) = (Map.fromList prims, Map.fromList (map swap prims))
  where
  swap (a,b) = (b,a)

  prim ec n = (mkUnqual (Name n), ec)

  prims =
    [ prim ECTrue        "True"
    , prim ECFalse       "False"
    , prim ECPlus        "+"
    , prim ECMinus       "-"
    , prim ECMul         "*"
    , prim ECDiv         "/"
    , prim ECMod         "%"
    , prim ECExp         "^^"
    , prim ECLg2         "lg2"
    , prim ECLt          "<"
    , prim ECGt          ">"
    , prim ECLtEq        "<="
    , prim ECGtEq        ">="
    , prim ECEq          "=="
    , prim ECNotEq       "!="
    , prim ECFunEq       "==="
    , prim ECFunNotEq    "!=="
    , prim ECAnd         "&&"
    , prim ECOr          "||"
    , prim ECXor         "^"
    , prim ECCompl       "~"
    , prim ECShiftL      "<<"
    , prim ECShiftR      ">>"
    , prim ECRotL        "<<<"
    , prim ECRotR        ">>>"
    , prim ECCat         "#"
    , prim ECAt          "@"
    , prim ECAtRange     "@@"
    , prim ECAtBack      "!"
    , prim ECAtRangeBack "!!"
    , prim ECMin         "min"
    , prim ECMax         "max"

    , prim ECSplitAt     "splitAt"
    , prim ECZero        "zero"
    , prim ECJoin        "join"
    , prim ECSplit       "split"
    , prim ECReverse     "reverse"
    , prim ECTranspose   "transpose"

    , prim ECDemote      "demote"

    , prim ECFromThen    "fromThen"
    , prim ECFromTo      "fromTo"
    , prim ECFromThenTo  "fromThenTo"

    , prim ECInfFrom     "infFrom"
    , prim ECInfFromThen "infFromThen"

    , prim ECError       "error"

    , prim ECPMul        "pmult"
    , prim ECPDiv        "pdiv"
    , prim ECPMod        "pmod"

    , prim ECRandom      "random"
    ]


instance PP ECon where
  ppPrec _ ECNeg = text "-"
  ppPrec _ con   = pp (Map.findWithDefault err con primDocs)
    where
    err = panic "Cryptol.Prims.Syntax" [ "Primitive missing from name map"
                                       , show con ]

ppPrefix :: ECon -> Doc
ppPrefix con = optParens (Map.member con eBinOpPrec) (pp con)


