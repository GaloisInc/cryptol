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
  ) where

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



instance PP ECon where
  ppPrec _ con =
    case con of
      ECTrue        -> text "True"
      ECFalse       -> text "False"
      ECPlus        -> text "+"
      ECMinus       -> text "-"
      ECMul         -> text "*"
      ECDiv         -> text "/"
      ECMod         -> text "%"
      ECExp         -> text "^^"
      ECLg2         -> text "lg2"
      ECNeg         -> text "-"
      ECLt          -> text "<"
      ECGt          -> text ">"
      ECLtEq        -> text "<="
      ECGtEq        -> text ">="
      ECEq          -> text "=="
      ECNotEq       -> text "!="
      ECFunEq       -> text "==="
      ECFunNotEq    -> text "!=="
      ECAnd         -> text "&&"
      ECOr          -> text "||"
      ECXor         -> text "^"
      ECCompl       -> text "~"
      ECShiftL      -> text "<<"
      ECShiftR      -> text ">>"
      ECRotL        -> text "<<<"
      ECRotR        -> text ">>>"
      ECCat         -> text "#"
      ECAt          -> text "@"
      ECAtRange     -> text "@@"
      ECAtBack      -> text "!"
      ECAtRangeBack -> text "!!"
      ECMin         -> text "min"
      ECMax         -> text "max"

      ECSplitAt     -> text "splitAt"
      ECZero        -> text "zero"
      ECJoin        -> text "join"
      ECSplit       -> text "split"
      ECReverse     -> text "reverse"
      ECTranspose   -> text "transpose"

      ECDemote      -> text "demote"

      ECFromThen    -> text "fromThen"
      ECFromTo      -> text "fromTo"
      ECFromThenTo  -> text "fromThenTo"

      ECInfFrom     -> text "infFrom"
      ECInfFromThen -> text "infFromThen"

      ECError       -> text "error"

      ECPMul        -> text "pmult"
      ECPDiv        -> text "pdiv"
      ECPMod        -> text "pmod"

      ECRandom      -> text "random"

ppPrefix :: ECon -> Doc
ppPrefix con = optParens (Map.member con eBinOpPrec) (pp con)


