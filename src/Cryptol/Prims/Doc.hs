-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

module Cryptol.Prims.Doc
  ( helpDoc
  , description
  ) where

import Cryptol.Prims.Syntax
import Cryptol.Prims.Types(typeOf)
import Cryptol.Utils.PP

helpDoc :: ECon -> Doc
helpDoc prim =
  vcat [ text "Description"
       , text "-----------"
       , text ""
       , text "    "
                   <> ppPrefix prim <+> text ":" <+> pp ty
       , text ""
       , description prim
       ]
  where ty = typeOf prim

method :: String -> [Doc] -> [String] -> Doc
method txt _is notes =
  hang (text txt) 2 (vcat [ text "*" <+> text i | i <- notes ])
  -- XXX: Display what instances are supported.

noDoc :: Doc
noDoc = text "No documentation is available."

dBits, dWords, dSeqs, dTuples, dRecords, dFuns, dFinSeqs :: Doc
dCmps, dAriths, dEverything :: [Doc]
dBits       = text "bits"
dWords      = text "words"
dSeqs       = text "sequences"
dFinSeqs    = text "finite sequences"
dTuples     = text "tuples"
dRecords    = text "records"
dFuns       = text "functions"
dCmps       = [ dBits, dWords, dSeqs, dTuples, dRecords ]
dAriths     = [ dWords, dSeqs, dTuples, dRecords, dFuns ]
dEverything = [ dBits, dWords, dSeqs, dTuples, dRecords, dFuns ]

description :: ECon -> Doc
description prim =
  case prim of
    ECTrue    -> text "The constant True. Corresponds to the bit value 1."
    ECFalse   -> text "The constant False. Corresponds to the bit value 0."

    ECDemote  -> text "The value corresponding to a numeric type."

    ECPlus    -> method "Add two values."
                    dAriths
                    [ "For words, addition uses modulo arithmetic."
                    , "Structured values are added element-wise."
                    ]

    ECMinus           -> method "Infix subtraction."
                    dAriths
                    [ "For words, subtraction uses modulo arithmetic."
                    , "Structured values are subtracted element-wise. Defined as:"
                    , "a - b = a + negate b"
                    , "See also: `negate'."
                    ]
    ECMul             -> method "Multiplies two values."
                    dAriths
                    [ "For words, multiplies two words, modulus 2^^a."
                    , "Structured values are multiplied element-wise."
                    ]
    ECDiv             -> method "Divides two values."
                    dAriths
                    [ "For words, divides two words, modulus 2^^a."
                    , "Structured values are divided element-wise."
                    ]
    ECMod             -> method "Infix modulus."
                    dAriths
                    [ "For words, takes the modulus of two words, modulus 2^^a."
                    , "Over structured values, operates element-wise."
                    , "Be careful, as this will often give unexpected results due to interaction of the two moduli."
                    ]
    ECExp             -> method "Exponentiation."
                    dAriths
                    [ "For words, takes the exponent of two words, modulus 2^^a."
                    , "Over structured values, operates element-wise."
                    , "Be careful, due to its fast-growing nature, exponentiation is prone to interacting poorly with defaulting."
                    ]
    ECLg2             -> method "Log base two"
                    dAriths
                    [ "For words, computes the ceiling of log, base 2, of a number."
                    , "Over structured values, operates element-wise."
                    ]
    ECNeg             -> method "Unary negation"
                    dAriths
                    [ "Returns the twos complement of its argument."
                    , "Over structured values, operates element-wise."
                    , "negate a = ~a + 1" -- is this right?
                    ]
    ECLt              -> method "Less than comparison"
                    dCmps 
                    [ "Less-than. Only works on comparable arguments." ]
    ECGt              -> method "Greater than comparison"
                    dCmps
                    [ "Greater-than of two comparable arguments." ]
    ECLtEq            -> method "Less than or equal comparison"
                    dCmps
                    [ "Less-than or equal of two comparable arguments." ]
    ECGtEq            -> method "Greater than or equal comparison"
                    dCmps
                    [ "Greater-than or equal of two comparable arguments." ]
    ECEq              -> method "Equality test"
                    dEverything
                    [ "Compares any two values of the same type for equality." ]
    ECNotEq           -> method "Not-equals test"
                    dEverything
                    [ "Compares any two values of the same type for inequality." ]

    ECFunEq           -> noDoc
    ECFunNotEq        -> noDoc
    ECMin             -> method "Minimum of two arguments"
                    dCmps
                    [ "Returns the smaller of two comparable arguments." ]
    ECMax             -> method "Maximum of two arguments"
                    dCmps
                    [ "Returns the greater of two comparable arguments." ]

    ECAnd             -> method "Logical and"
                    dEverything
                    [ "Logical `and' over bits. Extends element-wise over sequences, tuples." ]
    ECOr              -> method "Logical or"
                    dEverything
                    [ "Logical `or' over bits. Extends element-wise over sequences, tuples." ]
    ECXor             -> method "Logical exclusive-or"
                    dEverything
                    [ "Logical `exclusive or' over bits. Extends element-wise over sequences, tuples." ]
    ECCompl           -> method "Logical complement"
                    dEverything
                    [ "Bitwise complement. Extends element-wise over sequences, tuples." ]
    ECZero            -> method "Polymorphic zero"
                    dEverything -- uh, no arguments?
                    [ "Gives an arbitrary shaped value whose bits are all False."
                    , "~zero likewise gives an arbitrary shaped value whose bits are all True."
                    ]

    ECShiftL          -> method "Left shift"
                    [ dFinSeqs ]
                    [ "Left shift.  The first argument is the sequence to shift, the second is the number of positions to shift by."  ]
    ECShiftR          -> method "Right shift"
                    [ dFinSeqs ]
                    [ "Right shift.  The first argument is the sequence to shift, the second is the number of positions to shift by."  ]
    ECRotL            -> method "Left rotate"
                    [ dFinSeqs ]
                    [ "Left rotate.  The first argument is the sequence to rotate, the second is the number of positions to rotate by."  ]
    ECRotR            -> method "Right rotate"
                    [ dFinSeqs ]
                    [ "Right rotate.  The first argument is the sequence to rotate, the second is the number of positions to rotate by."  ]

    ECCat             -> noDoc
    ECSplitAt         -> method "Two-way split operator"
                    [ dSeqs ]
                    [ "Split a sequence into a tuple of sequences" ]
    ECJoin            -> method "Join sequences"
                    [ dSeqs ]
                    [ "Joins sequences" ]
    ECSplit           -> method "Polymorphic split operator"
                    [ dSeqs ]
                    [ "Splits a sequence into 'parts' groups with 'each' elements." ]
    ECReverse         -> method "Reverse a sequence"
                    [ dSeqs ]
                    [ "Reverses the elements in a sequence." ]
    ECTranspose       -> method "Matrix transposition"
                    [ dSeqs ]
                    [ "Transposes an [a][b] matrix into a [b][a] matrix." ]

    ECAt              -> method "Index select operator"
                    [ dSeqs ]
                    [ "Index operator.  The first argument is a sequence."
                      ,"The second argument is the zero-based index of the element to select from the sequence."
                    ]
    ECAtRange         -> method "Bulk index operator"
                    [ dSeqs ]
                    [ "Bulk index operator.  The first argument is a sequence."
                      ,"The second argument is a sequence of the zero-based indices of the elements to select."
                    ]
    ECAtBack          -> method "Reverse index select operator"
                    [ dFinSeqs ]
                    [ "Reverse index operator.  The first argument is a finite sequence."
                      ,"The second argument is the zero-based index of the element to select, starting from the end of the sequence."
                    ]
    ECAtRangeBack     -> method "Bulk reverse index operator"
                    [ dFinSeqs ]
                    [ "Bulk reverse index operator.  The first argument is a finite sequence."
                      ,"The second argument is a sequence of the zero-based indices of the elements to select, starting from the end of the sequence."
                    ]

    ECFromThen        -> noDoc
    ECFromTo          -> noDoc
    ECFromThenTo      -> noDoc

    ECInfFrom         -> noDoc
    ECInfFromThen     -> noDoc

    ECError           -> noDoc

    ECPMul            -> method "Polynomial multiplication"
                    [ dWords ]
                    [ "Performs multiplication of GF2^^8 polynomials." ]
    ECPDiv            -> method "Polynomial division"
                    [ dWords ]
                    [ "Performs division of GF2^^8 polynomials." ]
    ECPMod            -> method "Polynomial modulus"
                    [ dWords ]
                    [ "Performs modulus of GF2^^8 polynomials." ]

    ECRandom          -> method "Random value generation"
                    dCmps
                    [ "Generates random values from a seed."
                      ,"When called with a function, currently generates a function that always returns zero."
                    ]
