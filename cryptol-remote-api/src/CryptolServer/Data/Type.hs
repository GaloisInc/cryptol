{-# LANGUAGE OverloadedStrings #-}
module CryptolServer.Data.Type
  ( JSONSchema(..)
  , JSONType(..)
  ) where

import qualified Data.Aeson as JSON
import Data.Aeson ((.=))
import qualified Data.Text as T

import Cryptol.Parser.Selector (ppSelector)
import Cryptol.TypeCheck.PP (NameMap, emptyNameMap, ppWithNames)
import Cryptol.TypeCheck.Type (Kind(..), PC(..), TC(..), TCon(..), TFun(..), TParam(..), Type(..), Schema(..), addTNames, kindOf)
import Cryptol.Utils.PP (pp)
import Cryptol.Utils.RecordMap (canonicalFields)


newtype JSONSchema = JSONSchema Schema

data JSONType = JSONType NameMap Type

newtype JSONKind = JSONKind Kind

instance JSON.ToJSON JSONSchema where
  toJSON (JSONSchema (Forall vars props ty)) =
    let ns = addTNames vars emptyNameMap
    in JSON.object [ "forall" .=
                      [JSON.object
                        [ "name" .= show (ppWithNames ns v)
                        , "kind" .= JSONKind (kindOf v)
                        ]
                      | v@(TParam _uniq _k _flav _info) <- vars
                      ]
                     , "propositions" .= map (JSON.toJSON . JSONType ns) props
                     , "type" .= JSONType ns ty
                     ]

instance JSON.ToJSON JSONKind where
  toJSON (JSONKind k) = convert k
    where
      convert KType = "Type"
      convert KNum = "Num"
      convert KProp = "Prop"
      convert (k1 :-> k2) =
        JSON.object [ "kind" .= T.pack "arrow"
                    , "from" .= convert k1
                    , "to" .= convert k2
                    ]

instance JSON.ToJSON JSONType where
  toJSON (JSONType ns t) = convert t
    where
      convert (TCon (TError _ _) _) =
        -- TODO: figure out what to do in this situation
        error "JSON conversion of errors is not yet supported"
      convert (TCon (TC tc) args) =
        JSON.object $
        case (tc, args) of
          (TCNum n, []) ->
            [ "type" .= T.pack "number" , "value" .= n ]
          (TCInf, []) -> ["type" .= T.pack "inf"]
          (TCBit, []) -> ["type" .= T.pack "Bit"]
          (TCInteger, []) -> ["type" .= T.pack "Integer"]
          (TCIntMod, [n]) -> [ "type" .= T.pack "Z"
                             , "modulus" .= JSONType ns n
                             ]
          (TCSeq, [t1, TCon (TC TCBit) []]) ->
            [ "type" .= T.pack "bitvector"
            , "width" .= JSONType ns t1
            ]
          (TCSeq, [t1, t2]) ->
            [ "type" .= T.pack "sequence"
            , "length" .= JSONType ns t1
            , "contents" .= JSONType ns t2
            ]
          (TCFun, [t1, t2]) ->
            [ "type" .= T.pack "function"
            , "domain" .= JSONType ns t1
            , "range" .= JSONType ns t2
            ]
          (TCTuple _ , []) ->
            [ "type" .= T.pack "unit" ]
          (TCTuple _, fs) ->
            [ "type" .= T.pack "tuple"
            , "contents" .= map (JSONType ns) fs
            ]
          (TCRational, []) ->
            [ "type" .= T.pack "Rational"]
          (other, otherArgs) ->
            [ "type" .= T.pack "unknown"
            , "constructor" .= show other
            , "arguments" .= show otherArgs
            ]
      convert (TCon (TF tf) args) =
        JSON.object
        [ "type" .= T.pack t'
        , "arguments" .= map (JSONType ns) args
        ]
        where
          t' =
            case tf of
              TCAdd -> "+"
              TCSub -> "-"
              TCMul -> "*"
              TCDiv -> "/"
              TCMod -> "%"
              TCExp -> "^^"
              TCWidth -> "width"
              TCMin -> "min"
              TCMax -> "max"
              TCCeilDiv -> "/^"
              TCCeilMod -> "%^"
              TCLenFromThenTo -> "lengthFromThenTo"
      convert (TCon (PC pc) args) =
        JSON.object $
        case (pc, args) of
          (PEqual, [t1, t2]) ->
            [ "prop" .= T.pack "=="
            , "left" .= JSONType ns t1
            , "right" .= JSONType ns t2
            ]
          (PNeq, [t1, t2]) ->
            [ "prop" .= T.pack "!="
            , "left" .= JSONType ns t1
            , "right" .= JSONType ns t2
            ]
          (PGeq, [t1, t2]) ->
            [ "prop" .= T.pack ">="
            , "greater" .= JSONType ns t1
            , "less" .= JSONType ns t2
            ]
          (PFin, [t']) ->
            [ "prop" .= T.pack "fin"
            , "subject" .= JSONType ns t'
            ]
          (PHas x, [t1, t2]) ->
            [ "prop" .= T.pack "has"
            , "selector" .= show (ppSelector x)
            , "type" .= JSONType ns t1
            , "is"   .= JSONType ns t2
            ]
          (PRing, [t']) ->
            [ "prop" .= T.pack "Ring"
            , "subject" .= JSONType ns t'
            ]
          (PField, [t']) ->
            [ "prop" .= T.pack "Field"
            , "subject" .= JSONType ns t'
            ]
          (PRound, [t']) ->
            [ "prop" .= T.pack "Round"
            , "subject" .= JSONType ns t'
            ]
          (PIntegral, [t']) ->
            [ "prop" .= T.pack "Integral"
            , "subject" .= JSONType ns t'
            ]
          (PCmp, [t']) ->
            [ "prop" .= T.pack "Cmp"
            , "subject" .= JSONType ns t'
            ]
          (PSignedCmp, [t']) ->
            [ "prop" .= T.pack "SignedCmp"
            , "subject" .= JSONType ns t'
            ]
          (PLiteral, [t1, t2]) ->
            [ "prop" .= T.pack "Literal"
            , "size" .= JSONType ns t1
            , "subject" .= JSONType ns t2
            ]
          (PZero, [t']) ->
            [ "prop" .= T.pack "Zero"
            , "subject" .= JSONType ns t'
            ]
          (PLogic, [t']) ->
            [ "prop" .= T.pack "Logic"
            , "subject" .= JSONType ns t'
            ]
          (PTrue, []) ->
            [ "prop" .= T.pack "True"
            ]
          (PAnd, [t1, t2]) ->
            [ "prop" .= T.pack "And"
            , "left" .= JSONType ns t1
            , "right" .= JSONType ns t2
            ]
          (pc', args') ->
            [ "prop" .= T.pack "unknown"
            , "constructor" .= show pc'
            , "arguments" .= show args'
            ]
      convert (TVar v) =
        JSON.object
        [ "type" .= T.pack "variable"
        , "kind" .= JSONKind (kindOf v)
        , "name" .= show (ppWithNames ns v)
        ]
      convert (TUser _n _args def) = convert def
      convert (TRec fields) =
        JSON.object
        [ "type" .= T.pack "record"
        , "fields" .=
          JSON.object [ T.pack (show (pp f)) .= JSONType ns t'
                      | (f, t') <- canonicalFields fields
                      ]
        ]
