{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-missing-deriving-strategies #-}
module CryptolServer.Data.Type
  ( JSONSchema(..)
  , JSONType(..)
  , JSONPType(..)
  ) where

import qualified Data.Aeson as JSON
import Data.Aeson ((.=), (.:), (.!=), (.:?))
import Data.Aeson.Types (Parser, typeMismatch)
import Data.Functor ((<&>))
import qualified Data.Text as T

import qualified Cryptol.Parser.AST as C
import Cryptol.Parser.Position (emptyRange)
import Cryptol.Parser.Selector (ppSelector)
import Cryptol.Utils.RecordMap (recordFromFields)
import Cryptol.TypeCheck.PP (NameMap, emptyNameMap, ppWithNames)
import Cryptol.TypeCheck.Type (Kind(..), PC(..), TC(..), TCon(..), TFun(..), TParam(..), Type(..), Schema(..), addTNames, kindOf)
import Cryptol.Utils.Ident (mkIdent)
import Cryptol.Utils.PP (pp)
import Cryptol.Utils.RecordMap (canonicalFields)

import qualified Argo.Doc as Doc
import CryptolServer.AesonCompat


newtype JSONSchema = JSONSchema Schema

newtype JSONPType = JSONPType { unJSONPType :: C.Type C.PName }

data JSONType = JSONType NameMap Type
  deriving (Eq, Show)

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
      convert (TCon (TError {}) _) =
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
            , "arguments" .= map (JSONType ns) otherArgs
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
            , "arguments" .= map (JSONType ns) args'
            ]
      convert (TVar v) =
        JSON.object
        [ "type" .= T.pack "variable"
        , "kind" .= JSONKind (kindOf v)
        , "name" .= show (ppWithNames ns v)
        ]
      convert (TUser _n _args def) = convert def
      convert (TNewtype _nt _ts) =
        JSON.object [ "type" .= T.pack "newtype" ]
      convert (TRec fields) =
        JSON.object
        [ "type" .= T.pack "record"
        , "fields" .=
          JSON.object [ keyFromText (T.pack (show (pp f))) .= JSONType ns t'
                      | (f, t') <- canonicalFields fields
                      ]
        ]


instance JSON.FromJSON JSONPType where
  parseJSON val = JSONPType <$> getType val

    where
      getType :: JSON.Value -> Parser (C.Type C.PName)
      getType (JSON.Object o) =
            case lookupKM "type" o of
              Just t -> asType t o
              Nothing ->
                case lookupKM "prop" o of
                  Just p -> asProp p o
                  Nothing -> fail "Expected type or prop key"
      getType other = typeMismatch "object" other

      asType "record" = \o -> C.TRecord <$> ((o .: "fields") >>= getFields)
        where
          getFields obj = recordFromFields <$> traverse (\(k, v) -> (mkIdent (keyToText k),) . (emptyRange,) <$> getType v) (toListKM obj)
      asType "variable" = \o -> C.TUser <$> (name <$> o .: "name") <*> (map unJSONPType <$> (o .:? "arguments" .!= []))
      asType "number" = \o -> C.TNum <$> (o .: "value")
      asType "inf" = const $ pure $ C.TUser (name "inf") []
      asType "Bit" = const $ pure $ C.TBit
      asType "Integer" = const $ pure $ C.TUser (name "Integer") []
      asType "Z" = \o -> typeField o "modulus" <&> \m -> C.TUser (name "Z") [m]
      asType "bitvector" = \o -> typeField o "width" <&> \w -> C.TSeq w C.TBit
      asType "sequence" = binTC C.TSeq "length" "contents"
      asType "function" = binTC C.TFun "domain" "range"
      asType "unit" = const $ pure $ C.TTuple []
      asType "tuple" = \o -> C.TTuple <$> typeListField o "contents"
      asType "Rational" = const $ pure $ C.TUser (name "Rational") []
      asType "+" = tyFun "+"
      asType "-" = tyFun "-"
      asType "*" = tyFun "*"
      asType "/" = tyFun "/"
      asType "%" = tyFun "%"
      asType "^^" = tyFun "^^"
      asType "width" = tyFun "width"
      asType "min" = tyFun "min"
      asType "max" = tyFun "max"
      asType "/^" = tyFun "/^"
      asType "%^" = tyFun "%^"
      asType "lengthFromThenTo" = tyFun "lengthFromThenTo"
      asType other = const $ fail $ "Didn't understand type tag " <> show other

      typeField o fname = (o .: fname) >>= getType
      typeListField o fname = (o .: fname) >>= traverse getType

      name = C.UnQual . mkIdent

      asProp "==" = binPropF "==" "left" "right"
      asProp "!=" = binPropF "!=" "left" "right"
      asProp ">=" = binPropF ">=" "left" "right"
      asProp "fin" = unaryPropF "fin" "subject"
      asProp "Ring" = unaryPropF "Ring" "subject"
      asProp "Field" = unaryPropF "Field" "subject"
      asProp "Round" = unaryPropF "Round" "subject"
      asProp "Integral" = unaryPropF "Integral" "subject"
      asProp "Cmp" = unaryPropF "Cmp" "subject"
      asProp "SignedCmp" = unaryPropF "SignedCmp" "subject"
      asProp "Literal" = binPropF "Literal" "size" "subject"
      asProp "Zero" = unaryPropF "Zero" "subject"
      asProp "Logic" = unaryPropF "Logic" "subject"
      asProp "True" = const $ pure $ C.TUser (name "True") []
      asProp "And" = binPropF "And" "left" "right"
      asProp other = const $ fail $ "Didn't understand proposition " ++ show other

      binProp prop a b = C.TUser (name prop) [a, b]
      binPropF prop f1 f2 o = binProp prop <$> typeField o f1 <*> typeField o f2
      unaryProp prop a = C.TUser (name prop) [a]
      unaryPropF prop f o = unaryProp prop <$> typeField o f
      binTC tc f1 f2 o = tc <$> typeField o f1 <*> typeField o f2
      tyFun tf o = C.TUser (name tf) <$> typeListField o "arguments"

instance Doc.Described JSONSchema where
  typeName = "JSON Cryptol Types"
  description =
    [ Doc.Paragraph [Doc.Text "JSON representations of types are type schemas. A type schema has three fields:"]
    , Doc.DescriptionList
        [ (pure $ Doc.Literal "forall",
           Doc.Paragraph [ Doc.Text "Contains an array of objects. Each object has two fields: "
                         , Doc.Literal "name", Doc.Text " is the name of a type variable, and "
                         , Doc.Literal "kind", Doc.Text " is its kind. There are four kind formers: the string "
                         , Doc.Literal "Type", Doc.Text " represents ordinary datatypes, the string "
                         , Doc.Literal "Num", Doc.Text " is the kind of numbers, and "
                         , Doc.Literal "Prop", Doc.Text " is the kind of propositions. "
                         , Doc.Text "Arrow kinds are represented by objects in which the field "
                         , Doc.Literal "kind", Doc.Text " is the string "
                         , Doc.Literal "arrow", Doc.Text ", and the fields "
                         , Doc.Literal "from", Doc.Text " and ", Doc.Literal "to"
                         , Doc.Text " are the kinds on the left and right side of the arrow, respectively."
                         ])
        , (pure $ Doc.Literal "propositions",
           Doc.Paragraph [Doc.Text "A JSON array of the constraints in the type."])
        , (pure $ Doc.Literal "type",
           Doc.Paragraph [ Doc.Text "The type in which the variables from "
                         , Doc.Literal "forall", Doc.Text " are in scope and the constraints in "
                         , Doc.Literal "propositions", Doc.Text " are in effect."
                         ])
        ]
    ]
