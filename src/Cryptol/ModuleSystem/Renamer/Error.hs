-- |
-- Module      :  Cryptol.ModuleSystem.Renamer
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# Language DeriveGeneric, DeriveAnyClass #-}
{-# Language OverloadedStrings #-}
module Cryptol.ModuleSystem.Renamer.Error where

import Cryptol.ModuleSystem.Name
import Cryptol.Parser.AST
import Cryptol.Parser.Position
import Cryptol.Parser.Selector(ppNestedSels)
import Cryptol.Utils.PP

import GHC.Generics (Generic)
import Control.DeepSeq

import Prelude ()
import Prelude.Compat

-- Errors ----------------------------------------------------------------------

data RenamerError
  = MultipleSyms (Located PName) [Name]
    -- ^ Multiple imported symbols contain this name

  | UnboundName Namespace (Located PName)
    -- ^ Some name not bound to any definition

  | OverlappingSyms [Name]
    -- ^ An environment has produced multiple overlapping symbols

  | WrongNamespace Namespace Namespace (Located PName)
    -- ^ expected, actual.
    -- When a name is missing from the expected namespace, but exists in another

  | FixityError (Located Name) Fixity (Located Name) Fixity
    -- ^ When the fixity of two operators conflict

  | InvalidConstraint (Type PName)
    -- ^ When it's not possible to produce a Prop from a Type.

  | MalformedBuiltin (Type PName) PName
    -- ^ When a builtin type/type-function is used incorrectly.

  | BoundReservedType PName (Maybe Range) Doc
    -- ^ When a builtin type is named in a binder.

  | OverlappingRecordUpdate (Located [Selector]) (Located [Selector])
    -- ^ When record updates overlap (e.g., @{ r | x = e1, x.y = e2 }@)

  | InvalidDependency [DepName]
    deriving (Show, Generic, NFData)


-- We use this because parameter constrstaints have no names
data DepName = NamedThing Name
             | ModParamName Range (Maybe ModName)
             | ConstratintAt Range -- ^ identifed by location in source
               deriving (Eq,Ord,Show,Generic,NFData)

depNameLoc :: DepName -> Range
depNameLoc x =
  case x of
    NamedThing n -> nameLoc n
    ConstratintAt r -> r
    ModParamName r _ -> r


instance PP RenamerError where
  ppPrec _ e = case e of

    MultipleSyms lqn qns ->
      hang (text "[error] at" <+> pp (srcRange lqn))
         4 $ (text "Multiple definitions for symbol:" <+> pp (thing lqn))
          $$ vcat (map ppLocName qns)

    UnboundName ns lqn ->
      hang (text "[error] at" <+> pp (srcRange lqn))
         4 (something <+> "not in scope:" <+> pp (thing lqn))
      where
      something = case ns of
                    NSValue   -> "Value"
                    NSType    -> "Type"
                    NSModule  -> "Module"
                    NSSignature -> "Signature"

    OverlappingSyms qns ->
      hang (text "[error]")
         4 $ text "Overlapping symbols defined:"
          $$ vcat (map ppLocName qns)

    WrongNamespace expected actual lqn ->
      hang ("[error] at" <+> pp (srcRange lqn ))
         4 (fsep $
            [ "Expected a", sayNS expected, "named", quotes (pp (thing lqn))
            , "but found a", sayNS actual, "instead"
            ] ++ suggestion)
        where
        sayNS ns = case ns of
                     NSValue  -> "value"
                     NSType   -> "type"
                     NSModule -> "module"
                     NSSignature -> "signature"
        suggestion =
          case (expected,actual) of

            (NSValue,NSType) ->
                ["Did you mean `(" <.> pp (thing lqn) <.> text")?"]
            _ -> []

    FixityError o1 f1 o2 f2 ->
      hang (text "[error] at" <+> pp (srcRange o1) <+> text "and" <+> pp (srcRange o2))
         4 (vsep [ text "The fixities of"
                 , indent 2 $ vcat
                   [ "•" <+> pp (thing o1) <+> parens (pp f1)
                   , "•" <+> pp (thing o2) <+> parens (pp f2) ]
                 , text "are not compatible."
                 , text "You may use explicit parentheses to disambiguate." ])

    InvalidConstraint ty ->
      hang (hsep $ [text "[error]"] ++ maybe [] (\r -> [text "at" <+> pp r]) (getLoc ty))
         4 (fsep [ pp ty, text "is not a valid constraint" ])

    MalformedBuiltin ty pn ->
      hang (hsep $ [text "[error]"] ++ maybe [] (\r -> [text "at" <+> pp r]) (getLoc ty))
         4 (fsep [ text "invalid use of built-in type", pp pn
                 , text "in type", pp ty ])

    BoundReservedType n loc src ->
      hang (hsep $ [text "[error]"] ++ maybe [] (\r -> [text "at" <+> pp r]) loc)
         4 (fsep [ text "built-in type", quotes (pp n), text "shadowed in", src ])

    OverlappingRecordUpdate xs ys ->
      hang "[error] Overlapping record updates:"
         4 (vcat [ ppLab xs, ppLab ys ])
      where
      ppLab as = ppNestedSels (thing as) <+> "at" <+> pp (srcRange as)

    InvalidDependency ds ->
      hang "[error] Invalid recursive dependency:"
         4 (vcat [ "•" <+> pp x <.> ", defined at" <+> ppR (depNameLoc x)
                 | x <- ds ])
      where ppR r = pp (from r) <.> "--" <.> pp (to r)

instance PP DepName where
  ppPrec _ d =
    case d of
      ConstratintAt r -> "constraint at" <+> pp r
      NamedThing n ->
        case nameNamespace n of
          NSModule -> "submodule" <+> pp n
          NSType   -> "type" <+> pp n
          NSValue  -> pp n
          NSSignature -> "signature" <+> pp n
      ModParamName r x ->
        case x of
          Nothing -> "module parameter at" <+> pp r
          Just m  -> "module parameter" <+> pp m



-- Warnings --------------------------------------------------------------------

data RenamerWarning
  = SymbolShadowed PName Name [Name]
  | UnusedName Name
    deriving (Show, Generic, NFData)

instance Eq RenamerWarning where
  x == y = compare x y == EQ

-- used to determine in what order ot show things
instance Ord RenamerWarning where
  compare w1 w2 =
    case w1 of
      SymbolShadowed x y _ ->
        case w2 of
          SymbolShadowed x' y' _ -> compare (byStart y,x) (byStart y',x')
          _                      -> LT
      UnusedName x ->
        case w2 of
          UnusedName y -> compare (byStart x) (byStart y)
          _            -> GT

      where
      byStart = from . nameLoc


instance PP RenamerWarning where
  ppPrec _ (SymbolShadowed k x os) =
    hang (text "[warning] at" <+> loc)
       4 $ fsep [ "This binding for" <+> backticks (pp k)
                , "shadows the existing binding" <.> plural
                , text "at" ]
        $$ vcat (map (pp . nameLoc) os)

    where
    plural | length os > 1 = char 's'
           | otherwise     = mempty

    loc = pp (nameLoc x)

  ppPrec _ (UnusedName x) =
    hang (text "[warning] at" <+> pp (nameLoc x))
       4 (text "Unused name:" <+> pp x)



