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

import Data.List(intersperse)

import Cryptol.ModuleSystem.Name
import Cryptol.Parser.AST
import Cryptol.Parser.Position
import Cryptol.Parser.Selector(ppNestedSels)
import Cryptol.Utils.PP
import Cryptol.Utils.Ident(modPathSplit)

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

  | OverlappingRecordUpdate (Located [Selector]) (Located [Selector])
    -- ^ When record updates overlap (e.g., @{ r | x = e1, x.y = e2 }@)

  | InvalidDependency [DepName]
    -- ^ Things that can't depend on each other

  | MultipleModParams Ident [Range]
    -- ^ Module parameters with the same name

  | InvalidFunctorImport (ImpName Name)
    -- ^ Can't import functors directly

  | UnexpectedNest Range PName
    -- ^ Nested modules were not supposed to appear here

  | ModuleKindMismatch Range (ImpName Name) ModKind ModKind
    -- ^ Exepcted one kind (first one) but found the other (second one)

    deriving (Show, Generic, NFData, Eq, Ord)


{- | We use this to name dependencies.
In addition to normal names we have a way to refer to module parameters
and top-level module constraints, which have no explicit names -}
data DepName = NamedThing Name
               -- ^ Something with a name

             | ModPath ModPath
               -- ^ The module at this path

             | ModParamName Range Ident
               {- ^ Note that the range is important not just for error
                    reporting but to distinguish module parameters with
                    the same name (e.g., in nested functors) -}
             | ConstratintAt Range
               -- ^ Identifed by location in source
               deriving (Eq,Ord,Show,Generic,NFData)

depNameLoc :: DepName -> Maybe Range
depNameLoc x =
  case x of
    NamedThing n -> Just (nameLoc n)
    ConstratintAt r -> Just r
    ModParamName r _ -> Just r
    ModPath {} -> Nothing


data ModKind = AFunctor | ASignature | AModule
    deriving (Show, Generic, NFData, Eq, Ord)

instance PP ModKind where
  ppPrec _ e =
    case e of
      AFunctor   -> "a functor"
      ASignature -> "an interface"
      AModule    -> "a module"



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
                    NSConstructor -> "Constructor"

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
                     NSConstructor -> "constructor"
                     NSType   -> "type"
                     NSModule -> "module"
        suggestion =
          case (expected,actual) of

            (NSValue,NSType) ->
                ["Did you mean `(" <.> pp (thing lqn) <.> text")?"]
            (NSConstructor,NSValue) ->
                ["Perhaps the constructor got shadowed?"]
            _ -> []

    FixityError o1 f1 o2 f2 ->
      hang (text "[error] at" <+> pp (srcRange o1) <+> text "and" <+> pp (srcRange o2))
         4 (vsep [ text "The fixities of"
                 , indent 2 $ vcat
                   [ "•" <+> pp (thing o1) <+> parens (pp f1)
                   , "•" <+> pp (thing o2) <+> parens (pp f2) ]
                 , text "are not compatible."
                 , text "You may use explicit parentheses to disambiguate." ])

    OverlappingRecordUpdate xs ys ->
      hang "[error] Overlapping record updates:"
         4 (vcat [ ppLab xs, ppLab ys ])
      where
      ppLab as = ppNestedSels (thing as) <+> "at" <+> pp (srcRange as)

    InvalidDependency ds ->
      hang ("[error] Invalid" <+> self <+>"dependency:")
         4 (vcat [ "•" <+> pp x <.>
                    case depNameLoc x of
                      Just r -> ", defined at" <+> ppR r
                      Nothing -> mempty
                 | x <- ds ])
      where ppR r = pp (from r) <.> "--" <.> pp (to r)
            self = case ds of
                     [_] -> "self"
                     _   -> "recursive"

    MultipleModParams x rs ->
      hang ("[error] Multiple parameters with name" <+> backticks (pp x))
         4 (vcat [ "•" <+> pp r | r <- rs ])

    InvalidFunctorImport x ->
      hang ("[error] Invalid import of functor" <+> backticks (pp x))
        4 "• Functors need to be instantiated before they can be imported."

    UnexpectedNest s x ->
      hang ("[error] at" <+> pp s)
        4 ("submodule" <+> backticks (pp x) <+> "may not be defined here.")

    ModuleKindMismatch r x expected actual ->
      hang ("[error] at" <+> pp r)
        4 (vcat [ "• Expected" <+> pp expected
                , "•" <+> backticks (pp x) <+> "is" <+> pp actual
                ])


instance PP DepName where
  ppPrec _ d =
    case d of
      ConstratintAt r -> "constraint at" <+> pp r
      NamedThing n ->
        case nameNamespace n of
          NSModule -> "submodule" <+> pp n
          NSType   -> "type" <+> pp n
          NSValue  -> pp n
          NSConstructor -> "constructor" <+> pp n
      ModParamName _r i -> "module parameter" <+> pp i
      ModPath mp ->
        case modPathSplit mp of
          (m,[]) -> "module" <+> pp m
          (_,is) -> "submodule" <+> hcat (intersperse "::" (map pp is))



-- Warnings --------------------------------------------------------------------

data RenamerWarning
  = SymbolShadowed PName Name [Name]
  | UnusedName Name
  | PrefixAssocChanged PrefixOp (Expr Name) (Located Name) Fixity (Expr Name)
    deriving (Show, Generic, NFData)

instance Eq RenamerWarning where
  x == y = compare x y == EQ

-- used to determine in what order to show things
instance Ord RenamerWarning where
  compare w1 w2 =
    case (w1, w2) of
      (SymbolShadowed x y _, SymbolShadowed x' y' _) ->
        compare (byStart y, x) (byStart y', x')
      (UnusedName x, UnusedName x') ->
        compare (byStart x) (byStart x')
      (PrefixAssocChanged _ _ op _ _, PrefixAssocChanged _ _ op' _ _) ->
        compare (from $ srcRange op) (from $ srcRange op')
      _ -> compare (priority w1) (priority w2)

      where
      byStart = from . nameLoc
      priority SymbolShadowed {}     = 0 :: Int
      priority UnusedName {}         = 1
      priority PrefixAssocChanged {} = 2

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

  ppPrec _ (PrefixAssocChanged prefixOp x infixOp infixFixity y) =
    hang (text "[warning] at" <+> pp (srcRange infixOp))
       4 $ fsep [ backticks (pp old)
                , "is now parsed as"
                , backticks (pp new) ]

    where
    old = EInfix (EPrefix prefixOp x) infixOp infixFixity y
    new = EPrefix prefixOp (EInfix x infixOp infixFixity y)
