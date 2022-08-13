-- |
-- Module      :  Cryptol.TypeCheck.AST
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe                                #-}

{-# LANGUAGE RecordWildCards                     #-}
{-# LANGUAGE PatternGuards                       #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE DeriveAnyClass, DeriveGeneric       #-}
{-# LANGUAGE OverloadedStrings                   #-}
module Cryptol.TypeCheck.AST
  ( module Cryptol.TypeCheck.AST
  , Name()
  , TFun(..)
  , Selector(..)
  , Import, ImportG(..)
  , ImportSpec(..)
  , ExportType(..)
  , ExportSpec(..), isExportedBind, isExportedType, isExported
  , Pragma(..)
  , Fixity(..)
  , PrimMap(..)
  , module Cryptol.TypeCheck.Type
  ) where

import Cryptol.Parser.Position(Located,Range,HasLoc(..))
import Cryptol.ModuleSystem.Name
import Cryptol.ModuleSystem.Interface
import Cryptol.ModuleSystem.Exports(ExportSpec(..)
                                   , isExportedBind, isExportedType, isExported)
import Cryptol.Parser.AST ( Selector(..),Pragma(..)
                          , Import
                          , ImportG(..), ImportSpec(..), ExportType(..)
                          , Fixity(..))
import Cryptol.Utils.Ident (Ident,isInfixIdent,ModName,PrimIdent,prelPrim)
import Cryptol.Utils.RecordMap
import Cryptol.TypeCheck.FFI.FFIType
import Cryptol.TypeCheck.PP
import Cryptol.TypeCheck.Type

import GHC.Generics (Generic)
import Control.DeepSeq

import           Data.Map    (Map)
import qualified Data.Map    as Map
import qualified Data.IntMap as IntMap
import           Data.Text (Text)


-- | A Cryptol module.
data ModuleG mname =
              Module { mName             :: !mname
                     , mExports          :: ExportSpec Name
                     , mImports          :: [Import]

                       {-| Interfaces of submodules, including functors.
                           This is only the directly nested modules.
                           Info about more nested modules is in the
                           corresponding interface. -}
                     , mSubModules       :: Map Name (IfaceG Name)

                     -- params, if functor
                     , mParamTypes       :: Map Name ModTParam
                     , mParamConstraints :: [Located Prop]
                     , mParamFuns        :: Map Name ModVParam


                      -- Declarations, including everything from non-functor
                      -- submodules
                     , mTySyns           :: Map Name TySyn
                     , mNewtypes         :: Map Name Newtype
                     , mPrimTypes        :: Map Name AbstractType
                     , mDecls            :: [DeclGroup]
                     , mFunctors         :: Map Name (ModuleG Name)
                     } deriving (Show, Generic, NFData)

emptyModule :: mname -> ModuleG mname
emptyModule nm =
  Module
    { mName             = nm
    , mExports          = mempty
    , mImports          = []
    , mSubModules       = mempty

    , mParamTypes       = mempty
    , mParamConstraints = mempty
    , mParamFuns        = mempty

    , mTySyns           = mempty
    , mNewtypes         = mempty
    , mPrimTypes        = mempty
    , mDecls            = mempty
    , mFunctors         = mempty
    }

type Module = ModuleG ModName

-- | Is this a parameterized module?
isParametrizedModule :: ModuleG mname -> Bool
isParametrizedModule m = not (null (mParamTypes m) &&
                              null (mParamConstraints m) &&
                              null (mParamFuns m))


data Expr   = EList [Expr] Type         -- ^ List value (with type of elements)
            | ETuple [Expr]             -- ^ Tuple value
            | ERec (RecordMap Ident Expr) -- ^ Record value
            | ESel Expr Selector        -- ^ Elimination for tuple/record/list
            | ESet Type Expr Selector Expr -- ^ Change the value of a field.
                                           --   The included type gives the type of the record being updated

            | EIf Expr Expr Expr        -- ^ If-then-else
            | EComp Type Type Expr [[Match]]
                                        -- ^ List comprehensions
                                        --   The types cache the length of the
                                        --   sequence and its element type.

            | EVar Name                 -- ^ Use of a bound variable

            | ETAbs TParam Expr         -- ^ Function Value
            | ETApp Expr Type           -- ^ Type application

            | EApp Expr Expr            -- ^ Function application
            | EAbs Name Type Expr       -- ^ Function value


            | ELocated Range Expr       -- ^ Source location information

            {- | Proof abstraction.  Because we don't keep proofs around
                 we don't need to name the assumption, but we still need to
                 record the assumption.  The assumption is the 'Type' term,
                 which should be of kind 'KProp'.
             -}
            | EProofAbs {- x -} Prop Expr

            {- | If @e : p => t@, then @EProofApp e : t@,
                 as long as we can prove @p@.

                 We don't record the actual proofs, as they are not
                 used for anything.  It may be nice to keep them around
                 for sanity checking.
             -}

            | EProofApp Expr {- proof -}

            | EWhere Expr [DeclGroup]

            | EPropGuards [([Prop], Expr)]

              deriving (Show, Generic, NFData)


data Match  = From Name Type Type Expr
                                  -- ^ Type arguments are the length and element
                                  --   type of the sequence expression
            | Let Decl
              deriving (Show, Generic, NFData)

data DeclGroup  = Recursive   [Decl]    -- ^ Mutually recursive declarations
                | NonRecursive Decl     -- ^ Non-recursive declaration
                  deriving (Show, Generic, NFData)

groupDecls :: DeclGroup -> [Decl]
groupDecls dg = case dg of
  Recursive ds   -> ds
  NonRecursive d -> [d]


data Decl       = Decl { dName        :: !Name
                       , dSignature   :: Schema
                       , dDefinition  :: DeclDef
                       , dPragmas     :: [Pragma]
                       , dInfix       :: !Bool
                       , dFixity      :: Maybe Fixity
                       , dDoc         :: Maybe Text
                       } deriving (Generic, NFData, Show)

data DeclDef    = DPrim
                | DForeign FFIFunType
                | DExpr Expr
                  deriving (Show, Generic, NFData)


--------------------------------------------------------------------------------

-- | Construct a primitive, given a map to the unique primitive name.
ePrim :: PrimMap -> PrimIdent -> Expr
ePrim pm n = EVar (lookupPrimDecl n pm)

-- | Make an expression that is @error@ pre-applied to a type and a message.
eError :: PrimMap -> Type -> String -> Expr
eError prims t str =
  EApp (ETApp (ETApp (ePrim prims (prelPrim "error")) t)
              (tNum (length str))) (eString prims str)

eString :: PrimMap -> String -> Expr
eString prims str = EList (map (eChar prims) str) tChar

eChar :: PrimMap -> Char -> Expr
eChar prims c = ETApp (ETApp (ePrim prims (prelPrim "number")) (tNum v)) (tWord (tNum w))
  where v = fromEnum c
        w = 8 :: Int


instance PP (WithNames Expr) where
  ppPrec prec (WithNames expr nm) =
    case expr of
      ELocated _ t  -> ppWP prec t

      EList [] t    -> optParens (prec > 0)
                    $ text "[]" <+> colon <+> ppWP prec t

      EList es _    -> ppList $ map ppW es

      ETuple es     -> ppTuple $ map ppW es

      ERec fs       -> ppRecord
                        [ pp f <+> text "=" <+> ppW e | (f,e) <- displayFields fs ]

      ESel e sel    -> ppWP 4 e <.> text "." <.> pp sel

      ESet _ty e sel v  -> braces (pp e <+> "|" <+> pp sel <+> "=" <+> pp v)

      EIf e1 e2 e3  -> optParens (prec > 0)
                    $ sep [ text "if"   <+> ppW e1
                          , text "then" <+> ppW e2
                          , text "else" <+> ppW e3 ]

      EComp _ _ e mss -> let arm ms = text "|" <+> commaSep (map ppW ms)
                          in brackets $ ppW e <+> (align (vcat (map arm mss)))

      EVar x        -> ppPrefixName x

      EAbs {}       -> let (xs,e) = splitWhile splitAbs expr
                       in ppLam nm prec [] [] xs e

      EProofAbs {}  -> let (ps,e1) = splitWhile splitProofAbs expr
                           (xs,e2) = splitWhile splitAbs e1
                       in ppLam nm prec [] ps xs e2

      ETAbs {}      -> let (ts,e1) = splitWhile splitTAbs     expr
                           (ps,e2) = splitWhile splitProofAbs e1
                           (xs,e3) = splitWhile splitAbs      e2
                       in ppLam nm prec ts ps xs e3

      -- infix applications
      EApp (EApp (EVar o) a) b
        | isInfixIdent (nameIdent o) ->
          ppPrec 3 a <+> ppInfixName o <+> ppPrec 3 b

        | otherwise ->
          ppPrefixName o <+> ppPrec 3 a <+> ppPrec 3 b

      EApp e1 e2    -> optParens (prec > 3)
                    $  ppWP 3 e1 <+> ppWP 4 e2

      EProofApp e   -> optParens (prec > 3)
                    $ ppWP 3 e <+> text "<>"

      ETApp e t     -> optParens (prec > 3)
                    $ ppWP 3 e <+> ppWP 5 t

      EWhere e ds   -> optParens (prec > 0) $ align $ vsep $
                         [ ppW e
                         , hang "where" 2 (vcat (map ppW ds))
                         ]
      
      EPropGuards guards -> 
        parens (text "propguard" <+> hsep (ppGuard <$> guards))
        where ppGuard (props, e) = 
                pipe <+> commaSep (pp <$> props) <+> text "=>" <+> pp e

    where
    ppW x   = ppWithNames nm x
    ppWP x  = ppWithNamesPrec nm x

ppLam :: NameMap -> Int -> [TParam] -> [Prop] -> [(Name,Type)] -> Expr -> Doc
ppLam nm prec [] [] [] e = nest 2 (ppWithNamesPrec nm prec e)
ppLam nm prec ts ps xs e =
  optParens (prec > 0) $
  nest 2 $ sep
    [ text "\\" <.> hsep (tsD ++ psD ++ xsD ++ [text "->"])
    , ppWithNames ns1 e
    ]
  where
  ns1 = addTNames ts nm

  tsD = if null ts then [] else [braces $ commaSep $ map ppT ts]
  psD = if null ps then [] else [parens $ commaSep $ map ppP ps]
  xsD = if null xs then [] else [sep    $ map ppArg xs]

  ppT = ppWithNames ns1
  ppP = ppWithNames ns1
  ppArg (x,t) = parens (pp x <+> text ":" <+> ppWithNames ns1 t)


splitWhile :: (a -> Maybe (b,a)) -> a -> ([b],a)
splitWhile f e = case f e of
                   Nothing     -> ([], e)
                   Just (x,e1) -> let (xs,e2) = splitWhile f e1
                                  in (x:xs,e2)

splitAbs :: Expr -> Maybe ((Name,Type), Expr)
splitAbs (EAbs x t e)         = Just ((x,t), e)
splitAbs _                    = Nothing

splitTAbs :: Expr -> Maybe (TParam, Expr)
splitTAbs (ETAbs t e)         = Just (t, e)
splitTAbs _                   = Nothing

splitProofAbs :: Expr -> Maybe (Prop, Expr)
splitProofAbs (EProofAbs p e) = Just (p,e)
splitProofAbs _               = Nothing

splitTApp :: Expr -> Maybe (Type,Expr)
splitTApp (ETApp e t) = Just (t, e)
splitTApp _           = Nothing

splitProofApp :: Expr -> Maybe ((), Expr)
splitProofApp (EProofApp e) = Just ((), e)
splitProofApp _ = Nothing

-- | Deconstruct an expression, typically polymorphic, into
-- the types and proofs to which it is applied.
-- Since we don't store the proofs, we just return
-- the number of proof applications.
-- The first type is the one closest to the expr.
splitExprInst :: Expr -> (Expr, [Type], Int)
splitExprInst e = (e2, reverse ts, length ps)
  where
  (ps,e1) = splitWhile splitProofApp e
  (ts,e2) = splitWhile splitTApp e1


instance HasLoc Expr where
  getLoc (ELocated r _) = Just r
  getLoc _ = Nothing

instance PP Expr where
  ppPrec n t = ppWithNamesPrec IntMap.empty n t


instance PP (WithNames Match) where
  ppPrec _ (WithNames mat nm) =
    case mat of
      From x _ _ e -> pp x <+> text "<-" <+> ppWithNames nm e
      Let d      -> text "let" <+> ppWithNames nm d

instance PP Match where
  ppPrec = ppWithNamesPrec IntMap.empty

instance PP (WithNames DeclGroup) where
  ppPrec _ (WithNames dg nm) =
    case dg of
      Recursive ds    -> text "/* Recursive */"
                      $$ vcat (map (ppWithNames nm) ds)
                      $$ text ""
      NonRecursive d  -> text "/* Not recursive */"
                      $$ ppWithNames nm d
                      $$ text ""

instance PP DeclGroup where
  ppPrec = ppWithNamesPrec IntMap.empty

instance PP (WithNames Decl) where
  ppPrec _ (WithNames Decl { .. } nm) =
    vcat $
      [ pp dName <+> text ":" <+> ppWithNames nm dSignature ]
      ++ (if null dPragmas
            then []
            else [text "pragmas" <+> pp dName <+> sep (map pp dPragmas)])
      ++ [ nest 2 (sep [pp dName <+> text "=", ppWithNames nm dDefinition]) ]

instance PP (WithNames DeclDef) where
  ppPrec _ (WithNames DPrim _)        = text "<primitive>"
  ppPrec _ (WithNames (DForeign _) _) = text "<foreign>"
  ppPrec _ (WithNames (DExpr e) nm)   = ppWithNames nm e

instance PP Decl where
  ppPrec = ppWithNamesPrec IntMap.empty

instance PP n => PP (ModuleG n) where
  ppPrec = ppWithNamesPrec IntMap.empty

instance PP n => PP (WithNames (ModuleG n)) where
  ppPrec _ (WithNames Module { .. } nm) =
    text "module" <+> pp mName $$
    -- XXX: Print exports?
    vcat (map pp mImports) $$
    -- XXX: Print tysyns
    -- XXX: Print abstarct types/functions
    vcat (map (ppWithNames (addTNames mps nm)) mDecls)
    where mps = map mtpParam (Map.elems mParamTypes)
