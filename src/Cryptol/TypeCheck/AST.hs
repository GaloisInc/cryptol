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
{-# LANGUAGE NamedFieldPuns                      #-}
{-# LANGUAGE ViewPatterns                        #-}
module Cryptol.TypeCheck.AST
  ( module Cryptol.TypeCheck.AST
  , Name()
  , TFun(..)
  , Selector(..)
  , Import, ImportG(..), ImpName(..)
  , ImportSpec(..)
  , ExportType(..)
  , ExportSpec(..), isExportedBind, isExportedType, isExported
  , Pragma(..)
  , Fixity(..)
  , PrimMap(..)
  , module Cryptol.TypeCheck.Type
  ) where

import Data.Maybe(mapMaybe)

import Cryptol.Utils.Panic(panic)
import Cryptol.Utils.Ident (Ident,isInfixIdent,ModName,PrimIdent,prelPrim)
import Cryptol.Parser.Position(Located,Range,HasLoc(..))
import Cryptol.ModuleSystem.Name
import Cryptol.ModuleSystem.NamingEnv.Types
import Cryptol.ModuleSystem.Interface
import Cryptol.ModuleSystem.Exports(ExportSpec(..)
                                   , isExportedBind, isExportedType, isExported)
import Cryptol.Parser.AST ( Selector(..),Pragma(..)
                          , Import
                          , ImportG(..), ImportSpec(..), ExportType(..)
                          , Fixity(..)
                          , ImpName(..)
                          )
import Cryptol.Utils.RecordMap
import Cryptol.TypeCheck.FFI.FFIType
import Cryptol.TypeCheck.PP
import Cryptol.TypeCheck.Type

import GHC.Generics (Generic)
import Control.DeepSeq


import           Data.Set    (Set)
import           Data.Map    (Map)
import qualified Data.Map    as Map
import qualified Data.IntMap as IntMap
import           Data.Text (Text)


data TCTopEntity =
    TCTopModule (ModuleG ModName)
  | TCTopSignature ModName ModParamNames
    deriving (Show, Generic, NFData)

tcTopEntitytName :: TCTopEntity -> ModName
tcTopEntitytName ent =
  case ent of
    TCTopModule m -> mName m
    TCTopSignature m _ -> m

-- | Panics if the entity is not a module
tcTopEntityToModule :: TCTopEntity -> Module
tcTopEntityToModule ent =
  case ent of
    TCTopModule m -> m
    TCTopSignature {} -> panic "tcTopEntityToModule" [ "Not a module" ]


-- | A Cryptol module.
data ModuleG mname =
              Module { mName             :: !mname
                     , mDoc              :: !(Maybe Text)
                     , mExports          :: ExportSpec Name

                     -- Functors:
                     , mParamTypes       :: Map Name ModTParam
                     , mParamFuns        :: Map Name ModVParam
                     , mParamConstraints :: [Located Prop]

                     , mParams           :: FunctorParams
                       -- ^ Parameters grouped by "import".

                     , mFunctors         :: Map Name (ModuleG Name)
                       -- ^ Functors directly nested in this module.
                       -- Things further nested are in the modules in the
                       -- elements of the map.


                     , mNested           :: !(Set Name)
                       -- ^ Submodules, functors, and interfaces nested directly
                       -- in this module

                      -- These have everything from this module and all submodules
                     , mTySyns           :: Map Name TySyn
                     , mNewtypes         :: Map Name Newtype
                     , mPrimTypes        :: Map Name AbstractType
                     , mDecls            :: [DeclGroup]
                     , mSubmodules       :: Map Name (IfaceNames Name)
                     , mSignatures       :: !(Map Name ModParamNames)

                     , mInScope          :: NamingEnv
                       -- ^ Things in scope at the top level.
                       --   Submodule in-scope information is in 'mSubmodules'.
                     } deriving (Show, Generic, NFData)

emptyModule :: mname -> ModuleG mname
emptyModule nm =
  Module
    { mName             = nm
    , mDoc              = Nothing
    , mExports          = mempty

    , mParams           = mempty
    , mParamTypes       = mempty
    , mParamConstraints = mempty
    , mParamFuns        = mempty

    , mNested           = mempty

    , mTySyns           = mempty
    , mNewtypes         = mempty
    , mPrimTypes        = mempty
    , mDecls            = mempty
    , mFunctors         = mempty
    , mSubmodules       = mempty
    , mSignatures       = mempty

    , mInScope          = mempty
    }

-- | Find all the foreign declarations in the module and return their names and FFIFunTypes.
findForeignDecls :: ModuleG mname -> [(Name, FFIFunType)]
findForeignDecls = mapMaybe getForeign . concatMap groupDecls . mDecls
  where getForeign d =
          case dDefinition d of
            DForeign ffiType _ -> Just (dName d, ffiType)
            _                  -> Nothing

-- | Find all the foreign declarations that are in functors, including in the
-- top-level module itself if it is a functor.
-- This is used to report an error
findForeignDeclsInFunctors :: ModuleG mname -> [Name]
findForeignDeclsInFunctors mo
  | isParametrizedModule mo = fromM mo
  | otherwise               = findInSubs mo
  where
  findInSubs :: ModuleG mname -> [Name]
  findInSubs = concatMap fromM . Map.elems . mFunctors
  fromM m = map fst (findForeignDecls m) ++ findInSubs m




type Module = ModuleG ModName

-- | Is this a parameterized module?
isParametrizedModule :: ModuleG mname -> Bool
isParametrizedModule m = not (null (mParams m) &&
                              null (mParamTypes m) &&
                              null (mParamConstraints m) &&
                              null (mParamFuns m))


data Expr   = EList [Expr] Type         -- ^ List value (with type of elements)
            | ETuple [Expr]             -- ^ Tuple value
            | ERec (RecordMap Ident Expr) -- ^ Record value
            | ESel Expr Selector        -- ^ Elimination for tuple/record/list
            | ESet Type Expr Selector Expr -- ^ Change the value of a field.
                                           --   The included type gives the type of the record being updated

            | EIf Expr Expr Expr        -- ^ If-then-else
            | ECase Expr (Map Ident CaseAlt) (Maybe CaseAlt)
              -- ^ Case expression. The keys are the name of constructors
              -- `Nothing` for default case, the expresssions are what to
              -- do if the constructor matches.  If the constructor binds
              -- variables, then then the expr should be `EAbs`
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

            | EPropGuards [([Prop], Expr)] Type

              deriving (Show, Generic, NFData)

-- | Used for case expressions.  Similar to a lambda, the variables
-- are bound by the value examined in the case.
data CaseAlt = CaseAlt [(Name,Type)] Expr
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
                -- | Foreign functions can have an optional cryptol
                -- implementation
                | DForeign FFIFunType (Maybe Expr)
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

instance PP TCTopEntity where
  ppPrec _ te =
    case te of
      TCTopModule m -> pp m
      TCTopSignature x p ->
        ("interface" <+> pp x <+> "where") $$ nest 2 (pp p)


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
      ECase e arms dflt ->
        optParens (prec > 0) $
        vcat [ "case" <+> pp e <+> "of"
             , indent 2 (vcat ppArms $$ ppDflt)
             ]
        where
        ppArms  = [ pp i <+> pp c | (i,c) <- reverse (Map.toList arms) ]
        ppDflt  = maybe mempty pp dflt

      EComp _ _ e mss -> let arm ms = text "|" <+> commaSep (map ppW ms)
                          in brackets $ ppW e <+> align (vcat (map arm mss))

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

      EPropGuards guards _ -> 
        parens (text "propguards" <+> vsep (ppGuard <$> guards))
        where ppGuard (props, e) = indent 1
                                 $ pipe <+> commaSep (ppW <$> props)
                               <+> text "=>" <+> ppW e

    where
    ppW x   = ppWithNames nm x
    ppWP x  = ppWithNamesPrec nm x

instance PP CaseAlt where
  ppPrec _ (CaseAlt xs e) = hsep (map ppV xs) <+> "->" <+> pp e
    where ppV (x,t) = parens (pp x <.> ":" <+> pp t)

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

splitLoc :: Expr -> Maybe (Range, Expr)
splitLoc expr =
  case expr of
    ELocated r e -> Just (r,e)
    _            -> Nothing

-- | Remove outermost locations
dropLocs :: Expr -> Expr
dropLocs = snd . splitWhile splitLoc

splitAbs :: Expr -> Maybe ((Name,Type), Expr)
splitAbs (dropLocs -> EAbs x t e) = Just ((x,t), e)
splitAbs _                        = Nothing

splitApp :: Expr -> Maybe (Expr,Expr)
splitApp (dropLocs -> EApp f a) = Just (a, f)
splitApp _                      = Nothing

splitTAbs :: Expr -> Maybe (TParam, Expr)
splitTAbs (dropLocs -> ETAbs t e)   = Just (t, e)
splitTAbs _                         = Nothing

splitProofAbs :: Expr -> Maybe (Prop, Expr)
splitProofAbs (dropLocs -> EProofAbs p e) = Just (p,e)
splitProofAbs _                           = Nothing

splitTApp :: Expr -> Maybe (Type,Expr)
splitTApp (dropLocs -> ETApp e t) = Just (t, e)
splitTApp _                       = Nothing

splitProofApp :: Expr -> Maybe ((), Expr)
splitProofApp (dropLocs -> EProofApp e) = Just ((), e)
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
  ppPrec _ (WithNames DPrim _) = text "<primitive>"
  ppPrec _ (WithNames (DForeign _ me) nm) =
    case me of
      Just e -> text "(foreign)" <+> ppWithNames nm e
      Nothing -> text "<foreign>"
  ppPrec _ (WithNames (DExpr e) nm) = ppWithNames nm e

instance PP Decl where
  ppPrec = ppWithNamesPrec IntMap.empty

instance PP n => PP (ModuleG n) where
  ppPrec = ppWithNamesPrec IntMap.empty

instance PP n => PP (WithNames (ModuleG n)) where
  ppPrec _ (WithNames Module { .. } nm) =
    vcat [ text "module" <+> pp mName
         -- XXX: Print exports?
         , vcat (map pp' (Map.elems mTySyns))
         -- XXX: Print abstarct types/functions
         , vcat (map pp' mDecls)

         , vcat (map pp (Map.elems mFunctors))
         ]
    where mps = map mtpParam (Map.elems mParamTypes)
          pp' :: PP (WithNames a) => a -> Doc
          pp' = ppWithNames (addTNames mps nm)

instance PP (WithNames TCTopEntity) where
  ppPrec _ (WithNames ent nm) =
    case ent of
     TCTopModule m -> ppWithNames nm m
     TCTopSignature n ps ->
        hang ("interface module" <+> pp n <+> "where") 2 (pp ps)
