-- |
-- Module      :  $Header$
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
module Cryptol.TypeCheck.AST
  ( module Cryptol.TypeCheck.AST
  , Name()
  , TFun(..)
  , Selector(..)
  , Import(..)
  , ImportSpec(..)
  , ExportType(..)
  , ExportSpec(..), isExportedBind, isExportedType
  , Pragma(..)
  , Fixity(..)
  , PrimMap(..)
  , TCErrorMessage(..)
  , module Cryptol.TypeCheck.Type
  ) where

import Cryptol.ModuleSystem.Name
import Cryptol.Prims.Syntax
import Cryptol.Parser.AST ( Selector(..),Pragma(..)
                          , Import(..), ImportSpec(..), ExportType(..)
                          , ExportSpec(..), isExportedBind
                          , isExportedType, Fixity(..) )
import Cryptol.Utils.Ident (Ident,isInfixIdent,ModName,packIdent)
import Cryptol.TypeCheck.PP
import Cryptol.TypeCheck.Type

import GHC.Generics (Generic)
import Control.DeepSeq

import           Data.Map    (Map)
import qualified Data.IntMap as IntMap




-- | A Cryptol module.
data Module = Module { mName     :: !ModName
                     , mExports  :: ExportSpec Name
                     , mImports  :: [Import]
                     , mTySyns   :: Map Name TySyn
                     , mNewtypes :: Map Name Newtype
                     , mDecls    :: [DeclGroup]
                     } deriving (Show, Generic, NFData)


data Expr   = EList [Expr] Type         -- ^ List value (with type of elements)
            | ETuple [Expr]             -- ^ Tuple value
            | ERec [(Ident,Expr)]       -- ^ Record value
            | ESel Expr Selector        -- ^ Elimination for tuple/record/list

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


            {- | Proof abstraction.  Because we don't keep proofs around
                 we don't need to name the assumption, but we still need to
                 record the assumption.  The assumption is the `Type` term,
                 which should be of kind `KProp`.
             -}
            | EProofAbs {- x -} Prop Expr

            {- | If `e : p => t`, then `EProofApp e : t`,
                 as long as we can prove `p`.

                 We don't record the actual proofs, as they are not
                 used for anything.  It may be nice to keep them around
                 for sanity checking.
             -}

            | EProofApp Expr {- proof -}

            | EWhere Expr [DeclGroup]

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
                       , dDoc         :: Maybe String
                       } deriving (Generic, NFData, Show)

data DeclDef    = DPrim
                | DExpr Expr
                  deriving (Show, Generic, NFData)

-- ShowAST prints out just enough information to model the program in Coq
class ShowAST t where
  showAst :: t -> String

instance ShowAST Expr where
  showAst (EList es _) = "(EList " ++ showAst es ++ ")"
  showAst (ETuple es) = "(ETuple " ++ showAst es ++ ")"
  showAst (ERec ides) = "(ERec " ++ showAst ides ++ ")"
  showAst (ESel e s) = "(ESel " ++ showAst e ++ " " ++ showAst s ++ ")"
  showAst (EIf c t f) = "(EIf " ++ showAst c ++ " " ++ showAst t ++ " " ++ showAst f ++ ")"
  showAst (EComp _ _ e mss) = "(EComp " ++ showAst e ++ " " ++ showAst mss ++ ")"
  showAst (EVar n) = "(EVar " ++ showAst n ++ ")"
  showAst (EApp fe ae) = "(EApp " ++ showAst fe ++ " " ++ showAst ae ++ ")"
  showAst (EAbs n _ e) = "(EAbs " ++ showAst n ++ " " ++ showAst e ++ ")"
  showAst (EWhere e dclg) = "(EWhere " ++ showAst e ++ " " ++ showAst dclg ++ ")"
  --NOTE: erase all types for now, so these don't matter
  showAst (EProofAbs {-p-}_ e) = showAst e --"(EProofAbs " ++ show p ++ showAst e ++ ")"
  showAst (EProofApp e) = showAst e --"(EProofApp " ++ showAst e ++ ")"
  showAst (ETAbs {-tp-}_ e) = showAst e --"(ETAbs " ++ showAst tp ++ " " ++ showAst e ++ ")"
  showAst (ETApp e {-t-}_) = showAst e -- "(ETapp " ++ showAst e ++ " " ++ showAst t ++ ")"


instance (ShowAST a, ShowAST b) => ShowAST (a,b) where
  showAst (x,y) = "(" ++ showAst x ++ "," ++ showAst y ++ ")"
  
instance ShowAST Ident where
  showAst i = show i

instance ShowAST Type where
  showAst t = show t

instance ShowAST Selector where
  showAst s = show s

instance ShowAST Match where
  showAst (From n _ _ e) = "(From " ++ showAst n ++ " " ++ showAst e ++ ")"
  showAst (Let d) = "(Let " ++ showAst d ++ ")"

instance ShowAST Decl where
  showAst d = "(Decl " ++ showAst (dName d) ++ " " ++ showAst (dDefinition d) ++ ")"

instance ShowAST DeclDef where
  showAst DPrim = show DPrim
  showAst (DExpr e) = "(DExpr " ++ (showAst e) ++ ")"

instance ShowAST DeclGroup where
  showAst (Recursive ds) = showAst ds
  showAst (NonRecursive d) = showAst d

showASTList :: (ShowAST a) => [a] -> String
showASTList [] = ""
showASTList [x] = showAst x
showASTList (x : y) = (showAst x) ++ "," ++ showASTList y

instance (ShowAST a) => ShowAST [a] where
  showAst a = "[" ++ showASTList a ++ "]"

instance ShowAST TParam where
  showAst tp = show (tpUnique tp)

instance ShowAST Name where
  showAst n = show (nameUnique n)

-- instance ShowAST Expr where
--   showAst (ETAbs tp e) = "(ETAbs " ++ showAst tp ++ showAst e ++ ")"
--   showAst e = show e


--------------------------------------------------------------------------------



-- | Construct a primitive, given a map to the unique names of the Cryptol
-- module.
ePrim :: PrimMap -> Ident -> Expr
ePrim pm n = EVar (lookupPrimDecl n pm)

-- | Make an expression that is `error` pre-applied to a type and a message.
eError :: PrimMap -> Type -> String -> Expr
eError prims t str =
  EApp (ETApp (ETApp (ePrim prims (packIdent "error")) t)
              (tNum (length str))) (eString prims str)

eString :: PrimMap -> String -> Expr
eString prims str = EList (map (eChar prims) str) tChar

eChar :: PrimMap -> Char -> Expr
eChar prims c = ETApp (ETApp (ePrim prims (packIdent "demote")) (tNum v)) (tNum w)
  where v = fromEnum c
        w = 8 :: Int


instance PP (WithNames Expr) where
  ppPrec prec (WithNames expr nm) =
    case expr of
      EList [] t    -> optParens (prec > 0)
                    $ text "[]" <+> colon <+> ppWP prec t

      EList es _    -> brackets $ sep $ punctuate comma $ map ppW es

      ETuple es     -> parens $ sep $ punctuate comma $ map ppW es

      ERec fs       -> braces $ sep $ punctuate comma
                        [ pp f <+> text "=" <+> ppW e | (f,e) <- fs ]

      ESel e sel    -> ppWP 4 e <+> text "." <> pp sel

      EIf e1 e2 e3  -> optParens (prec > 0)
                    $ sep [ text "if"   <+> ppW e1
                          , text "then" <+> ppW e2
                          , text "else" <+> ppW e3 ]

      EComp _ _ e mss -> let arm ms = text "|" <+> commaSep (map ppW ms)
                          in brackets $ ppW e <+> vcat (map arm mss)

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
                    $ ppWP 3 e <+> ppWP 4 t

      EWhere e ds   -> optParens (prec > 0)
                     ( ppW e $$ text "where"
                                     $$ nest 2 (vcat (map ppW ds))
                                     $$ text "" )

    where
    ppW x   = ppWithNames nm x
    ppWP x  = ppWithNamesPrec nm x

ppLam :: NameMap -> Int -> [TParam] -> [Prop] -> [(Name,Type)] -> Expr -> Doc
ppLam nm prec [] [] [] e = ppWithNamesPrec nm prec e
ppLam nm prec ts ps xs e =
  optParens (prec > 0) $
  sep [ text "\\" <> tsD <+> psD <+> xsD <+> text "->"
      , ppWithNames ns1 e
      ]
  where
  ns1 = addTNames ts nm

  tsD = if null ts then empty else braces $ sep $ punctuate comma $ map ppT ts
  psD = if null ps then empty else parens $ sep $ punctuate comma $ map ppP ps
  xsD = if null xs then empty else sep    $ map ppArg xs

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
    pp dName <+> text ":" <+> ppWithNames nm dSignature  $$
    (if null dPragmas
        then empty
        else text "pragmas" <+> pp dName <+> sep (map pp dPragmas)
    ) $$
    pp dName <+> text "=" <+> ppWithNames nm dDefinition

instance PP (WithNames DeclDef) where
  ppPrec _ (WithNames DPrim _)      = text "<primitive>"
  ppPrec _ (WithNames (DExpr e) nm) = ppWithNames nm e

instance PP Decl where
  ppPrec = ppWithNamesPrec IntMap.empty

instance PP Module where
  ppPrec = ppWithNamesPrec IntMap.empty

instance PP (WithNames Module) where
  ppPrec _ (WithNames Module { .. } nm) =
    text "module" <+> pp mName $$
    -- XXX: Print exports?
    vcat (map pp mImports) $$
    -- XXX: Print tysyns
    vcat (map (ppWithNames nm) mDecls)

