-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe #-}
{-# LANGUAGE PatternGuards   #-}
{-# LANGUAGE RecordWildCards #-}
module Cryptol.Parser.AST
  ( -- * Names
    ModName(..), {-splitNamespace, parseModName, nsChar,-} modRange
  , QName(..), mkQual, mkUnqual, unqual
  , Name(..)
  , Named(..)
  , Pass(..)

    -- * Types
  , Schema(..)
  , TParam(..), tpQName
  , Kind(..)
  , Type(..)
  , Prop(..)

    -- * Declarations
  , Module(..)
  , Program(..)
  , TopDecl(..)
  , Decl(..)
  , TySyn(..)
  , Bind(..)
  , Pragma(..)
  , ExportType(..)
  , ExportSpec(..), exportBind, exportType
  , isExportedBind, isExportedType
  , TopLevel(..)
  , Import(..), ImportSpec(..)
  , Newtype(..)

    -- * Interactive
  , ReplInput(..)

    -- * Expressions
  , Expr(..)
  , Literal(..), NumInfo(..)
  , Match(..)
  , Pattern(..)
  , Selector(..)
  , TypeInst(..)

    -- * Positions
  , Located(..)
  , LName, LQName, LString
  , NoPos(..)

    -- * Pretty-printing
  , cppKind, ppSelector
  ) where

import Cryptol.Parser.Position
import Cryptol.Prims.Syntax
import Cryptol.Utils.PP

import qualified Data.Map as Map
import qualified Data.Set as Set
import           Data.List(intersperse)
import           Data.Bits(shiftR)
import           Data.Maybe (catMaybes)
import           Numeric(showIntAtBase)

#if __GLASGOW_HASKELL__ < 710
import           Data.Monoid (Monoid(..))
#endif

-- | Module names are just namespaces.
--
-- INVARIANT: the list of strings should never be empty in a valid module name.
newtype ModName = ModName [String]
                  deriving (Eq,Ord,Show)

data Name     = Name String
              | NewName Pass Int
               deriving (Eq,Ord,Show)

data QName    = QName (Maybe ModName) Name
               deriving (Eq,Ord,Show)

mkQual :: ModName -> Name -> QName
mkQual  = QName . Just

mkUnqual :: Name -> QName
mkUnqual  = QName Nothing

unqual :: QName -> Name
unqual (QName _ n) = n


data Pass     = NoPat | MonoValues
               deriving (Eq,Ord,Show)

-- | A name with location information.
type LName    = Located Name

-- | A qualified name with location information.
type LQName   = Located QName

-- | A string with location information.
type LString  = Located String

newtype Program = Program [TopDecl]
                  deriving (Eq,Show)

data Module = Module { mName    :: Located ModName
                     , mImports :: [Located Import]
                     , mDecls   :: [TopDecl]
                     } deriving (Eq,Show)

modRange :: Module -> Range
modRange m = rCombs $ catMaybes
    [ getLoc (mName m)
    , getLoc (mImports m)
    , getLoc (mDecls m)
    , Just (Range { from = start, to = start, source = "" })
    ]


data TopDecl  = Decl (TopLevel Decl)
              | TDNewtype (TopLevel Newtype)
              | Include (Located FilePath)
                deriving (Eq,Show)

data Decl     = DSignature [LQName] Schema
              | DPragma [LQName] Pragma
              | DBind Bind
              | DPatBind Pattern Expr
              | DType TySyn
              | DLocated Decl Range
                deriving (Eq,Show)

-- | An import declaration.
data Import = Import { iModule    :: ModName
                     , iAs        :: Maybe ModName
                     , iSpec      :: Maybe ImportSpec
                     } deriving (Eq,Show)

-- | The list of names following an import.
--
-- INVARIANT: All of the 'Name' entries in the list are expected to be
-- unqualified names; the 'QName' or 'NewName' constructors should not be
-- present.
data ImportSpec = Hiding [Name]
                | Only   [Name]
                  deriving (Eq,Show)

data TySyn    = TySyn LQName [TParam] Type
                deriving (Eq,Show)

{- | Bindings.  Notes:

    * The parser does not associate type signatures and pragmas with
      their bindings: this is done in a separate pass, after de-sugaring
      pattern bindings.  In this way we can associate pragmas and type
      signatures with the variables defined by pattern bindings as well.

    * Currently, there is no surface syntax for defining monomorphic
      bindings (i.e., bindings that will not be automatically generalized
      by the type checker.  However, they are useful when de-sugaring
      patterns.
-}
data Bind     = Bind { bName      :: LQName       -- ^ Defined thing
                     , bParams    :: [Pattern]    -- ^ Parameters
                     , bDef       :: Expr         -- ^ Definition
                     , bSignature :: Maybe Schema -- ^ Optional type sig
                     , bPragmas   :: [Pragma]     -- ^ Optional pragmas
                     , bMono      :: Bool  -- ^ Is this a monomorphic binding
                     } deriving (Eq,Show)

data Pragma   = PragmaNote String
              | PragmaProperty
                deriving (Eq,Show)

data Newtype  = Newtype { nName   :: LQName       -- ^ Type name
                        , nParams :: [TParam]     -- ^ Type params
                        , nBody   :: [Named Type] -- ^ Constructor
                        } deriving (Eq,Show)

-- | Input at the REPL, which can either be an expression or a @let@
-- statement.
data ReplInput = ExprInput Expr
               | LetInput Decl
                 deriving (Eq, Show)

-- | Export information for a declaration.
data ExportType = Public
                | Private
                  deriving (Eq,Show,Ord)

data TopLevel a = TopLevel { tlExport :: ExportType
                           , tlValue  :: a
                           } deriving (Show,Eq,Ord)

instance Functor TopLevel where
  fmap f tl = tl { tlValue = f (tlValue tl) }

data ExportSpec = ExportSpec { eTypes  :: Set.Set QName
                             , eBinds  :: Set.Set QName
                             } deriving (Show)

instance Monoid ExportSpec where
  mempty      = ExportSpec { eTypes = mempty, eBinds = mempty }
  mappend l r = ExportSpec { eTypes = mappend (eTypes l) (eTypes r)
                           , eBinds  = mappend (eBinds  l) (eBinds  r)
                           }

-- | Add a binding name to the export list, if it should be exported.
exportBind :: TopLevel QName -> ExportSpec
exportBind n
  | tlExport n == Public = mempty { eBinds = Set.singleton (tlValue n) }
  | otherwise            = mempty

-- | Check to see if a binding is exported.
isExportedBind :: QName -> ExportSpec -> Bool
isExportedBind n = Set.member n . eBinds

-- | Add a type synonym name to the export list, if it should be exported.
exportType :: TopLevel QName -> ExportSpec
exportType n
  | tlExport n == Public = mempty { eTypes = Set.singleton (tlValue n) }
  | otherwise            = mempty

-- | Check to see if a type synonym is exported.
isExportedType :: QName -> ExportSpec -> Bool
isExportedType n = Set.member n . eTypes

-- | Infromation about the representation of a numeric constant.
data NumInfo  = BinLit Int                      -- ^ n-digit binary literal
              | OctLit Int                      -- ^ n-digit octal  literal
              | DecLit                          -- ^ overloaded decimal literal
              | HexLit Int                      -- ^ n-digit hex literal
              | CharLit                         -- ^ character literal
              | PolyLit Int                     -- ^ polynomial literal
                deriving (Eq,Show)

-- | Literals.
data Literal  = ECNum Integer NumInfo           -- ^ @0x10@  (HexLit 2)
              | ECString String                 -- ^ @\"hello\"@
                deriving (Eq,Show)

data Expr     = EVar QName                      -- ^ @ x @
              | ECon ECon                       -- ^ @ split @
              | ELit Literal                    -- ^ @ 0x10 @
              | ETuple [Expr]                   -- ^ @ (1,2,3) @
              | ERecord [Named Expr]            -- ^ @ { x = 1, y = 2 } @
              | ESel Expr Selector              -- ^ @ e.l @
              | EList [Expr]                    -- ^ @ [1,2,3] @
              | EFromTo Type (Maybe Type) (Maybe Type)   -- ^ @[1, 5 ..  117 ] @
              | EInfFrom Expr (Maybe Expr)      -- ^ @ [1, 3 ...] @
              | EComp Expr [[Match]]            -- ^ @ [ 1 | x <- xs ] @
              | EApp Expr Expr                  -- ^ @ f x @
              | EAppT Expr [TypeInst]           -- ^ @ f `{x = 8}, f`{8} @
              | EIf Expr Expr Expr              -- ^ @ if ok then e1 else e2 @
              | EWhere Expr [Decl]              -- ^ @ 1 + x where { x = 2 } @
              | ETyped Expr Type                -- ^ @ 1 : [8] @
              | ETypeVal Type                   -- ^ @ `(x + 1)@, @x@ is a type
              | EFun [Pattern] Expr             -- ^ @ \\x y -> x @
              | ELocated Expr Range             -- ^ position annotation
                deriving (Eq,Show)

data TypeInst = NamedInst (Named Type)
              | PosInst Type
                deriving (Eq,Show)


{- | Selectors are used for projecting from various components.
Each selector has an option spec to specify the shape of the thing
that is being selected.  Currently, there is no surface syntax for
list selectors, but they are used during the desugaring of patterns.
-}

data Selector = TupleSel Int   (Maybe Int)
                -- ^ Zero-based tuple selection.
                -- Optionally specifies the shape of the tuple (one-based).

              | RecordSel Name (Maybe [Name])
                -- ^ Record selection.
                -- Optionally specifies the shape of the record.

              | ListSel Int    (Maybe Int)
                -- ^ List selection.
                -- Optionally specifies the length of the list.
                deriving (Eq,Show,Ord)

data Match    = Match Pattern Expr              -- ^ p <- e
              | MatchLet Bind
                deriving (Eq,Show)

data Pattern  = PVar LName                    -- ^ @ x @
              | PWild                         -- ^ @ _ @
              | PTuple [Pattern]              -- ^ @ (x,y,z) @
              | PRecord [ Named Pattern ]     -- ^ @ { x = (a,b,c), y = z } @
              | PList [ Pattern ]             -- ^ @ [ x, y, z ] @
              | PTyped Pattern Type           -- ^ @ x : [8] @
              | PSplit Pattern Pattern        -- ^ @ (x # y) @
              | PLocated Pattern Range        -- ^ Location information
                deriving (Eq,Show)


data Named a  = Named { name :: Located Name, value :: a }
                deriving (Eq,Show)

instance Functor Named where
  fmap f x = x { value = f (value x) }


data Schema   = Forall [TParam] [Prop] Type (Maybe Range)
                deriving (Eq,Show)

data Kind     = KNum | KType
                deriving (Eq,Show)

data TParam   = TParam { tpName  :: Name
                       , tpKind  :: Maybe Kind
                       , tpRange :: Maybe Range
                       }
                deriving (Eq,Show)

tpQName :: TParam -> QName
tpQName  = mkUnqual . tpName


data Type     = TFun Type Type          -- ^ @[8] -> [8]@
              | TSeq Type Type          -- ^ @[8] a@
              | TBit                    -- ^ @Bit@
              | TNum Integer            -- ^ @10@
              | TChar Char              -- ^ @'a'@
              | TInf                    -- ^ @inf@
              | TUser QName [Type]      -- ^ A type variable or synonym
              | TApp TFun [Type]        -- ^ @2 + x@
              | TRecord [Named Type]    -- ^ @{ x : [8], y : [32] }@
              | TTuple [Type]           -- ^ @([8], [32])@
              | TWild                   -- ^ @_@, just some type.
              | TLocated Type Range     -- ^ Location information
                deriving (Eq,Show)

data Prop     = CFin Type             -- ^ @ fin x   @
              | CEqual Type Type      -- ^ @ x == 10 @
              | CGeq Type Type        -- ^ @ x >= 10 @
              | CArith Type           -- ^ @ Arith a @
              | CCmp Type             -- ^ @ Cmp a @
              | CLocated Prop Range   -- ^ Location information
                deriving (Eq,Show)


--------------------------------------------------------------------------------
-- Note: When an explicit location is missing, we could use the sub-components
-- to try to estimate a location...


instance AddLoc Expr where
  addLoc = ELocated

  dropLoc (ELocated e _) = dropLoc e
  dropLoc e              = e

instance HasLoc Expr where
  getLoc (ELocated _ r) = Just r
  getLoc _              = Nothing

instance HasLoc TParam where
  getLoc (TParam _ _ r) = r

instance AddLoc TParam where
  addLoc (TParam a b _) l = TParam a b (Just l)
  dropLoc (TParam a b _)  = TParam a b Nothing

instance HasLoc Type where
  getLoc (TLocated _ r) = Just r
  getLoc _              = Nothing

instance AddLoc Type where
  addLoc = TLocated

  dropLoc (TLocated e _) = dropLoc e
  dropLoc e              = e

instance HasLoc Prop where
  getLoc (CLocated _ r) = Just r
  getLoc _              = Nothing

instance AddLoc Prop where
  addLoc = CLocated

  dropLoc (CLocated e _) = dropLoc e
  dropLoc e              = e

instance AddLoc Pattern where
  addLoc = PLocated

  dropLoc (PLocated e _) = dropLoc e
  dropLoc e              = e

instance HasLoc Pattern where
  getLoc (PLocated _ r) = Just r
  getLoc _              = Nothing

instance HasLoc Bind where
  getLoc b = getLoc (bName b, bDef b)

instance HasLoc Match where
  getLoc (Match p e)    = getLoc (p,e)
  getLoc (MatchLet b)   = getLoc b

instance HasLoc a => HasLoc (Named a) where
  getLoc l = getLoc (name l, value l)

instance HasLoc Schema where
  getLoc (Forall _ _ _ r) = r

instance AddLoc Schema where
  addLoc  (Forall xs ps t _) r = Forall xs ps t (Just r)
  dropLoc (Forall xs ps t _)   = Forall xs ps t Nothing

instance HasLoc Decl where
  getLoc (DLocated _ r) = Just r
  getLoc _              = Nothing

instance AddLoc Decl where
  addLoc d r             = DLocated d r

  dropLoc (DLocated d _) = dropLoc d
  dropLoc d              = d

instance HasLoc a => HasLoc (TopLevel a) where
  getLoc = getLoc . tlValue

instance HasLoc TopDecl where
  getLoc td = case td of
    Decl tld    -> getLoc tld
    TDNewtype n -> getLoc n
    Include lfp -> getLoc lfp

instance HasLoc Module where
  getLoc m
    | null locs = Nothing
    | otherwise = Just (rCombs locs)
    where
    locs = catMaybes [ getLoc (mName m)
                     , getLoc (mImports m)
                     , getLoc (mDecls m)
                     ]

instance HasLoc Newtype where
  getLoc n
    | null locs = Nothing
    | otherwise = Just (rCombs locs)
    where
    locs = catMaybes [ getLoc (nName n), getLoc (nBody n) ]


--------------------------------------------------------------------------------





--------------------------------------------------------------------------------
-- Pretty printing


ppL :: PP a => Located a -> Doc
ppL = pp . thing

ppNamed :: PP a => String -> Named a -> Doc
ppNamed s x = ppL (name x) <+> text s <+> pp (value x)


instance PP Module where
  ppPrec _ m = text "module" <+> ppL (mName m) <+> text "where"
            $$ vcat (map ppL (mImports m))
            $$ vcat (map pp (mDecls m))

instance PP Program where
  ppPrec _ (Program ds) = vcat (map pp ds)

instance PP TopDecl where
  ppPrec _ top_decl =
    case top_decl of
      Decl    d   -> pp d
      TDNewtype n -> pp n
      Include l   -> text "include" <+> text (show (thing l))

instance PP Decl where
  ppPrec n decl =
    case decl of
      DSignature xs s -> commaSep (map ppL xs) <+> text ":" <+> pp s
      DPatBind p e    -> pp p <+> text "=" <+> pp e
      DBind b         -> ppPrec n b
      DPragma xs p    -> ppPragma xs p
      DType ts        -> ppPrec n ts
      DLocated d _    -> ppPrec n d

instance PP Newtype where
  ppPrec _ nt = hsep
    [ text "newtype", ppL (nName nt), hsep (map pp (nParams nt)), char '='
    , braces (commaSep (map (ppNamed ":") (nBody nt))) ]

instance PP Import where
  ppPrec _ d = text "import" <+> sep [ pp (iModule d), mbAs, mbSpec ]
    where
    mbAs = maybe empty (\ name -> text "as" <+> pp name ) (iAs d)

    mbSpec = maybe empty pp (iSpec d)

instance PP ImportSpec where
  ppPrec _ s = case s of
    Hiding names -> text "hiding" <+> parens (commaSep (map pp names))
    Only names   ->                   parens (commaSep (map pp names))

-- TODO: come up with a good way of showing the export specification here
instance PP a => PP (TopLevel a) where
  ppPrec _ tl = pp (tlValue tl)


instance PP Pragma where
  ppPrec _ (PragmaNote x) = text x
  ppPrec _ PragmaProperty = text "property"

ppPragma :: [LQName] -> Pragma -> Doc
ppPragma xs p =
  text "/*" <+> text "pragma" <+> commaSep (map ppL xs) <+> text ":" <+> pp p
  <+> text "*/"

instance PP Bind where
  ppPrec _ b = sig $$ vcat [ ppPragma [f] p | p <- bPragmas b ] $$
               hang (lhs <+> eq) 4 (pp (bDef b))
    where f = bName b
          sig = case bSignature b of
                  Nothing -> empty
                  Just s  -> pp (DSignature [f] s)
          eq  = if bMono b then text ":=" else text "="
          lhs = ppL f <+> fsep (map (ppPrec 3) (bParams b))


instance PP TySyn where
  ppPrec _ (TySyn x xs t) = text "type" <+> ppL x <+> fsep (map (ppPrec 1) xs)
                                        <+> text "=" <+> pp t

instance PP ModName where
  ppPrec _ (ModName ns) = hcat (punctuate (text "::") (map text ns))

instance PP QName where
  ppPrec _ (QName mb n) = mbNs <> pp n
    where
    mbNs = maybe empty (\ mn -> pp mn <> text "::") mb

instance PP Name where
  ppPrec _ (Name x)       = text x
  -- XXX: This may clash with user-specified names.
  ppPrec _ (NewName p x)  = text "__" <> passName p <> int x

passName :: Pass -> Doc
passName pass =
  case pass of
    NoPat       -> text "p"
    MonoValues  -> text "mv"

instance PP Literal where
  ppPrec _ lit =
    case lit of
      ECNum n i     -> ppNumLit n i
      ECString s    -> text (show s)


ppNumLit :: Integer -> NumInfo -> Doc
ppNumLit n info =
  case info of
    DecLit    -> integer n
    CharLit   -> text (show (toEnum (fromInteger n) :: Char))
    BinLit w  -> pad 2  "0b" w
    OctLit w  -> pad 8  "0o" w
    HexLit w  -> pad 16 "0x" w
    PolyLit w -> text "<|" <+> poly w <+> text "|>"
  where
  pad base pref w =
    let txt = showIntAtBase base ("0123456789abcdef" !!) n ""
    in text pref <> text (replicate (w - length txt) '0') <> text txt

  poly w = let (res,deg) = bits Nothing [] 0 n
               z | w == 0 = []
                 | Just d <- deg, d + 1 == w = []
                 | otherwise = [polyTerm0 (w-1)]
           in fsep $ intersperse (text "+") $ z ++ map polyTerm res

  polyTerm 0 = text "1"
  polyTerm 1 = text "x"
  polyTerm p = text "x" <> text "^^" <> int p

  polyTerm0 0 = text "0"
  polyTerm0 p = text "0" <> text "*" <> polyTerm p

  bits d res p num
    | num == 0  = (res,d)
    | even num  = bits d             res  (p + 1) (num `shiftR` 1)
    | otherwise = bits (Just p) (p : res) (p + 1) (num `shiftR` 1)

wrap :: Int -> Int -> Doc -> Doc
wrap contextPrec myPrec doc = if myPrec < contextPrec then parens doc else doc

-- | Succeeds if the expression is an infix operator.
isInfixOp :: Expr -> Maybe (ECon, Assoc, Int)
isInfixOp (ELocated e _)  = isInfixOp e
isInfixOp (ECon x)        = do (a,p) <- Map.lookup x eBinOpPrec
                               return (x,a,p)
isInfixOp _               = Nothing

isPrefixOp :: Expr -> Maybe ECon
isPrefixOp (ELocated e _)                        = isPrefixOp e
isPrefixOp (ECon x) | x == ECNeg || x == ECCompl = Just x
isPrefixOp _                                     = Nothing

isEApp :: Expr -> Maybe (Expr, Expr)
isEApp (ELocated e _)     = isEApp e
isEApp (EApp e1 e2)       = Just (e1,e2)
isEApp _                  = Nothing

asEApps :: Expr -> (Expr, [Expr])
asEApps expr = go expr []
    where go e es = case isEApp e of
                      Nothing       -> (e, es)
                      Just (e1, e2) -> go e1 (e2 : es)

isEInfix :: Expr -> Maybe (Infix ECon Expr)
isEInfix e =
  do (e1,ieRight) <- isEApp e
     (f,ieLeft)   <- isEApp e1
     (ieOp,ieAssoc,iePrec) <- isInfixOp f
     return Infix { .. }

isTInfix :: Type -> Maybe (Infix TFun Type)
isTInfix (TLocated t _)  = isTInfix t
isTInfix (TApp ieOp [ieLeft,ieRight]) =
  do (ieAssoc,iePrec) <- Map.lookup ieOp tBinOpPrec
     return Infix { .. }
isTInfix _               = Nothing

instance PP TypeInst where
  ppPrec _ (PosInst t)   = pp t
  ppPrec _ (NamedInst x) = ppNamed "=" x

{- Precedences:
0: lambda, if, where, type annotation
2: infix expression   (separate precedence table)
3: application, prefix expressions
-}
instance PP Expr where
  -- Wrap if top level operator in expression is less than `n`
  ppPrec n expr =
    case expr of

      -- atoms
      EVar x        -> pp x
      ECon x        -> ppPrefix x
      ELit x        -> pp x
      ETuple es     -> parens (commaSep (map pp es))
      ERecord fs    -> braces (commaSep (map (ppNamed "=") fs))
      EList es      -> brackets (commaSep (map pp es))
      EFromTo e1 e2 e3 -> brackets (pp e1 <> step <+> text ".." <+> end)
        where step = maybe empty (\e -> comma <+> pp e) e2
              end  = maybe empty pp e3
      EInfFrom e1 e2 -> brackets (pp e1 <> step <+> text "...")
        where step = maybe empty (\e -> comma <+> pp e) e2
      EComp e mss   -> brackets (pp e <+> vcat (map arm mss))
        where arm ms = text "|" <+> commaSep (map pp ms)
      ETypeVal t    -> text "`" <> ppPrec 5 t     -- XXX
      EAppT e ts    -> ppPrec 4 e <> text "`" <> braces (commaSep (map pp ts))
      ESel    e l   -> ppPrec 4 e <> text "." <> pp l

      -- low prec
      EFun xs e     -> wrap n 0 (text "\\" <> hsep (map (ppPrec 3) xs) <+>
                                 text "->" <+> pp e)

      EIf e1 e2 e3  -> wrap n 0 $ sep [ text "if"   <+> pp e1
                                      , text "then" <+> pp e2
                                      , text "else" <+> pp e3 ]

      ETyped e t    -> wrap n 0 (ppPrec 2 e <+> text ":" <+> pp t)

      EWhere  e ds  -> wrap n 0 (pp e
                                $$ text "where"
                                $$ nest 2 (vcat (map pp ds))
                                $$ text "")


      -- applications
      _ | Just einf <- isEInfix expr
                    -> optParens (n>2) $ ppInfix 2 isEInfix einf

      EApp e1 e2
        | Just op <- isPrefixOp e1
                    -> wrap n 3 (pp op <> ppPrec 3 e2)

      EApp _ _      -> let (e, es) = asEApps expr in
                       wrap n 3 (ppPrec 3 e <+> fsep (map (ppPrec 4) es))

      ELocated e _  -> ppPrec n e

instance PP Selector where
  ppPrec _ sel =
    case sel of
      TupleSel x sig    -> int x <+> ppSig tupleSig sig
      RecordSel x sig  -> pp x  <+> ppSig recordSig sig
      ListSel x sig    -> int x <+> ppSig listSig sig

    where
    tupleSig n   = int n
    recordSig xs = braces $ fsep $ punctuate comma $ map pp xs
    listSig n    = int n

    ppSig f = maybe empty (\x -> text "/* of" <+> f x <+> text "*/")


-- | Display the thing selected by the selector, nicely.
ppSelector :: Selector -> Doc
ppSelector sel =
  case sel of
    TupleSel x _  -> ordinal x <+> text "field"
    RecordSel x _ -> text "field" <+> pp x
    ListSel x _   -> ordinal x <+> text "element"



instance PP Pattern where
  ppPrec n pat =
    case pat of
      PVar x        -> pp (thing x)
      PWild         -> char '_'
      PTuple ps     -> parens   (commaSep (map pp ps))
      PRecord fs    -> braces   (commaSep (map (ppNamed "=") fs))
      PList ps      -> brackets (commaSep (map pp ps))
      PTyped p t    -> wrap n 0 (ppPrec 1 p  <+> text ":" <+> pp t)
      PSplit p1 p2  -> wrap n 1 (ppPrec 1 p1 <+> text "#" <+> ppPrec 1 p2)
      PLocated p _  -> ppPrec n p

instance PP Match where
  ppPrec _ (Match p e)  = pp p <+> text "<-" <+> pp e
  ppPrec _ (MatchLet b) = pp b


instance PP Schema where
  ppPrec _ (Forall xs ps t _) = sep [vars <+> preds, pp t]
    where vars = case xs of
                   [] -> empty
                   _  -> braces (commaSep (map pp xs))
          preds = case ps of
                    [] -> empty
                    _  -> parens (commaSep (map pp ps)) <+> text "=>"

instance PP Kind where
  ppPrec _ KType  = text "*"
  ppPrec _ KNum   = text "#"

-- | "Conversational" printing of kinds (e.g., to use in error messages)
cppKind :: Kind -> Doc
cppKind KType = text "a value type"
cppKind KNum  = text "a numeric type"

instance PP TParam where
  ppPrec n (TParam p Nothing _)   = ppPrec n p
  ppPrec n (TParam p (Just k) _)  = wrap n 1 (pp p <+> text ":" <+> pp k)

-- 4: wrap [_] t
-- 3: wrap application
-- 2: wrap function
-- 1:
instance PP Type where
  ppPrec n ty =
    case ty of
      TWild          -> text "_"
      TTuple ts      -> parens $ commaSep $ map pp ts
      TRecord fs     -> braces $ commaSep $ map (ppNamed ":") fs
      TBit           -> text "Bit"
      TInf           -> text "inf"
      TNum x         -> integer x
      TChar x        -> text (show x)
      TSeq t1 TBit   -> brackets (pp t1)
      TSeq t1 t2     -> optParens (n > 3)
                      $ brackets (pp t1) <> ppPrec 3 t2

      TApp _ [_,_]
        | Just tinf <- isTInfix ty
                     -> optParens (n > 2)
                      $ ppInfix 2 isTInfix tinf

      TApp f ts      -> optParens (n > 2)
                      $ pp f <+> fsep (map (ppPrec 4) ts)

      TUser f []     -> pp f

      TUser f ts     -> optParens (n > 2)
                      $ pp f <+> fsep (map (ppPrec 4) ts)

      TFun t1 t2     -> optParens (n > 1)
                      $ sep [ppPrec 2 t1 <+> text "->", ppPrec 1 t2]

      TLocated t _   -> ppPrec n t

instance PP Prop where
  ppPrec n prop =
    case prop of
      CFin t       -> text "fin"   <+> ppPrec 4 t
      CArith t     -> text "Arith" <+> ppPrec 4 t
      CCmp t       -> text "Cmp"   <+> ppPrec 4 t
      CEqual t1 t2 -> ppPrec 2 t1 <+> text "==" <+> ppPrec 2 t2
      CGeq t1 t2   -> ppPrec 2 t1 <+> text ">=" <+> ppPrec 2 t2
      CLocated c _ -> ppPrec n c


--------------------------------------------------------------------------------
-- Drop all position information, so equality reflects program structure

class NoPos t where
  noPos :: t -> t

-- WARNING: This does not call `noPos` on the `thing` inside
instance NoPos (Located t) where
  noPos x = x { srcRange = rng }
    where rng = Range { from = Position 0 0, to = Position 0 0, source = "" }

instance NoPos t => NoPos (Named t) where
  noPos t = Named { name = noPos (name t), value = noPos (value t) }

instance NoPos t => NoPos [t]       where noPos = fmap noPos
instance NoPos t => NoPos (Maybe t) where noPos = fmap noPos

instance NoPos Program where
  noPos (Program x) = Program (noPos x)

instance NoPos Module where
  noPos m = Module { mName    = mName m
                   , mImports = noPos (mImports m)
                   , mDecls   = noPos (mDecls m)
                   }

instance NoPos TopDecl where
  noPos decl =
    case decl of
      Decl    x   -> Decl     (noPos x)
      TDNewtype n -> TDNewtype(noPos n)
      Include x   -> Include  (noPos x)

instance NoPos a => NoPos (TopLevel a) where
  noPos tl = tl { tlValue = noPos (tlValue tl) }

instance NoPos Decl where
  noPos decl =
    case decl of
      DSignature x y   -> DSignature (noPos x) (noPos y)
      DPragma    x y   -> DPragma    (noPos x) (noPos y)
      DPatBind   x y   -> DPatBind   (noPos x) (noPos y)
      DBind      x     -> DBind      (noPos x)
      DType      x     -> DType      (noPos x)
      DLocated   x _   -> noPos x

instance NoPos Newtype where
  noPos n = Newtype { nName   = noPos (nName n)
                    , nParams = nParams n
                    , nBody   = noPos (nBody n)
                    }

instance NoPos Bind where
  noPos x = Bind { bName      = noPos (bName      x)
                 , bParams    = noPos (bParams    x)
                 , bDef       = noPos (bDef       x)
                 , bSignature = noPos (bSignature x)
                 , bPragmas   = noPos (bPragmas   x)
                 , bMono      = bMono x
                 }

instance NoPos Pragma where
  noPos p@(PragmaNote {})   = p
  noPos p@(PragmaProperty)  = p




instance NoPos TySyn where
  noPos (TySyn x y z) = TySyn (noPos x) (noPos y) (noPos z)

instance NoPos Expr where
  noPos expr =
    case expr of
      EVar x        -> EVar     x
      ECon x        -> ECon     x
      ELit x        -> ELit     x
      ETuple x      -> ETuple   (noPos x)
      ERecord x     -> ERecord  (noPos x)
      ESel x y      -> ESel     (noPos x) y
      EList x       -> EList    (noPos x)
      EFromTo x y z -> EFromTo  (noPos x) (noPos y) (noPos z)
      EInfFrom x y  -> EInfFrom (noPos x) (noPos y)
      EComp x y     -> EComp    (noPos x) (noPos y)
      EApp  x y     -> EApp     (noPos x) (noPos y)
      EAppT x y     -> EAppT    (noPos x) (noPos y)
      EIf   x y z   -> EIf      (noPos x) (noPos y) (noPos z)
      EWhere x y    -> EWhere   (noPos x) (noPos y)
      ETyped x y    -> ETyped   (noPos x) (noPos y)
      ETypeVal x    -> ETypeVal (noPos x)
      EFun x y      -> EFun     (noPos x) (noPos y)
      ELocated x _  -> noPos x

instance NoPos TypeInst where
  noPos (PosInst ts)   = PosInst (noPos ts)
  noPos (NamedInst fs) = NamedInst (noPos fs)

instance NoPos Match where
  noPos (Match x y)  = Match (noPos x) (noPos y)
  noPos (MatchLet b) = MatchLet (noPos b)

instance NoPos Pattern where
  noPos pat =
    case pat of
      PVar x       -> PVar    (noPos x)
      PWild        -> PWild
      PTuple x     -> PTuple  (noPos x)
      PRecord x    -> PRecord (noPos x)
      PList x      -> PList   (noPos x)
      PTyped x y   -> PTyped  (noPos x) (noPos y)
      PSplit x y   -> PSplit  (noPos x) (noPos y)
      PLocated x _ -> noPos x

instance NoPos Schema where
  noPos (Forall x y z _) = Forall (noPos x) (noPos y) (noPos z) Nothing

instance NoPos TParam where
  noPos (TParam x y _)  = TParam x y Nothing

instance NoPos Type where
  noPos ty =
    case ty of
      TWild         -> TWild
      TApp x y      -> TApp     x         (noPos y)
      TUser x y     -> TUser    x         (noPos y)
      TRecord x     -> TRecord  (noPos x)
      TTuple x      -> TTuple   (noPos x)
      TFun x y      -> TFun     (noPos x) (noPos y)
      TSeq x y      -> TSeq     (noPos x) (noPos y)
      TBit          -> TBit
      TInf          -> TInf
      TNum n        -> TNum n
      TChar n       -> TChar n
      TLocated x _  -> noPos x

instance NoPos Prop where
  noPos prop =
    case prop of
      CEqual  x y   -> CEqual  (noPos x) (noPos y)
      CGeq x y      -> CGeq (noPos x) (noPos y)
      CFin x        -> CFin (noPos x)
      CArith x      -> CArith (noPos x)
      CCmp x        -> CCmp   (noPos x)
      CLocated c _  -> noPos c


