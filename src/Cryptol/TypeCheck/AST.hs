-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe                                #-}
{-# LANGUAGE RecordWildCards                     #-}
{-# LANGUAGE PatternGuards                       #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
module Cryptol.TypeCheck.AST
  ( module Cryptol.TypeCheck.AST
  , TFun(..)
  , Name(..), QName(..), mkUnqual, unqual
  , ModName(..)
  , Selector(..)
  , Import(..)
  , ImportSpec(..)
  , ExportType(..)
  , ExportSpec(..), isExportedBind, isExportedType
  , Pragma(..)
  ) where

import Cryptol.Prims.Syntax
import Cryptol.Parser.AST ( Name(..), Selector(..),Pragma(..), ppSelector
                          , Import(..), ImportSpec(..), ExportType(..)
                          , ExportSpec(..), ModName(..), isExportedBind
                          , isExportedType, QName(..), mkUnqual, unqual )
import Cryptol.Utils.Panic(panic)
import Cryptol.TypeCheck.PP

import           Data.Map    (Map)
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import           Data.Set (Set)

{- | A Cryptol module.
-}
data Module = Module { mName     :: ModName
                     , mExports  :: ExportSpec
                     , mImports  :: [Import]
                     , mTySyns   :: Map QName TySyn
                     , mNewtypes :: Map QName Newtype
                     , mDecls    :: [DeclGroup]
                     } deriving Show


-- | Kinds, classify types.
data Kind   = KType
            | KNum
            | KProp
            | Kind :-> Kind
              deriving (Eq,Show)
infixr 5 :->


-- | The types of polymorphic values.
data Schema = Forall { sVars :: [TParam], sProps :: [Prop], sType :: Type }
              deriving (Eq, Show)

-- | Type synonym.
data TySyn  = TySyn { tsName        :: QName      -- ^ Name
                    , tsParams      :: [TParam]   -- ^ Parameters
                    , tsConstraints :: [Prop]     -- ^ Ensure body is OK
                    , tsDef         :: Type       -- ^ Definition
                    }
              deriving (Eq, Show)

-- | Named records
data Newtype  = Newtype { ntName   :: QName
                        , ntParams :: [TParam]
                        , ntConstraints :: [Prop]
                        , ntFields :: [(Name,Type)]
                        } deriving (Show)

-- | Type parameters.
data TParam = TParam { tpUnique :: !Int       -- ^ Parameter identifier
                     , tpKind   :: Kind       -- ^ Kind of parameter
                     , tpName   :: Maybe QName-- ^ Name from source, if any.
                     }
              deriving (Show)

instance Eq TParam where
  x == y = tpUnique x == tpUnique y

instance Ord TParam where
  compare x y = compare (tpUnique x) (tpUnique y)

tpVar :: TParam -> TVar
tpVar p = TVBound (tpUnique p) (tpKind p)

-- | The internal representation of types.
-- These are assumed to be kind correct.
data Type   = TCon TCon [Type]
              -- ^ Type constant with args

            | TVar TVar
              -- ^ Type variable (free or bound)

            | TUser QName [Type] Type
              {- ^ This is just a type annotation, for a type that
              was written as a type synonym.  It is useful so that we
              can use it to report nicer errors.
              Example: `TUser T ts t` is really just the type `t` that
              was written as `T ts` by the user. -}

            | TRec [(Name,Type)]
              -- ^ Record type

              deriving (Show,Eq,Ord)

-- | The type is supposed to be of kind `KProp`
type Prop   = Type

-- | The type is "simple" (i.e., it contains no type functions).
type SType  = Type


-- | Type variables.
data TVar   = TVFree !Int Kind (Set TVar) Doc
              -- ^ Unique, kind, ids of bound type variables that are in scope
              -- The `Doc` is a description of how this type came to be.


            | TVBound !Int Kind
              deriving Show

-- | Type constants.
data TCon   = TC TC | PC PC | TF TFun
              deriving (Show,Eq,Ord)

-- | Built-in type constants.

-- | Predicate symbols.
data PC     = PEqual        -- ^ @_ == _@
            | PNeq          -- ^ @_ /= _@
            | PGeq          -- ^ @_ >= _@
            | PFin          -- ^ @fin _@

            -- classes
            | PHas Selector -- ^ @Has sel type field@ does not appear in schemas
            | PArith        -- ^ @Arith _@
            | PCmp          -- ^ @Cmp _@
              deriving (Show,Eq,Ord)

-- | 1-1 constants.
data TC     = TCNum Integer            -- ^ Numbers
            | TCInf                    -- ^ Inf
            | TCBit                    -- ^ Bit
            | TCSeq                    -- ^ @[_] _@
            | TCFun                    -- ^ @_ -> _@
            | TCTuple Int              -- ^ @(_, _, _)@
            | TCNewtype UserTC         -- ^ user-defined, @T@
              deriving (Show,Eq,Ord)

data UserTC = UserTC QName Kind
                deriving Show

instance Eq UserTC where
  UserTC x _ == UserTC y _ = x == y

instance Ord UserTC where
  compare (UserTC x _) (UserTC y _) = compare x y

instance Eq TVar where
  TVBound x _     == TVBound y _     = x == y
  TVFree  x _ _ _ == TVFree  y _ _ _ = x == y
  _             == _              = False

instance Ord TVar where
  compare (TVFree x _ _ _) (TVFree y _ _ _) = compare x y
  compare (TVFree _ _ _ _) _                = LT
  compare _            (TVFree _ _ _ _)     = GT

  compare (TVBound x _) (TVBound y _)       = compare x y



data Expr   = ECon ECon                 -- ^ Built-in constant

            | EList [Expr] Type         -- ^ List value (with type of elements)
            | ETuple [Expr]             -- ^ Tuple value
            | ERec [(Name,Expr)]        -- ^ Record value
            | ESel Expr Selector        -- ^ Elimination for tuple/record/list

            | EIf Expr Expr Expr        -- ^ If-then-else
            | EComp Type Expr [[Match]] -- ^ List comprehensions
                                        --   The type caches the type of the
                                        --   expr.

            | EVar QName                -- ^ Use of a bound variable

            | ETAbs TParam Expr         -- ^ Function Value
            | ETApp Expr Type           -- ^ Type application

            | EApp Expr Expr            -- ^ Function application
            | EAbs QName Type Expr      -- ^ Function value


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

            {- | if e : t1, then cast e : t2
                 as long as we can prove that 't1 = t2'.
                 We could express this in terms of a built-in constant.
                 `cast :: {a,b} (a =*= b) => a -> b`

                 Using the constant is a bit verbose though, because we
                 end up with both the source and target type. So, instead
                 we use this language construct, which only stores the
                 target type, and the source type can be reconstructed
                 from the expression.

                 Another way to think of this is simply as an expression
                 with an explicit type annotation.
              -}
            | ECast Expr Type


            | EWhere Expr [DeclGroup]

              deriving Show


data Match  = From QName Type Expr-- ^ do we need this type?  it seems like it
                                  --   can be computed from the expr
            | Let Decl
              deriving Show



data DeclGroup  = Recursive   [Decl]    -- ^ Mutually recursive declarations
                | NonRecursive Decl     -- ^ Non-recursive declaration
                  deriving Show

groupDecls :: DeclGroup -> [Decl]
groupDecls dg = case dg of
  Recursive ds   -> ds
  NonRecursive d -> [d]

data Decl       = Decl { dName        :: QName
                       , dSignature   :: Schema
                       , dDefinition  :: Expr
                       , dPragmas     :: [Pragma]
                       } deriving (Show)



--------------------------------------------------------------------------------


isFreeTV :: TVar -> Bool
isFreeTV (TVFree {}) = True
isFreeTV _           = False

isBoundTV :: TVar -> Bool
isBoundTV (TVBound {})  = True
isBoundTV _             = False


--------------------------------------------------------------------------------
tIsNum :: Type -> Maybe Integer
tIsNum ty = case tNoUser ty of
              TCon (TC (TCNum x)) [] -> Just x
              _                      -> Nothing

tIsInf :: Type -> Bool
tIsInf ty = case tNoUser ty of
              TCon (TC TCInf) [] -> True
              _                  -> False

tIsVar :: Type -> Maybe TVar
tIsVar ty = case tNoUser ty of
              TVar x -> Just x
              _      -> Nothing

tIsFun :: Type -> Maybe (Type, Type)
tIsFun ty = case tNoUser ty of
              TCon (TC TCFun) [a, b] -> Just (a, b)
              _                      -> Nothing

tIsSeq :: Type -> Maybe (Type, Type)
tIsSeq ty = case tNoUser ty of
              TCon (TC TCSeq) [n, a] -> Just (n, a)
              _                      -> Nothing

tIsBit :: Type -> Bool
tIsBit ty = case tNoUser ty of
              TCon (TC TCBit) [] -> True
              _                  -> False

tIsTuple :: Type -> Maybe [Type]
tIsTuple ty = case tNoUser ty of
                TCon (TC (TCTuple _)) ts -> Just ts
                _                        -> Nothing

pIsFin :: Prop -> Maybe Type
pIsFin ty = case tNoUser ty of
              TCon (PC PFin) [t1] -> Just t1
              _                   -> Nothing

pIsGeq :: Prop -> Maybe (Type,Type)
pIsGeq ty = case tNoUser ty of
              TCon (PC PGeq) [t1,t2] -> Just (t1,t2)
              _                      -> Nothing

pIsEq :: Prop -> Maybe (Type,Type)
pIsEq ty = case tNoUser ty of
             TCon (PC PEqual) [t1,t2] -> Just (t1,t2)
             _                        -> Nothing

pIsArith :: Prop -> Maybe Type
pIsArith ty = case tNoUser ty of
                TCon (PC PArith) [t1] -> Just t1
                _                     -> Nothing

pIsCmp :: Prop -> Maybe Type
pIsCmp ty = case tNoUser ty of
              TCon (PC PCmp) [t1] -> Just t1
              _                   -> Nothing



pIsNumeric :: Prop -> Bool
pIsNumeric (TCon (PC PEqual) _) = True
pIsNumeric (TCon (PC PNeq) _)   = True
pIsNumeric (TCon (PC PGeq) _)   = True
pIsNumeric (TCon (PC PFin) _)   = True
pIsNumeric (TUser _ _ t)        = pIsNumeric t
pIsNumeric _                    = False





--------------------------------------------------------------------------------
tNum     :: Integral a => a -> Type
tNum n    = TCon (TC (TCNum (fromIntegral n))) []

tZero     :: Type
tZero     = tNum (0 :: Int)

tOne     :: Type
tOne      = tNum (1 :: Int)

tTwo     :: Type
tTwo      = tNum (2 :: Int)

tInf     :: Type
tInf      = TCon (TC TCInf) []

tBit     :: Type
tBit      = TCon (TC TCBit) []

eTrue    :: Expr
eTrue     = ECon ECTrue

eFalse   :: Expr
eFalse    = ECon ECFalse

tWord    :: Type -> Type
tWord a   = tSeq a tBit

tSeq     :: Type -> Type -> Type
tSeq a b  = TCon (TC TCSeq) [a,b]

tChar :: Type
tChar = tWord (tNum (8 :: Int))

eChar :: Char -> Expr
eChar c = ETApp (ETApp (ECon ECDemote) (tNum v)) (tNum w)
  where v = fromEnum c
        w = 8 :: Int

tString :: Int -> Type
tString len = tSeq (tNum len) tChar

eString :: String -> Expr
eString str = EList (map eChar str) tChar

-- | Make an expression that is `error` pre-applied to a type and a
-- message.
eError :: Type -> String -> Expr
eError t str =
  EApp (ETApp (ETApp (ECon ECError) t) (tNum (length str))) (eString str)

tRec     :: [(Name,Type)] -> Type
tRec      = TRec

tTuple   :: [Type] -> Type
tTuple ts = TCon (TC (TCTuple (length ts))) ts


infixr 5 `tFun`

-- | Make a function type.
tFun     :: Type -> Type -> Type
tFun a b  = TCon (TC TCFun) [a,b]

-- | Eliminate type synonyms.
tNoUser  :: Type -> Type
tNoUser t = case t of
              TUser _ _ a -> tNoUser a
              _           -> t

tWidth  :: Type -> Type
tWidth t  = TCon (TF TCWidth) [t]

tLenFromThen :: Type -> Type -> Type -> Type
tLenFromThen t1 t2 t3 = TCon (TF TCLenFromThen) [t1,t2,t3]

tLenFromThenTo :: Type -> Type -> Type -> Type
tLenFromThenTo t1 t2 t3 = TCon (TF TCLenFromThenTo) [t1,t2,t3]

tMax :: Type -> Type -> Type
tMax t1 t2 = TCon (TF TCMax) [t1,t2]

infix 4 =#=, >==
infixl 6 .+.
infixl 7 .*.

-- | Equality for numeric types.
(=#=) :: Type -> Type -> Prop
x =#= y = TCon (PC PEqual) [x,y]

(=/=) :: Type -> Type -> Prop
x =/= y = TCon (PC PNeq) [x,y]

pArith :: Type -> Prop
pArith t = TCon (PC PArith) [t]

pCmp :: Type -> Prop
pCmp t = TCon (PC PCmp) [t]

-- | Make a greater-than-or-equal-to constraint.
(>==) :: Type -> Type -> Prop
x >== y = TCon (PC PGeq) [x,y]

-- | A `Has` constraint, used for tuple and record selection.
pHas :: Selector -> Type -> Type -> Prop
pHas l ty fi = TCon (PC (PHas l)) [ty,fi]

pFin :: Type -> Prop
pFin ty = TCon (PC PFin) [ty]



-- | Make multiplication type.
(.*.) :: Type -> Type -> Type
x .*. y = TCon (TF TCMul) [x,y]

-- | Make addition type.
(.+.) :: Type -> Type -> Type
x .+. y = TCon (TF TCAdd) [x,y]

(.-.) :: Type -> Type -> Type
x .-. y = TCon (TF TCSub) [x,y]

(.^.) :: Type -> Type -> Type
x .^. y = TCon (TF TCExp) [x,y]

tDiv :: Type -> Type -> Type
tDiv x y = TCon (TF TCDiv) [x,y]

tMod :: Type -> Type -> Type
tMod x y = TCon (TF TCMod) [x,y]

-- | Make a @min@ type.
tMin :: Type -> Type -> Type
tMin x y = TCon (TF TCMin) [x,y]


newtypeTyCon :: Newtype -> TCon
newtypeTyCon nt = TC $ TCNewtype $ UserTC (ntName nt) (kindOf nt)

newtypeConType :: Newtype -> Schema
newtypeConType nt =
  Forall as (ntConstraints nt)
    $ TRec (ntFields nt) `tFun` TCon (newtypeTyCon nt) (map (TVar . tpVar) as)
  where
  as = ntParams nt

--------------------------------------------------------------------------------

class HasKind t where
  kindOf :: t -> Kind

instance HasKind TVar where
  kindOf (TVFree  _ k _ _) = k
  kindOf (TVBound _ k) = k

instance HasKind TCon where
  kindOf (TC tc) = kindOf tc
  kindOf (PC pc) = kindOf pc
  kindOf (TF tf) = kindOf tf

instance HasKind UserTC where
  kindOf (UserTC _ k) = k

instance HasKind TC where
  kindOf tcon =
    case tcon of
      TCNum _   -> KNum
      TCInf     -> KNum
      TCBit     -> KType
      TCSeq     -> KNum :-> KType :-> KType
      TCFun     -> KType :-> KType :-> KType
      TCTuple n -> foldr (:->) KType (replicate n KType)
      TCNewtype x -> kindOf x

instance HasKind PC where
  kindOf pc =
    case pc of
      PEqual    -> KNum :-> KNum :-> KProp
      PNeq      -> KNum :-> KNum :-> KProp
      PGeq      -> KNum :-> KNum :-> KProp
      PFin      -> KNum :-> KProp
      PHas _    -> KType :-> KType :-> KProp
      PArith    -> KType :-> KProp
      PCmp      -> KType :-> KProp

instance HasKind TFun where
  kindOf tfun =
    case tfun of
      TCWidth  -> KNum :-> KNum
      TCLg2    -> KNum :-> KNum

      TCAdd    -> KNum :-> KNum :-> KNum
      TCSub    -> KNum :-> KNum :-> KNum
      TCMul    -> KNum :-> KNum :-> KNum
      TCDiv    -> KNum :-> KNum :-> KNum
      TCMod    -> KNum :-> KNum :-> KNum
      TCExp    -> KNum :-> KNum :-> KNum
      TCMin    -> KNum :-> KNum :-> KNum
      TCMax    -> KNum :-> KNum :-> KNum

      TCLenFromThen   -> KNum :-> KNum :-> KNum :-> KNum
      TCLenFromThenTo -> KNum :-> KNum :-> KNum :-> KNum

instance HasKind Type where
  kindOf ty =
    case ty of
      TVar a      -> kindOf a
      TCon c ts   -> quickApply (kindOf c) ts
      TUser _ _ t -> kindOf t
      TRec {}     -> KType

instance HasKind TySyn where
  kindOf (TySyn _ as _ t) = foldr (:->) (kindOf t) (map kindOf as)

instance HasKind Newtype where
  kindOf nt = foldr (:->) KType (map kindOf (ntParams nt))

instance HasKind TParam where
  kindOf p = tpKind p

quickApply :: Kind -> [a] -> Kind
quickApply k []               = k
quickApply (_ :-> k) (_ : ts) = quickApply k ts
quickApply k _                = panic "Cryptol.TypeCheck.AST.quickApply"
                                  [ "Applying a non-function kind:", show k ]

-- Pretty Printing -------------------------------------------------------------

instance PP Kind where
  ppPrec p k = case k of
    KType   -> char '*'
    KNum    -> char '#'
    KProp   -> text "Prop"
    l :-> r -> optParens (p >= 1) (sep [ppPrec 1 l, text "->", ppPrec 0 r])

instance PP (WithNames TVar) where

  ppPrec _ (WithNames (TVBound x _) mp) =
    case IntMap.lookup x mp of
      Just a  -> text a
      Nothing -> text ("a`" ++ show x)

  ppPrec _ (WithNames (TVFree x _ _ _) _) =
    char '?' <> text (intToName x)

instance PP TVar where
  ppPrec = ppWithNamesPrec IntMap.empty

instance PP TParam where
  ppPrec = ppWithNamesPrec IntMap.empty

instance PP (WithNames TParam) where
  ppPrec _ (WithNames p mp) = ppWithNames mp (tpVar p)

instance PP (WithNames Type) where
  ppPrec prec ty0@(WithNames ty nmMap) =
    case ty of
      TVar a  -> ppWithNames nmMap a
      TRec fs -> braces $ fsep $ punctuate comma
                    [ pp l <+> text ":" <+> go 0 t | (l,t) <- fs ]
      TUser c ts _ -> optParens (prec > 3) $ pp c <+> fsep (map (go 4) ts)

      TCon (TC tc) ts ->
        case (tc,ts) of
          (TCNum n, [])       -> integer n
          (TCInf,   [])       -> text "inf"
          (TCBit,   [])       -> text "Bit"

          (TCSeq,   [t1,TCon (TC TCBit) []]) -> brackets (go 0 t1)
          (TCSeq,   [t1,t2])  -> optParens (prec > 3)
                              $ brackets (go 0 t1) <> go 3 t2

          (TCFun,   [t1,t2])  -> optParens (prec > 1)
                              $ go 2 t1 <+> text "->" <+> go 1 t2

          (TCTuple _, fs)     -> parens $ fsep $ punctuate comma $ map (go 0) fs

          (_, _)              -> pp tc <+> fsep (map (go 4) ts)

      TCon (PC pc) ts ->
        case (pc,ts) of
          (PEqual, [t1,t2])   -> go 0 t1 <+> text "==" <+> go 0 t2
          (PNeq ,  [t1,t2])   -> go 0 t1 <+> text "/=" <+> go 0 t2
          (PGeq,  [t1,t2])    -> go 0 t1 <+> text ">=" <+> go 0 t2
          (PFin,  [t1])       -> text "fin" <+> (go 4 t1)
          (PHas x, [t1,t2])   -> ppSelector x <+> text "of"
                               <+> go 0 t1 <+> text "is" <+> go 0 t2

          (PArith, [t1])      -> pp pc <+> go 4 t1
          (PCmp, [t1])        -> pp pc <+> go 4 t1

          (_, _)              -> pp pc <+> fsep (map (go 4) ts)

      _ | Just tinf <- isTInfix ty0 -> optParens (prec > 2)
                                     $ ppInfix 2 isTInfix tinf

      TCon f ts -> optParens (prec > 3)
                $ pp f <+> fsep (map (go 4) ts)

    where
    go p t = ppWithNamesPrec nmMap p t

    isTInfix (WithNames (TCon (TF ieOp) [ieLeft',ieRight']) _) =
      do let ieLeft  = WithNames ieLeft' nmMap
             ieRight = WithNames ieRight' nmMap
         (ieAssoc,iePrec) <- Map.lookup ieOp tBinOpPrec
         return Infix { .. }
    isTInfix _ = Nothing

addTNames :: [TParam] -> NameMap -> NameMap
addTNames as ns = foldr (uncurry IntMap.insert) ns
                $ named ++ zip unnamed avail

  where avail   = filter (`notElem` used) (nameList [])
        named   = [ (u,show (pp n))
                          | TParam { tpUnique = u, tpName = Just n } <- as ]
        unnamed = [ u     | TParam { tpUnique = u, tpName = Nothing } <- as ]

        used    = map snd named ++ IntMap.elems ns

ppNewtypeShort :: Newtype -> Doc
ppNewtypeShort nt =
  text "newtype" <+> pp (ntName nt) <+> hsep (map (ppWithNamesPrec nm 9) ps)
  where
  ps  = ntParams nt
  nm = addTNames ps emptyNameMap


instance PP Schema where
  ppPrec = ppWithNamesPrec IntMap.empty

instance PP (WithNames Schema) where
  ppPrec _ (WithNames s ns) = vars <+> props <+> ppWithNames ns1 (sType s)
    where
    vars = case sVars s of
      [] -> empty
      vs -> braces $ commaSep $ map (ppWithNames ns1) vs

    props = case sProps s of
      [] -> empty
      ps -> parens (commaSep (map (ppWithNames ns1) ps)) <+> text "=>"

    ns1 = addTNames (sVars s) ns

instance PP TySyn where
  ppPrec = ppWithNamesPrec IntMap.empty

instance PP (WithNames TySyn) where
  ppPrec _ (WithNames (TySyn n ps _ ty) ns) =
    text "type" <+> pp n <+> sep (map (ppWithNames ns1) ps) <+> char '='
                <+> ppWithNames ns1 ty
    where ns1 = addTNames ps ns

instance PP Type where
  ppPrec n t = ppWithNamesPrec IntMap.empty n t


instance PP TCon where
  ppPrec _ (TC tc) = pp tc
  ppPrec _ (PC tc) = pp tc
  ppPrec _ (TF tc) = pp tc

instance PP PC where
  ppPrec _ x =
    case x of
      PEqual    -> text "(==)"
      PNeq      -> text "(/=)"
      PGeq      -> text "(>=)"
      PFin      -> text "fin"
      PHas sel  -> parens (ppSelector sel)
      PArith    -> text "Arith"
      PCmp      -> text "Cmp"

instance PP TC where
  ppPrec _ x =
    case x of
      TCNum n   -> integer n
      TCInf     -> text "inf"
      TCBit     -> text "Bit"
      TCSeq     -> text "[]"
      TCFun     -> text "(->)"
      TCTuple 0 -> text "()"
      TCTuple 1 -> text "(one tuple?)"
      TCTuple n -> parens $ hcat $ replicate (n-1) comma
      TCNewtype u -> pp u

instance PP UserTC where
  ppPrec p (UserTC x _) = ppPrec p x

instance PP (WithNames Expr) where
  ppPrec prec (WithNames expr nm) =
    case expr of
      ECon c        -> ppPrefix c

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

      EComp _ e mss -> let arm ms = text "|" <+> commaSep (map ppW ms)
                       in brackets $ ppW e <+> vcat (map arm mss)

      EVar x        -> pp x

      EAbs {}       -> let (xs,e) = splitWhile splitAbs expr
                       in ppLam nm prec [] [] xs e

      EProofAbs {}  -> let (ps,e1) = splitWhile splitProofAbs expr
                           (xs,e2) = splitWhile splitAbs e1
                       in ppLam nm prec [] ps xs e2

      ETAbs {}      -> let (ts,e1) = splitWhile splitTAbs     expr
                           (ps,e2) = splitWhile splitProofAbs e1
                           (xs,e3) = splitWhile splitAbs      e2
                       in ppLam nm prec ts ps xs e3

      EApp e1 e2    -> optParens (prec > 3)
                    $  ppWP 3 e1 <+> ppWP 4 e2

      EProofApp e   -> optParens (prec > 3)
                    $ ppWP 3 e <+> text "<>"

      ETApp e t     -> optParens (prec > 3)
                    $ ppWP 3 e <+> ppWP 4 t

      ECast e t     -> optParens (prec > 0)
                     ( ppWP 2 e <+> text ":" <+> ppW t )

      EWhere e ds   -> optParens (prec > 0)
                     ( ppW e $$ text "where"
                                     $$ nest 2 (vcat (map ppW ds))
                                     $$ text "" )

    where
    ppW x   = ppWithNames nm x
    ppWP x  = ppWithNamesPrec nm x

ppLam :: NameMap -> Int -> [TParam] -> [Prop] -> [(QName,Type)] -> Expr -> Doc
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

splitAbs :: Expr -> Maybe ((QName,Type), Expr)
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
      From x _ e -> pp x <+> text "<-" <+> ppWithNames nm e
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

