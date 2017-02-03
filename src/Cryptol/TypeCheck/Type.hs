{-# Language Safe, DeriveGeneric, DeriveAnyClass, RecordWildCards #-}
{-# Language FlexibleInstances, FlexibleContexts #-}
{-# Language PatternGuards #-}
module Cryptol.TypeCheck.Type
  (module Cryptol.TypeCheck.Type, TFun(..)) where


import GHC.Generics (Generic)
import Control.DeepSeq

import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.List(sortBy)
import           Data.Ord(comparing)

import Cryptol.Parser.AST ( Selector(..), ppSelector )
import Cryptol.ModuleSystem.Name
import Cryptol.Prims.Syntax
import Cryptol.Utils.Ident (Ident)
import Cryptol.TypeCheck.PP
import Cryptol.TypeCheck.Solver.InfNat
import Cryptol.Utils.Panic(panic)

infix  4 =#=, >==
infixr 5 `tFun`
infixr 5 :->
infixl 6 .+.
infixl 7 .*.



-- | Kinds, classify types.
data Kind   = KType
            | KNum
            | KProp
            | Kind :-> Kind
              deriving (Eq, Ord, Show, Generic, NFData)

-- | The types of polymorphic values.
data Schema = Forall { sVars :: [TParam], sProps :: [Prop], sType :: Type }
              deriving (Show, Generic, NFData)

-- | Type parameters.
data TParam = TParam { tpUnique :: !Int       -- ^ Parameter identifier
                     , tpKind   :: Kind       -- ^ Kind of parameter
                     , tpName   :: Maybe Name -- ^ Name from source, if any.
                     }
              deriving (Show, Generic, NFData)


-- | The internal representation of types.
-- These are assumed to be kind correct.
data Type   = TCon TCon [Type]
              -- ^ Type constant with args

            | TVar TVar
              -- ^ Type variable (free or bound)

            | TUser Name [Type] Type
              {- ^ This is just a type annotation, for a type that
              was written as a type synonym.  It is useful so that we
              can use it to report nicer errors.
              Example: `TUser T ts t` is really just the type `t` that
              was written as `T ts` by the user. -}

            | TRec [(Ident,Type)]
              -- ^ Record type

              deriving (Show, Generic, NFData)



-- | Type variables.
data TVar   = TVFree !Int Kind (Set TVar) Doc
              -- ^ Unique, kind, ids of bound type variables that are in scope
              -- The `Doc` is a description of how this type came to be.


            | TVBound !Int Kind
              deriving (Show, Generic, NFData)


-- | The type is supposed to be of kind `KProp`
type Prop   = Type


-- | Type constants.
data TCon   = TC TC | PC PC | TF TFun | TError Kind TCErrorMessage
              deriving (Show, Eq, Ord, Generic, NFData)


-- | Predicate symbols.
data PC     = PEqual        -- ^ @_ == _@
            | PNeq          -- ^ @_ /= _@
            | PGeq          -- ^ @_ >= _@
            | PFin          -- ^ @fin _@

            -- classes
            | PHas Selector -- ^ @Has sel type field@ does not appear in schemas
            | PArith        -- ^ @Arith _@
            | PCmp          -- ^ @Cmp _@

            | PAnd          -- ^ This is useful when simplifying things in place
            | PTrue         -- ^ Ditto
              deriving (Show, Eq, Ord, Generic, NFData)

-- | 1-1 constants.
data TC     = TCNum Integer            -- ^ Numbers
            | TCInf                    -- ^ Inf
            | TCBit                    -- ^ Bit
            | TCSeq                    -- ^ @[_] _@
            | TCFun                    -- ^ @_ -> _@
            | TCTuple Int              -- ^ @(_, _, _)@
            | TCNewtype UserTC         -- ^ user-defined, @T@
              deriving (Show, Eq, Ord, Generic, NFData)


data UserTC = UserTC Name Kind
              deriving (Show, Generic, NFData)


data TCErrorMessage = TCErrorMessage
  { tcErrorMessage :: !String
    -- XXX: Add location?
  } deriving (Show, Eq, Ord, Generic, NFData)




-- | Type synonym.
data TySyn  = TySyn { tsName        :: Name       -- ^ Name
                    , tsParams      :: [TParam]   -- ^ Parameters
                    , tsConstraints :: [Prop]     -- ^ Ensure body is OK
                    , tsDef         :: Type       -- ^ Definition
                    }
              deriving (Show, Generic, NFData)





-- | Named records
data Newtype  = Newtype { ntName   :: Name
                        , ntParams :: [TParam]
                        , ntConstraints :: [Prop]
                        , ntFields :: [(Ident,Type)]
                        } deriving (Show, Generic, NFData)




--------------------------------------------------------------------------------


class HasKind t where
  kindOf :: t -> Kind

instance HasKind TVar where
  kindOf (TVFree  _ k _ _) = k
  kindOf (TVBound _ k) = k

instance HasKind TCon where
  kindOf (TC tc)      = kindOf tc
  kindOf (PC pc)      = kindOf pc
  kindOf (TF tf)      = kindOf tf
  kindOf (TError k _) = k

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
      PAnd      -> KProp :-> KProp :-> KProp
      PTrue     -> KProp

instance HasKind TFun where
  kindOf tfun =
    case tfun of
      TCWidth  -> KNum :-> KNum

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

kindResult :: Kind -> Kind
kindResult (_ :-> k) = kindResult k
kindResult k         = k

--------------------------------------------------------------------------------

-- Syntactic equality, ignoring type synonyms and record order
instance Eq Type where
  TUser _ _ x == y        = x == y
  x == TUser _ _ y        = y == x

  TCon x xs == TCon y ys  = x == y && xs == ys
  TVar x    == TVar y     = x == y

  TRec xs   == TRec ys    = norm xs == norm ys
    where norm = sortBy (comparing fst)

  _         == _          = False

instance Ord Type where
  compare x0 y0 =
    case (x0,y0) of
      (TUser _ _ t, _)        -> compare t y0
      (_, TUser _ _ t)        -> compare x0 t

      (TVar x, TVar y)        -> compare x y
      (TVar {}, _)            -> LT
      (_, TVar {})            -> GT

      (TCon x xs, TCon y ys)  -> compare (x,xs) (y,ys)
      (TCon {}, _)            -> LT
      (_,TCon {})             -> GT

      (TRec xs, TRec ys)      -> compare (norm xs) (norm ys)
        where norm = sortBy (comparing fst)



instance Eq TParam where
  x == y = tpUnique x == tpUnique y

instance Ord TParam where
  compare x y = compare (tpUnique x) (tpUnique y)

tpVar :: TParam -> TVar
tpVar p = TVBound (tpUnique p) (tpKind p)

-- | The type is "simple" (i.e., it contains no type functions).
type SType  = Type



newtypeConType :: Newtype -> Schema
newtypeConType nt =
  Forall as (ntConstraints nt)
    $ TRec (ntFields nt) `tFun` TCon (newtypeTyCon nt) (map (TVar . tpVar) as)
  where
  as = ntParams nt




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

--------------------------------------------------------------------------------
-- Queries

isFreeTV :: TVar -> Bool
isFreeTV (TVFree {}) = True
isFreeTV _           = False

isBoundTV :: TVar -> Bool
isBoundTV (TVBound {})  = True
isBoundTV _             = False


tIsError :: Type -> Maybe TCErrorMessage
tIsError ty = case tNoUser ty of
                TCon (TError _ x) _ -> Just x
                _                   -> Nothing

tIsNat' :: Type -> Maybe Nat'
tIsNat' ty =
  case tNoUser ty of
    TCon (TC (TCNum x)) [] -> Just (Nat x)
    TCon (TC TCInf)     [] -> Just Inf
    _                      -> Nothing

tIsNum :: Type -> Maybe Integer
tIsNum ty = do Nat x <- tIsNat' ty
               return x

tIsInf :: Type -> Bool
tIsInf ty = tIsNat' ty == Just Inf

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

tIsBinFun :: TFun -> Type -> Maybe (Type,Type)
tIsBinFun f ty = case tNoUser ty of
                   TCon (TF g) [a,b] | f == g -> Just (a,b)
                   _                          -> Nothing

-- | Split up repeated occurances of the given binary type-level function.
tSplitFun :: TFun -> Type -> [Type]
tSplitFun f t0 = go t0 []
  where go ty xs = case tIsBinFun f ty of
                     Just (a,b) -> go a (go b xs)
                     Nothing    -> ty : xs


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

pIsTrue :: Prop -> Bool
pIsTrue ty  = case tNoUser ty of
                TCon (PC PTrue) _ -> True
                _                 -> False

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

tNat'    :: Nat' -> Type
tNat' n'  = case n' of
              Inf   -> tInf
              Nat n -> tNum n

tBit     :: Type
tBit      = TCon (TC TCBit) []

tWord    :: Type -> Type
tWord a   = tSeq a tBit

tSeq     :: Type -> Type -> Type
tSeq a b  = TCon (TC TCSeq) [a,b]

tChar :: Type
tChar = tWord (tNum (8 :: Int))

tString :: Int -> Type
tString len = tSeq (tNum len) tChar

tRec     :: [(Ident,Type)] -> Type
tRec      = TRec

tTuple   :: [Type] -> Type
tTuple ts = TCon (TC (TCTuple (length ts))) ts

newtypeTyCon :: Newtype -> TCon
newtypeTyCon nt = TC $ TCNewtype $ UserTC (ntName nt) (kindOf nt)


-- | Make a function type.
tFun     :: Type -> Type -> Type
tFun a b  = TCon (TC TCFun) [a,b]

-- | Eliminate outermost type synonyms.
tNoUser  :: Type -> Type
tNoUser t = case t of
              TUser _ _ a -> tNoUser a
              _           -> t


--------------------------------------------------------------------------------
-- Construction of type functions

-- | Make a malformed numeric type.
tBadNumber :: TCErrorMessage -> Type
tBadNumber msg = TCon (TError KNum msg) []

tf1 :: TFun -> Type -> Type
tf1 f x = TCon (TF f) [x]

tf2 :: TFun -> Type -> Type -> Type
tf2 f x y = TCon (TF f) [x,y]

tf3 :: TFun -> Type -> Type -> Type -> Type
tf3 f x y z = TCon (TF f) [x,y,z]

(.*.) :: Type -> Type -> Type
(.*.) = tMul

-- | Make addition type.
(.+.) :: Type -> Type -> Type
(.+.) = tAdd

(.-.) :: Type -> Type -> Type
(.-.) = tSub

(.^.) :: Type -> Type -> Type
(.^.) = tExp



tAdd :: Type -> Type -> Type
tAdd = tf2 TCAdd

tSub :: Type -> Type -> Type
tSub = tf2 TCSub

tMul :: Type -> Type -> Type
tMul = tf2 TCMul

tDiv :: Type -> Type -> Type
tDiv = tf2 TCDiv

tMod :: Type -> Type -> Type
tMod = tf2 TCMod

tExp :: Type -> Type -> Type
tExp = tf2 TCExp

tMin :: Type -> Type -> Type
tMin = tf2 TCMin

tMax :: Type -> Type -> Type
tMax = tf2 TCMax

tWidth :: Type -> Type
tWidth = tf1 TCWidth

tLenFromThen :: Type -> Type -> Type -> Type
tLenFromThen = tf3 TCLenFromThen

tLenFromThenTo :: Type -> Type -> Type -> Type
tLenFromThenTo = tf3 TCLenFromThenTo








--------------------------------------------------------------------------------
-- Construction of constraints.

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

pTrue :: Prop
pTrue = TCon (PC PTrue) []

pAnd :: [Prop] -> Prop
pAnd []       = pTrue
pAnd [x]      = x
pAnd (x : xs)
  | Just _ <- tIsError x    = x
  | pIsTrue x               = rest
  | Just _ <- tIsError rest = rest
  | pIsTrue rest            = x
  | otherwise               = TCon (PC PAnd) [x, rest]
  where rest = pAnd xs

pSplitAnd :: Prop -> [Prop]
pSplitAnd p0 = go [p0]
  where
  go [] = []
  go (q : qs) =
    case tNoUser q of
      TCon (PC PAnd) [l,r] -> go (l : r : qs)
      TCon (PC PTrue) _    -> go qs
      _                    -> q : go qs

pFin :: Type -> Prop
pFin ty =
  case tNoUser ty of
    TCon (TC (TCNum _)) _ -> pTrue
    TCon (TC TCInf)     _ -> pError (TCErrorMessage "`inf` is not finite.")
    _                     -> TCon (PC PFin) [ty]

-- | Make a malformed property.
pError :: TCErrorMessage -> Prop
pError msg = TCon (TError KProp msg) []

--------------------------------------------------------------------------------


class FVS t where
  fvs :: t -> Set TVar

instance FVS Type where
  fvs = go
    where
    go ty =
      case ty of
        TCon _ ts   -> Set.unions (map go ts)
        TVar x      -> Set.singleton x
        TUser _ _ t -> go t
        TRec fs     -> Set.unions (map (go . snd) fs)

instance FVS a => FVS (Maybe a) where
  fvs Nothing  = Set.empty
  fvs (Just x) = fvs x

instance FVS a => FVS [a] where
  fvs xs    = Set.unions (map fvs xs)

instance (FVS a, FVS b) => FVS (a,b) where
  fvs (x,y) = Set.union (fvs x) (fvs y)

instance FVS Schema where
  fvs (Forall as ps t) =
      Set.difference (Set.union (fvs ps) (fvs t)) bound
    where bound = Set.fromList (map tpVar as)



-- Pretty Printing -------------------------------------------------------------

instance PP TParam where
  ppPrec = ppWithNamesPrec IntMap.empty

instance PP (WithNames TParam) where
  ppPrec _ (WithNames p mp) = ppWithNames mp (tpVar p)

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


instance PP Type where
  ppPrec n t = ppWithNamesPrec IntMap.empty n t


instance PP TCon where
  ppPrec _ (TC tc)        = pp tc
  ppPrec _ (PC tc)        = pp tc
  ppPrec _ (TF tc)        = pp tc
  ppPrec _ (TError _ msg) = pp msg

instance PP TCErrorMessage where
  ppPrec _ tc = parens (text "error:" <+> text (tcErrorMessage tc))

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
      PTrue     -> text "True"
      PAnd      -> text "(&&)"

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


