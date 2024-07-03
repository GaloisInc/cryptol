{-# Language Safe, DeriveGeneric, DeriveAnyClass, RecordWildCards #-}
{-# Language FlexibleInstances, FlexibleContexts #-}
{-# Language PatternGuards #-}
{-# Language OverloadedStrings #-}
{-| This module contains types related to typechecking and the output of the
typechecker.  In particular, it should contain the types needed by
interface files (see 'Crytpol.ModuleSystem.Interface'), which are (kind of)
the output of the typechker.
-}
module Cryptol.TypeCheck.Type
  ( module Cryptol.TypeCheck.Type
  , module Cryptol.TypeCheck.TCon
  ) where


import GHC.Generics (Generic)
import Control.DeepSeq

import           Data.Map(Map)
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import           Data.Maybe (fromMaybe)
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text)

import Cryptol.Parser.Selector
import Cryptol.Parser.Position(Located,thing,Range,emptyRange)
import Cryptol.Parser.AST(ImpName(..))
import Cryptol.ModuleSystem.Name
import Cryptol.Utils.Ident (Ident, isInfixIdent, exprModName, ogModule, ModName)
import Cryptol.TypeCheck.TCon
import Cryptol.TypeCheck.PP
import Cryptol.TypeCheck.Solver.InfNat
import Cryptol.Utils.Fixity
import Cryptol.Utils.Panic(panic)
import Cryptol.Utils.RecordMap
import Prelude

infix  4 =#=, >==
infixr 5 `tFun`


--------------------------------------------------------------------------------
-- Module parameters

type FunctorParams = Map Ident ModParam

-- | Compute the names from all functor parameters
allParamNames :: FunctorParams -> ModParamNames
allParamNames mps =
  ModParamNames
    { mpnTypes       = Map.unions (map mpnTypes ps)
    , mpnConstraints = concatMap mpnConstraints ps
    , mpnFuns        = Map.unions (map mpnFuns ps)
    , mpnTySyn       = Map.unions (map mpnTySyn ps)
    , mpnDoc         = Nothing
    }
  where
  ps = map mpParameters (Map.elems mps)


-- | A module parameter.  Corresponds to a "signature import".
-- A single module parameter can bring multiple things in scope.
data ModParam = ModParam
  { mpName        :: Ident
    -- ^ The name of a functor parameter.

  , mpQual        :: !(Maybe ModName)
    -- ^ This is the qualifier for the parameter.  We use it to
    -- derive parameter names when doing `_` imports.

  , mpIface       :: ImpName Name
    -- ^ The interface corresponding to this parameter.
    -- This is thing in `import interface`

  , mpParameters  :: ModParamNames
    {- ^ These are the actual parameters, not the ones in the interface
      For example if the same interface is used for multiple parameters
      the `ifmpParameters` would all be different. -}
  } deriving (Show, Generic, NFData)

-- | Information about the names brought in through an "interface import".
-- This is also used to keep information about.
data ModParamNames = ModParamNames
  { mpnTypes       :: Map Name ModTParam
    -- ^ Type parameters

  , mpnTySyn      :: !(Map Name TySyn)
    -- ^ Type synonyms

  , mpnConstraints :: [Located Prop]
    -- ^ Constraints on param. types


  , mpnFuns        :: Map.Map Name ModVParam
    -- ^ Value parameters

  , mpnDoc         :: !(Maybe Text)
    -- ^ Documentation about the interface.
  } deriving (Show, Generic, NFData)

-- | A type parameter of a module.
data ModTParam = ModTParam
  { mtpName   :: Name
  , mtpKind   :: Kind
  , mtpDoc    :: Maybe Text
  } deriving (Show,Generic,NFData)


-- | This is how module parameters appear in actual types.
mtpParam :: ModTParam -> TParam
mtpParam mtp = TParam { tpUnique = nameUnique (mtpName mtp)
                      , tpKind   = mtpKind mtp
                      , tpFlav   = TPModParam (mtpName mtp)
                      , tpInfo   = desc
                      }
  where desc = TVarInfo { tvarDesc   = TVFromModParam (mtpName mtp)
                        , tvarSource = nameLoc (mtpName mtp)
                        }

-- | A value parameter of a module.
data ModVParam = ModVParam
  { mvpName   :: Name
  , mvpType   :: Schema
  , mvpDoc    :: Maybe Text
  , mvpFixity :: Maybe Fixity       -- XXX: This should be in the name?
  } deriving (Show,Generic,NFData)
--------------------------------------------------------------------------------




-- | The types of polymorphic values.
data Schema = Forall { sVars :: [TParam], sProps :: [Prop], sType :: Type }
              deriving (Eq, Show, Generic, NFData)

-- | Type parameters.
data TParam = TParam { tpUnique :: !Int       -- ^ Parameter identifier
                     , tpKind   :: Kind       -- ^ Kind of parameter
                     , tpFlav   :: TPFlavor
                        -- ^ What sort of type parameter is this
                     , tpInfo   :: !TVarInfo
                       -- ^ A description for better messages.
                     }
              deriving (Generic, NFData, Show)

data TPFlavor = TPModParam Name
              | TPUnifyVar
              | TPSchemaParam Name
              | TPTySynParam Name
              | TPPropSynParam Name
              | TPNominalParam Name
              | TPPrimParam Name
              deriving (Generic, NFData, Show)

tMono :: Type -> Schema
tMono = Forall [] []

isMono :: Schema -> Maybe Type
isMono s =
  case s of
    Forall [] [] t -> Just t
    _              -> Nothing


schemaParam :: Name -> TPFlavor
schemaParam = TPSchemaParam

tySynParam :: Name -> TPFlavor
tySynParam = TPTySynParam

propSynParam :: Name -> TPFlavor
propSynParam = TPPropSynParam

nominalParam :: Name -> TPFlavor
nominalParam = TPNominalParam

primParam :: Name -> TPFlavor
primParam = TPPrimParam

modTyParam :: Name -> TPFlavor
modTyParam = TPModParam


tpfName :: TPFlavor -> Maybe Name
tpfName f =
  case f of
    TPUnifyVar       -> Nothing
    TPModParam x     -> Just x
    TPSchemaParam x  -> Just x
    TPTySynParam x   -> Just x
    TPPropSynParam x -> Just x
    TPNominalParam x -> Just x
    TPPrimParam x    -> Just x

tpName :: TParam -> Maybe Name
tpName = tpfName . tpFlav

-- | The internal representation of types.
-- These are assumed to be kind correct.
data Type   = TCon !TCon ![Type]
              -- ^ Type constant with args

            | TVar TVar
              -- ^ Type variable (free or bound)

            | TUser !Name ![Type] !Type
              {- ^ This is just a type annotation, for a type that
              was written as a type synonym.  It is useful so that we
              can use it to report nicer errors.
              Example: @TUser T ts t@ is really just the type @t@ that
              was written as @T ts@ by the user. -}

            | TRec !(RecordMap Ident Type)
              -- ^ Record type

            | TNominal !NominalType ![Type]
              -- ^ A nominal types

              deriving (Show, Generic, NFData)



-- | Type variables.
data TVar   = TVFree !Int Kind (Set TParam) TVarInfo
              -- ^ Unique, kind, ids of bound type variables that are in scope.
              -- The last field gives us some info for nicer warnings/errors.


            | TVBound {-# UNPACK #-} !TParam
              deriving (Show, Generic, NFData)

tvInfo :: TVar -> TVarInfo
tvInfo tv =
  case tv of
    TVFree _ _ _ d -> d
    TVBound tp     -> tpInfo tp

tvUnique :: TVar -> Int
tvUnique (TVFree u _ _ _) = u
tvUnique (TVBound TParam { tpUnique = u }) = u

data TVarInfo = TVarInfo { tvarSource :: !Range -- ^ Source code that gave rise
                         , tvarDesc   :: !TypeSource -- ^ Description
                         }
              deriving (Show, Generic, NFData)


-- | Explains how this type came to be, for better error messages.
data TypeSource = TVFromModParam Name     -- ^ Name of module parameter
                | TVFromSignature Name    -- ^ A variable in a signature
                | TypeWildCard
                | TypeOfRecordField Ident
                | TypeOfTupleField Int
                | TypeOfSeqElement
                | LenOfSeq
                | TypeParamInstNamed {-Fun-}Name {-Param-}Ident
                | TypeParamInstPos   {-Fun-}Name {-Pos (from 1)-}Int
                | DefinitionOf Name
                | LenOfCompGen
                | TypeOfArg ArgDescr
                | TypeOfRes
                | FunApp
                | TypeOfIfCondExpr
                | TypeFromUserAnnotation
                | GeneratorOfListComp
                | CasedExpression
                | ConPat
                | TypeErrorPlaceHolder
                  deriving (Show, Generic, NFData)

data ArgDescr = ArgDescr
  { argDescrFun    :: Maybe Name
  , argDescrNumber :: Maybe Int
  }
  deriving (Show,Generic,NFData)

noArgDescr :: ArgDescr
noArgDescr = ArgDescr { argDescrFun = Nothing, argDescrNumber = Nothing }

-- | Get the names of something that is related to the tvar.
tvSourceName :: TypeSource -> Maybe Name
tvSourceName tvs =
  case tvs of
    TVFromModParam x -> Just x
    TVFromSignature x -> Just x
    TypeParamInstNamed x _ -> Just x
    TypeParamInstPos x _ -> Just x
    DefinitionOf x -> Just x
    TypeOfArg x -> argDescrFun x
    _ -> Nothing


-- | A type annotated with information on how it came about.
data TypeWithSource = WithSource
  { twsType   :: Type
  , twsSource :: TypeSource
  , twsRange  :: !(Maybe Range)
  }


-- | The type is supposed to be of kind 'KProp'.
type Prop   = Type





-- | Type synonym.
data TySyn  = TySyn { tsName        :: Name       -- ^ Name
                    , tsParams      :: [TParam]   -- ^ Parameters
                    , tsConstraints :: [Prop]     -- ^ Ensure body is OK
                    , tsDef         :: Type       -- ^ Definition
                    , tsDoc         :: !(Maybe Text) -- ^ Documentation
                    }
              deriving (Show, Generic, NFData)





-- | Nominal types
data NominalType = NominalType
  { ntName        :: Name
  , ntParams      :: [TParam]
  , ntKind        :: !Kind             -- ^ Result kind
  , ntConstraints :: [Prop]
  , ntDef         :: NominalTypeDef
  , ntFixity      :: !(Maybe Fixity)
  , ntDoc         :: Maybe Text
  } deriving (Show, Generic, NFData)

-- | Definition of a nominal type
data NominalTypeDef =
    Struct StructCon
  | Enum [EnumCon]
  | Abstract
  deriving (Show, Generic, NFData)

-- | Constructor for a struct (aka newtype)
data StructCon = StructCon
  { ntConName     :: !Name
  , ntFields      :: RecordMap Ident Type
  } deriving (Show, Generic, NFData)

-- | Constructor for an enumeration
data EnumCon = EnumCon
  { ecName        :: Name
  , ecNumber      :: !Int -- ^ Number of constructor in the declaration
  , ecFields      :: [Type]
  , ecPublic      :: Bool
  , ecDoc         :: Maybe Text
  } deriving (Show,Generic,NFData)


instance Eq NominalType where
  x == y = ntName x == ntName y

instance Ord NominalType where
  compare x y = compare (ntName x) (ntName y)


--------------------------------------------------------------------------------

instance HasKind TVar where
  kindOf (TVFree  _ k _ _) = k
  kindOf (TVBound tp) = kindOf tp

instance HasKind Type where
  kindOf ty =
    case ty of
      TVar a      -> kindOf a
      TCon c ts   -> quickApply (kindOf c) ts
      TUser _ _ t -> kindOf t
      TRec {}     -> KType
      TNominal nt ts ->
        case ntDef nt of
          Struct {} -> KType
          Enum {}   -> KType
          Abstract  -> quickApply (kindOf nt) ts

instance HasKind TySyn where
  kindOf ts = foldr (:->) (kindOf (tsDef ts)) (map kindOf (tsParams ts))

instance HasKind NominalType where
  kindOf nt = foldr (:->) (ntKind nt) (map kindOf (ntParams nt))

instance HasKind TParam where
  kindOf = tpKind

quickApply :: Kind -> [a] -> Kind
quickApply k []               = k
quickApply (_ :-> k) (_ : ts) = quickApply k ts
quickApply k _                = panic "Cryptol.TypeCheck.AST.quickApply"
                                  [ "Applying a non-function kind:", show k ]

kindResult :: Kind -> Kind
kindResult (_ :-> k) = kindResult k
kindResult k         = k

--------------------------------------------------------------------------------

-- | Syntactic equality, ignoring type synonyms and record order.
instance Eq Type where
  TUser _ _ x == y        = x == y
  x == TUser _ _ y        = y == x

  TCon x xs == TCon y ys  = x == y && xs == ys
  TVar x    == TVar y     = x == y
  TRec xs   == TRec ys    = xs == ys
  TNominal ntx xs == TNominal nty ys = ntx == nty && xs == ys

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

      (TRec xs, TRec ys)      -> compare xs ys
      (TRec{}, _)             -> LT
      (_, TRec{})             -> GT

      (TNominal x xs, TNominal y ys) -> compare (x,xs) (y,ys)

instance Eq TParam where
  x == y = tpUnique x == tpUnique y

instance Ord TParam where
  compare x y = compare (tpUnique x) (tpUnique y)

tpVar :: TParam -> TVar
tpVar = TVBound

-- | The type is "simple" (i.e., it contains no type functions).
type SType  = Type


--------------------------------------------------------------------
-- Superclass

-- | Compute the set of all @Prop@s that are implied by the
--   given prop via superclass constraints.
superclassSet :: Prop -> Set Prop

superclassSet (TCon (PC PPrime) [n]) =
  Set.fromList [ pFin n, n >== tTwo ]

superclassSet (TCon (PC p0) [t]) = go p0
  where
  super p = Set.insert (TCon (PC p) [t]) (go p)

  go PRing      = super PZero
  go PLogic     = super PZero
  go PField     = super PRing
  go PIntegral  = super PRing
  go PRound     = super PField <> super PCmp
  go PCmp       = super PEq
  go PSignedCmp = super PEq
  go _ = mempty

superclassSet _ = mempty


nominalTypeConTypes :: NominalType -> [(Name,Schema)]
nominalTypeConTypes nt =
  case ntDef nt of
    Struct s -> [ ( ntConName s
                  , Forall as ctrs (TRec (ntFields s) `tFun` resT)
                  ) ]
    Enum cs  -> [ ( ecName c
                  , Forall as ctrs (foldr tFun resT (ecFields c))
                  )
                | c <- cs
                ]
    Abstract -> []
  where
  as    = ntParams nt
  ctrs  = ntConstraints nt
  resT  = TNominal nt (map (TVar . tpVar) as)

nominalTypeIsAbstract :: NominalType -> Bool
nominalTypeIsAbstract nt =
  case ntDef nt of
    Abstract -> True
    _        -> False

instance Eq TVar where
  TVBound x       == TVBound y       = x == y
  TVFree  x _ _ _ == TVFree  y _ _ _ = x == y
  _             == _              = False

instance Ord TVar where
  compare (TVFree x _ _ _) (TVFree y _ _ _) = compare x y
  compare (TVFree _ _ _ _) _                = LT
  compare _            (TVFree _ _ _ _)     = GT

  compare (TVBound x) (TVBound y) = compare x y

--------------------------------------------------------------------------------
-- Queries

isFreeTV :: TVar -> Bool
isFreeTV (TVFree {}) = True
isFreeTV _           = False

isBoundTV :: TVar -> Bool
isBoundTV (TVBound {})  = True
isBoundTV _             = False


tIsError :: Type -> Maybe Type
tIsError ty = case tNoUser ty of
                TCon (TError _) [t] -> Just t
                TCon (TError _) _   -> panic "tIsError" ["Malformed error"]
                _                   -> Nothing

tHasErrors :: Type -> Bool
tHasErrors ty =
  case tNoUser ty of
    TCon (TError _) _   -> True
    TCon _ ts           -> any tHasErrors ts
    TRec mp             -> any tHasErrors mp
    _                   -> False

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

tIsInteger :: Type -> Bool
tIsInteger ty = case tNoUser ty of
                  TCon (TC TCInteger) [] -> True
                  _                      -> False

tIsIntMod :: Type -> Maybe Type
tIsIntMod ty = case tNoUser ty of
                 TCon (TC TCIntMod) [n] -> Just n
                 _                      -> Nothing

tIsRational :: Type -> Bool
tIsRational ty =
  case tNoUser ty of
    TCon (TC TCRational) [] -> True
    _                       -> False

tIsFloat :: Type -> Maybe (Type, Type)
tIsFloat ty =
  case tNoUser ty of
    TCon (TC TCFloat) [e, p] -> Just (e, p)
    _                        -> Nothing

tIsTuple :: Type -> Maybe [Type]
tIsTuple ty = case tNoUser ty of
                TCon (TC (TCTuple _)) ts -> Just ts
                _                        -> Nothing

tIsRec :: Type -> Maybe (RecordMap Ident Type)
tIsRec ty = case tNoUser ty of
              TRec fs -> Just fs
              _       -> Nothing

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

pIsPrime :: Prop -> Maybe Type
pIsPrime ty = case tNoUser ty of
                TCon (PC PPrime) [t1] -> Just t1
                _                     -> Nothing

pIsGeq :: Prop -> Maybe (Type,Type)
pIsGeq ty = case tNoUser ty of
              TCon (PC PGeq) [t1,t2] -> Just (t1,t2)
              _                      -> Nothing

pIsEqual :: Prop -> Maybe (Type,Type)
pIsEqual ty = case tNoUser ty of
                TCon (PC PEqual) [t1,t2] -> Just (t1,t2)
                _                        -> Nothing

pIsZero :: Prop -> Maybe Type
pIsZero ty = case tNoUser ty of
               TCon (PC PZero) [t1] -> Just t1
               _                    -> Nothing

pIsLogic :: Prop -> Maybe Type
pIsLogic ty = case tNoUser ty of
                TCon (PC PLogic) [t1] -> Just t1
                _                     -> Nothing

pIsRing :: Prop -> Maybe Type
pIsRing ty = case tNoUser ty of
                TCon (PC PRing) [t1] -> Just t1
                _                    -> Nothing

pIsField :: Prop -> Maybe Type
pIsField ty = case tNoUser ty of
                TCon (PC PField) [t1] -> Just t1
                _                     -> Nothing

pIsIntegral :: Prop -> Maybe Type
pIsIntegral ty = case tNoUser ty of
                   TCon (PC PIntegral) [t1] -> Just t1
                   _                        -> Nothing

pIsRound :: Prop -> Maybe Type
pIsRound ty = case tNoUser ty of
                     TCon (PC PRound) [t1] -> Just t1
                     _                     -> Nothing

pIsEq :: Prop -> Maybe Type
pIsEq ty = case tNoUser ty of
             TCon (PC PEq) [t1] -> Just t1
             _                  -> Nothing

pIsCmp :: Prop -> Maybe Type
pIsCmp ty = case tNoUser ty of
              TCon (PC PCmp) [t1] -> Just t1
              _                   -> Nothing

pIsSignedCmp :: Prop -> Maybe Type
pIsSignedCmp ty = case tNoUser ty of
                    TCon (PC PSignedCmp) [t1] -> Just t1
                    _                         -> Nothing

pIsLiteral :: Prop -> Maybe (Type, Type)
pIsLiteral ty = case tNoUser ty of
                  TCon (PC PLiteral) [t1, t2] -> Just (t1, t2)
                  _                           -> Nothing

pIsLiteralLessThan :: Prop -> Maybe (Type, Type)
pIsLiteralLessThan ty =
  case tNoUser ty of
    TCon (PC PLiteralLessThan) [t1, t2] -> Just (t1, t2)
    _                                   -> Nothing

pIsFLiteral :: Prop -> Maybe (Type,Type,Type,Type)
pIsFLiteral ty = case tNoUser ty of
                   TCon (PC PFLiteral) [t1,t2,t3,t4] -> Just (t1,t2,t3,t4)
                   _                                 -> Nothing

pIsTrue :: Prop -> Bool
pIsTrue ty  = case tNoUser ty of
                TCon (PC PTrue) _ -> True
                _                 -> False

pIsWidth :: Prop -> Maybe Type
pIsWidth ty = case tNoUser ty of
                TCon (TF TCWidth) [t1] -> Just t1
                _                      -> Nothing

pIsValidFloat :: Prop -> Maybe (Type,Type)
pIsValidFloat ty = case tNoUser ty of
                     TCon (PC PValidFloat) [a,b] -> Just (a,b)
                     _                           -> Nothing

--------------------------------------------------------------------------------


tNum     :: Integral a => a -> Type
tNum n    = TCon (TC (TCNum (toInteger n))) []

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

tNominal :: NominalType -> [Type] -> Type
tNominal = TNominal

tBit     :: Type
tBit      = TCon (TC TCBit) []

tInteger :: Type
tInteger  = TCon (TC TCInteger) []

tRational :: Type
tRational  = TCon (TC TCRational) []

tFloat   :: Type -> Type -> Type
tFloat e p = TCon (TC TCFloat) [ e, p ]

tIntMod :: Type -> Type
tIntMod n = TCon (TC TCIntMod) [n]

tArray :: Type -> Type -> Type
tArray a b = TCon (TC TCArray) [a, b]

tWord    :: Type -> Type
tWord a   = tSeq a tBit

tSeq     :: Type -> Type -> Type
tSeq a b  = TCon (TC TCSeq) [a,b]

tChar :: Type
tChar = tWord (tNum (8 :: Int))

tString :: Int -> Type
tString len = tSeq (tNum len) tChar

tRec     :: RecordMap Ident Type -> Type
tRec      = TRec

tTuple   :: [Type] -> Type
tTuple ts = TCon (TC (TCTuple (length ts))) ts

-- | Make a function type.
tFun     :: Type -> Type -> Type
tFun a b  = TCon (TC TCFun) [a,b]

-- | Eliminate outermost type synonyms.
tNoUser :: Type -> Type
tNoUser t = case t of
              TUser _ _ a -> tNoUser a
              _           -> t


--------------------------------------------------------------------------------
-- Construction of type functions

-- | Make an error value of the given type to replace
-- the given malformed type (the argument to the error function)
tError :: Type -> Type
tError t = TCon (TError (k :-> k)) [t]
  where k = kindOf t

tf1 :: TFun -> Type -> Type
tf1 f x = TCon (TF f) [x]

tf2 :: TFun -> Type -> Type -> Type
tf2 f x y = TCon (TF f) [x,y]

tf3 :: TFun -> Type -> Type -> Type -> Type
tf3 f x y z = TCon (TF f) [x,y,z]

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

tCeilDiv :: Type -> Type -> Type
tCeilDiv = tf2 TCCeilDiv

tCeilMod :: Type -> Type -> Type
tCeilMod = tf2 TCCeilMod

tLenFromThenTo :: Type -> Type -> Type -> Type
tLenFromThenTo = tf3 TCLenFromThenTo






--------------------------------------------------------------------------------
-- Construction of constraints.

-- | Equality for numeric types.
(=#=) :: Type -> Type -> Prop
x =#= y = TCon (PC PEqual) [x,y]

(=/=) :: Type -> Type -> Prop
x =/= y = TCon (PC PNeq) [x,y]

pZero :: Type -> Prop
pZero t = TCon (PC PZero) [t]

pLogic :: Type -> Prop
pLogic t = TCon (PC PLogic) [t]

pRing :: Type -> Prop
pRing t = TCon (PC PRing) [t]

pIntegral :: Type -> Prop
pIntegral t = TCon (PC PIntegral) [t]

pField :: Type -> Prop
pField t = TCon (PC PField) [t]

pRound :: Type -> Prop
pRound t = TCon (PC PRound) [t]

pEq :: Type -> Prop
pEq t = TCon (PC PEq) [t]

pCmp :: Type -> Prop
pCmp t = TCon (PC PCmp) [t]

pSignedCmp :: Type -> Prop
pSignedCmp t = TCon (PC PSignedCmp) [t]

pLiteral :: Type -> Type -> Prop
pLiteral x y = TCon (PC PLiteral) [x, y]

pLiteralLessThan :: Type -> Type -> Prop
pLiteralLessThan x y = TCon (PC PLiteralLessThan) [x, y]

-- | Make a greater-than-or-equal-to constraint.
(>==) :: Type -> Type -> Prop
x >== y = TCon (PC PGeq) [x,y]

-- | A @Has@ constraint, used for tuple and record selection.
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
    TCon (TC TCInf)     _ -> tError prop -- XXX: should we be doing this here??
    _                     -> prop
  where
  prop = TCon (PC PFin) [ty]

pValidFloat :: Type -> Type -> Type
pValidFloat e p = TCon (PC PValidFloat) [e,p]

pPrime :: Type -> Prop
pPrime ty =
  case tNoUser ty of
    TCon (TC TCInf) _ -> tError prop
    _ -> prop
  where
  prop = TCon (PC PPrime) [ty]

-- Negation --------------------------------------------------------------------

{-| `pNegNumeric` negates a simple (i.e., not And, not prime, etc) prop
over numeric type vars.  The result is a conjunction of properties.  -}
pNegNumeric :: Prop -> [Prop]
pNegNumeric prop =
  case tNoUser prop of
    TCon tcon tys ->
      case tcon of
        PC pc ->
          case pc of

            -- not (x == y)  <=>  x /= y
            PEqual -> [TCon (PC PNeq) tys]

            -- not (x /= y)  <=>  x == y
            PNeq -> [TCon (PC PEqual) tys]

            -- not (x >= y)  <=>  x /= y and y >= x
            PGeq -> [TCon (PC PNeq) tys, TCon (PC PGeq) (reverse tys)]

            -- not (fin x)  <=>  x == Inf
            PFin | [ty] <- tys -> [ty =#= tInf]
                 | otherwise -> bad

            -- not True  <=>  0 == 1
            PTrue -> [TCon (PC PEqual) [tZero, tOne]]

            _ -> bad

        TError _ki -> [prop] -- propogates `TError`

        TC _tc -> bad
        TF _tf -> bad

    _ -> bad

  where
  bad = panic "pNegNumeric"
          [ "Unexpected numeric constraint:"
          , pretty prop
          ]


--------------------------------------------------------------------------------

noFreeVariables :: FVS t => t -> Bool
noFreeVariables = all (not . isFreeTV) . Set.toList . fvs

freeParams :: FVS t => t -> Set TParam
freeParams x = Set.unions (map params (Set.toList (fvs x)))
  where
    params (TVFree _ _ tps _) = tps
    params (TVBound tp) = Set.singleton tp

class FVS t where
  fvs :: t -> Set TVar

instance FVS Type where
  fvs = go
    where
    go ty =
      case ty of
        TCon _ ts   -> fvs ts
        TVar x      -> Set.singleton x
        TUser _ _ t -> go t
        TRec fs     -> fvs (recordElements fs)
        TNominal _nt ts -> fvs ts


instance FVS a => FVS (Maybe a) where
  fvs Nothing  = Set.empty
  fvs (Just x) = fvs x

instance FVS a => FVS [a] where
  fvs xs        = Set.unions (map fvs xs)

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
                $ named ++ zip unnamed_nums numNames
                        ++ zip unnamed_vals valNames

  where avail xs = filter (`notElem` used) (nameList xs)
        numNames = avail ["n","m","i","j","k"]
        valNames = avail ["a","b","c","d","e"]

        nm x = (tpUnique x, tpName x, tpKind x)

        named        = [ (u,show (pp n)) | (u,Just n,_)  <- map nm as ]
        unnamed_nums = [ u               | (u,Nothing,KNum)  <- map nm as ]
        unnamed_vals = [ u               | (u,Nothing,KType) <- map nm as ]

        used    = map snd named ++ IntMap.elems ns

ppNominalShort :: NominalType -> Doc
ppNominalShort nt =
  kw <+> pp (ntName nt) <+> hsep (map (ppWithNamesPrec nm 9) ps)
  where
  ps = ntParams nt
  nm = addTNames ps emptyNameMap
  kw = case ntDef nt of
         Struct {} -> "newtype"
         Enum {}   -> "enum"
         Abstract {} -> "primitive type"

ppNominalFull :: NominalType -> Doc
ppNominalFull nt =
  case ntDef nt of

    Struct con -> ppKWDef "newtype" ("=" <+> pp (ntConName con) $$ nest 2 fs)
      where fs = vcat [ pp f <.> ":" <+> pp t
                      | (f,t) <- canonicalFields (ntFields con) ]
    Enum cons ->
      ppKWDef "enum" $
      vcat [ pref <+> pp (ecName con) <+> hsep (map (ppPrec 1) (ecFields con))
           | (pref,con) <- zip ("=" : repeat "|") cons
           ]

    Abstract ->
      "primitive type" <+> paramBinds <+> ctrs <+> ppTyUse <+>
                                                        ":" <+> pp (ntKind nt)
      where
      paramBinds =
        case ps of
          [] -> mempty
          _  -> braces (commaSep (map ppBind ps))
      ppBind p = ppWithNamesPrec nm 0 p <+> ":" <+> pp (kindOf p)
      ppC     = ppWithNamesPrec nm 0
      ctrs = case ntConstraints nt of
               [] -> mempty
               _  -> parens (commaSep (map ppC (ntConstraints nt))) <+> "=>"
  where
  ps = ntParams nt
  cs = vcat (map pp (ntConstraints nt))
  nm = addTNames ps emptyNameMap
  ppTyUse = pp (ntName nt) <+> hsep (map (ppWithNamesPrec nm 9) ps)
  ppKWDef kw def = (kw <+> ppTyUse) $$ nest 2 (cs $$ def)



instance PP Schema where
  ppPrec = ppWithNamesPrec IntMap.empty

instance PP (WithNames Schema) where
  ppPrec _ (WithNames s ns)
    | null (sVars s) && null (sProps s) = body
    | otherwise = nest 2 (sep (vars ++ props ++ [body]))
    where
    body = ppWithNames ns1 (sType s)

    vars = case sVars s of
      [] -> []
      vs -> [nest 1 (braces (commaSepFill (map (ppWithNames ns1) vs)))]

    props = case sProps s of
      [] -> []
      ps -> [nest 1 (parens (commaSepFill (map (ppWithNames ns1) ps))) <+> text "=>"]

    ns1 = addTNames (sVars s) ns

instance PP TySyn where
  ppPrec = ppWithNamesPrec IntMap.empty

instance PP (WithNames TySyn) where
  ppPrec _ (WithNames ts ns) =
    nest 2 $ sep
      [ fsep ([text "type"] ++ ctr ++ lhs ++ [char '='])
      , ppWithNames ns1 (tsDef ts)
      ]
    where ns1 = addTNames (tsParams ts) ns
          ctr = case kindResult (kindOf ts) of
                  KProp -> [text "constraint"]
                  _     -> []
          n = tsName ts
          lhs = case (nameFixity n, tsParams ts) of
                  (Just _, [x, y]) ->
                    [ppWithNames ns1 x, pp (nameIdent n), ppWithNames ns1 y]
                  (_, ps) ->
                    [pp n] ++ map (ppWithNames ns1) ps

instance PP NominalType where
  ppPrec = ppWithNamesPrec IntMap.empty

instance PP (WithNames NominalType) where
  ppPrec _  (WithNames nt _) = ppNominalShort nt -- XXX: do the full thing?



-- | The precedence levels used by this pretty-printing instance
-- correspond with parser non-terminals as follows:
--
--   * 0-1: @type@
--
--   * 2: @infix_type@
--
--   * 3: @app_type@
--
--   * 4: @dimensions atype@
--
--   * 5: @atype@
instance PP (WithNames Type) where
  ppPrec prec ty0@(WithNames ty nmMap) =
    case ty of
      TVar a  -> ppWithNames nmMap a
      TNominal nt ts -> optParens (prec > 3)
                                  (fsep (pp (ntName nt) : map (go 5) ts))
      TRec fs -> ppRecord
                    [ pp l <+> text ":" <+> go 0 t | (l,t) <- displayFields fs ]

      _ | Just tinf <- isTInfix ty0 -> optParens (prec > 2)
                                     $ ppInfix 2 isTInfix tinf

      TUser c ts t ->
        withNameDisp $ \disp ->
        case asOrigName c of
          Just og | NotInScope <- getNameFormat og disp ->
              go prec t -- unfold type synonym if not in scope
          _ ->
            case ts of
              [] -> pp c
              _ -> optParens (prec > 3) $ fsep (pp c : map (go 5) ts)

      TCon (TC tc) ts ->
        case (tc,ts) of
          (TCNum n, [])       -> integer n
          (TCInf,   [])       -> text "inf"
          (TCBit,   [])       -> text "Bit"
          (TCInteger, [])     -> text "Integer"
          (TCRational, [])    -> text "Rational"

          (TCIntMod, [n])     -> optParens (prec > 3) $ text "Z" <+> go 5 n

          (TCSeq,   [t1,TCon (TC TCBit) []]) -> brackets (go 0 t1)
          (TCSeq,   [t1,t2])  -> optParens (prec > 4)
                              $ brackets (go 0 t1) <.> go 4 t2

          (TCFun,   [t1,t2])  -> optParens (prec > 1)
                              $ go 2 t1 <+> text "->" <+> go 1 t2

          (TCTuple _, fs)     -> ppTuple $ map (go 0) fs

          (_, _)              -> optParens (prec > 3) $ fsep (pp tc : (map (go 5) ts))

      TCon (PC pc) ts ->
        case (pc,ts) of
          (PEqual, [t1,t2])   -> go 0 t1 <+> text "==" <+> go 0 t2
          (PNeq ,  [t1,t2])   -> go 0 t1 <+> text "!=" <+> go 0 t2
          (PGeq,  [t1,t2])    -> go 0 t1 <+> text ">=" <+> go 0 t2
          (PFin,  [t1])       -> optParens (prec > 3) $ text "fin" <+> (go 5 t1)
          (PPrime,  [t1])     -> optParens (prec > 3) $ text "prime" <+> (go 5 t1)
          (PHas x, [t1,t2])   -> ppSelector x <+> text "of"
                               <+> go 0 t1 <+> text "is" <+> go 0 t2
          (PAnd, [t1,t2])     -> nest 1 (parens (commaSepFill (map (go 0) (t1 : pSplitAnd t2))))

          (PRing, [t1])       -> pp pc <+> go 5 t1
          (PField, [t1])      -> pp pc <+> go 5 t1
          (PIntegral, [t1])   -> pp pc <+> go 5 t1
          (PRound, [t1])      -> pp pc <+> go 5 t1

          (PCmp, [t1])        -> pp pc <+> go 5 t1
          (PSignedCmp, [t1])  -> pp pc <+> go 5 t1
          (PLiteral, [t1,t2]) -> pp pc <+> go 5 t1 <+> go 5 t2
          (PLiteralLessThan, [t1,t2]) -> pp pc <+> go 5 t1 <+> go 5 t2

          (_, _)              -> optParens (prec > 3) $ fsep (pp pc : map (go 5) ts)

      TCon f ts -> optParens (prec > 3) $ fsep (pp f : map (go 5) ts)

    where
    go p t = ppWithNamesPrec nmMap p t

    isTInfix (WithNames (TCon tc [ieLeft',ieRight']) _) =
      do let ieLeft  = WithNames ieLeft' nmMap
             ieRight = WithNames ieRight' nmMap
         (ieOp, ieFixity) <- infixPrimTy tc
         return Infix { .. }

    isTInfix (WithNames (TUser n [ieLeft',ieRight'] _) _)
      | isInfixIdent (nameIdent n) =
      do let ieLeft   = WithNames ieLeft' nmMap
             ieRight  = WithNames ieRight' nmMap
             ieFixity = fromMaybe defaultFixity (nameFixity n)
             ieOp     = nameIdent n
         return Infix { .. }

    isTInfix _ = Nothing



instance PP (WithNames TVar) where

  ppPrec _ (WithNames tv mp) =
    case tv of
      TVBound {} -> nmTxt
      TVFree {} -> "?" <.> nmTxt
    where
    nmTxt
      | Just a <- IntMap.lookup (tvUnique tv) mp = text a
      | otherwise =
          case tv of
            TVBound x ->
              let declNm n = pp n <.> "`" <.> int (tpUnique x) in
              case tpFlav x of
                TPModParam n     -> ppPrefixName n
                TPUnifyVar       -> pickTVarName (tpKind x) (tvarDesc (tpInfo x)) (tpUnique x)
                TPSchemaParam n  -> declNm n
                TPTySynParam n   -> declNm n
                TPPropSynParam n -> declNm n
                TPNominalParam n -> declNm n
                TPPrimParam n    -> declNm n

            TVFree x k _ d -> pickTVarName k (tvarDesc d) x


pickTVarName :: Kind -> TypeSource -> Int -> Doc
pickTVarName k src uni =
  text $
  case src of
    TVFromModParam n       -> using n
    TVFromSignature n      -> using n
    TypeWildCard           -> mk $ case k of
                                     KNum -> "n"
                                     _    -> "a"
    TypeOfRecordField i    -> using i
    TypeOfTupleField n     -> mk ("tup_" ++ show n)
    TypeOfSeqElement       -> mk "a"
    LenOfSeq               -> mk "n"
    TypeParamInstNamed _ i -> using i
    TypeParamInstPos f n   -> mk (sh f ++ "_" ++ show n)
    DefinitionOf x ->
      case nameInfo x of
        GlobalName SystemName og
          | ogModule og == TopModule exprModName -> mk "it"
        _ -> using x
    LenOfCompGen           -> mk "n"
    GeneratorOfListComp    -> "seq"
    TypeOfIfCondExpr       -> "b"
    TypeOfArg ad           -> mk (case argDescrNumber ad of
                                    Nothing -> "arg"
                                    Just n  -> "arg_" ++ show n)
    TypeOfRes              -> "res"
    FunApp                 -> "fun"
    TypeFromUserAnnotation -> "user"
    TypeErrorPlaceHolder   -> "err"
    CasedExpression        -> "case"
    ConPat                 -> "conp"
  where
  sh a      = show (pp a)
  using a   = mk (sh a)
  mk a      = a ++ "`" ++ show uni

instance PP TVar where
  ppPrec = ppWithNamesPrec IntMap.empty

instance PP Type where
  ppPrec n t = ppWithNamesPrec IntMap.empty n t

instance PP TVarInfo where
  ppPrec _ tvinfo = hsep $ [pp (tvarDesc tvinfo)] ++ loc
    where
    loc = if rng == emptyRange then [] else ["at" <+> pp rng]
    rng = tvarSource tvinfo

instance PP ArgDescr where
  ppPrec _ ad = hsep ([which, "argument"] ++ ofFun)
        where
        which = maybe "function" ordinal (argDescrNumber ad)
        ofFun = case argDescrFun ad of
                  Nothing -> []
                  Just f  -> ["of" <+> pp f]


instance PP TypeSource where
  ppPrec _ tvsrc =
    case tvsrc of
      TVFromModParam m    -> "module parameter" <+> pp m
      TVFromSignature x   -> "signature variable" <+> quotes (pp x)
      TypeWildCard        -> "type wildcard (_)"
      TypeOfRecordField l -> "type of field" <+> quotes (pp l)
      TypeOfTupleField n  -> "type of" <+> ordinal n <+> "tuple field"
      TypeOfSeqElement    -> "type of sequence member"
      LenOfSeq            -> "length of sequence"
      TypeParamInstNamed f i -> "type argument" <+> quotes (pp i) <+>
                                          "of" <+> quotes (pp f)
      TypeParamInstPos   f i -> ordinal i <+> "type argument of" <+>
                                                      quotes (pp f)
      DefinitionOf x      -> "the type of" <+> quotes (pp x)
      LenOfCompGen        -> "length of comprehension generator"
      TypeOfArg ad        -> "type of" <+> pp ad
      TypeOfRes             -> "type of function result"
      TypeOfIfCondExpr      -> "type of `if` condition"
      TypeFromUserAnnotation -> "user annotation"
      GeneratorOfListComp    -> "generator in a list comprehension"
      FunApp                -> "function call"
      TypeErrorPlaceHolder  -> "type error place-holder"
      CasedExpression       -> "cased expression"
      ConPat                -> "constructor pattern"

instance PP ModParamNames where
  ppPrec _ ps =
    let tps = Map.elems (mpnTypes ps)
    in
    vcat $ map pp tps ++
          if null (mpnConstraints ps) then [] else
            [ "type constraint" <+>
                parens (commaSep (map (pp . thing) (mpnConstraints ps)))
            ] ++
           [ pp t | t <- Map.elems (mpnTySyn ps) ] ++
           map pp (Map.elems (mpnFuns ps))

instance PP ModTParam where
  ppPrec _ p =
    "type" <+> pp (mtpName p) <+> ":" <+> pp (mtpKind p)

instance PP ModVParam where
  ppPrec _ p = pp (mvpName p) <+> ":" <+> pp (mvpType p)


