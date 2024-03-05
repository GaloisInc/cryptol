-- |
-- Module      :  Cryptol.Parser.AST
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe #-}

{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleInstances #-}
module Cryptol.Parser.AST
  ( -- * Names
    Ident, mkIdent, mkInfix, isInfixIdent, nullIdent, identText
  , ModName, modRange
  , PName(..), getModName, getIdent, mkUnqual, mkQual
  , Named(..)
  , Pass(..)
  , Assoc(..)

    -- * Types
  , Schema(..)
  , TParam(..)
  , Kind(..)
  , Type(..)
  , Prop(..)
  , tsName
  , psName
  , tsFixity
  , psFixity

    -- * Declarations
  , Module
  , ModuleG(..)
  , mDecls        -- XXX: Temporary

  , mImports
  , mModParams
  , mIsFunctor
  , isParamDecl

  , ModuleDefinition(..)
  , ModuleInstanceArgs(..)
  , ModuleInstanceNamedArg(..)
  , ModuleInstanceArg(..)
  , ModuleInstance
  , emptyModuleInstance

  , Program(..)
  , TopDecl(..)
  , Decl(..)
  , Fixity(..), defaultFixity
  , FixityCmp(..), compareFixity
  , TySyn(..)
  , PropSyn(..)
  , Bind(..)
  , BindDef(..), LBindDef
  , BindImpl(..), bindImpl, exprDef
  , Pragma(..)
  , PropertyPragma(..)
  , PropertyType(..)
  , PropertyOptions
  , ExportType(..)
  , TopLevel(..)
  , Import, ImportG(..), ImportSpec(..), ImpName(..), impNameModPath
  , Newtype(..)
  , EnumDecl(..), EnumCon(..)
  , PrimType(..)
  , ParameterType(..)
  , ParameterFun(..)
  , NestedModule(..)
  , Signature(..)
  , SigDecl(..)
  , ModParam(..)
  , ParamDecl(..)
  , PropGuardCase(..)

    -- * Interactive
  , ReplInput(..)

    -- * Expressions
  , Expr(..)
  , Literal(..), NumInfo(..), FracInfo(..)
  , Match(..)
  , Pattern(..)
  , Selector(..)
  , CaseAlt(..)
  , TypeInst(..)
  , UpdField(..)
  , UpdHow(..)
  , FunDesc(..)
  , emptyFunDesc
  , PrefixOp(..)
  , prefixFixity
  , asEApps

    -- * Positions
  , Located(..)
  , LPName, LString, LIdent
  , NoPos(..)

    -- * Pretty-printing
  , cppKind, ppSelector
  ) where

import Cryptol.ModuleSystem.Name (Name, nameModPath, nameIdent)
import Cryptol.ModuleSystem.NamingEnv.Types
import Cryptol.Parser.Name
import Cryptol.Parser.Position
import Cryptol.Parser.Selector
import Cryptol.Utils.Fixity
import Cryptol.Utils.Ident
import Cryptol.Utils.RecordMap
import Cryptol.Utils.PP

import           Data.Map(Map)
import qualified Data.Map as Map
import           Data.List(intersperse)
import           Data.Bits(shiftR)
import           Data.Maybe (catMaybes,mapMaybe)
import           Data.Ratio(numerator,denominator)
import           Data.Text (Text)
import           Numeric(showIntAtBase,showFloat,showHFloat)

import GHC.Generics (Generic)
import Control.DeepSeq

import Prelude ()
import Prelude.Compat

-- AST -------------------------------------------------------------------------

-- | A name with location information.
type LPName    = Located PName

-- | An identifier with location information.
type LIdent    = Located Ident

-- | A string with location information.
type LString  = Located String

-- | A record with located ident fields
type Rec e = RecordMap Ident (Range, e)

newtype Program name = Program [TopDecl name]
                       deriving (Show)

{- | A module for the pre-typechecker phasese. The two parameters are:

  * @mname@ the type of module names. This is because top-level and nested
    modules use differnt types to identify a module.

  * @name@ the type of identifiers used by declarations.
    In the parser this starts off as `PName` and after resolving names
    in the renamer, this becomes `Name`.
-}
data ModuleG mname name = Module
  { mName     :: Located mname              -- ^ Name of the module
  , mDef      :: ModuleDefinition name
  , mInScope  :: NamingEnv
    -- ^ Names in scope inside this module, filled in by the renamer.
    --   Also, for the 'FunctorInstance' case this is not the final result of
    --   the names in scope. The typechecker adds in the names in scope in the
    --   functor, so this will just contain the names in the enclosing scope.
  } deriving (Show, Generic, NFData)


-- | Different flavours of module we have.
data ModuleDefinition name =
    NormalModule [TopDecl name]

  | FunctorInstance (Located (ImpName name))
                    (ModuleInstanceArgs name)
                    (ModuleInstance name)
    -- ^ The instance is filled in by the renamer

  | InterfaceModule (Signature name)
    deriving (Show, Generic, NFData)

{- | Maps names in the original functor with names in the instnace.
Does *NOT* include the parameters, just names for the definitions.
This *DOES* include entrirs for all the name in the instantiated functor,
including names in modules nested inside the functor. -}
type ModuleInstance name = Map name name

emptyModuleInstance :: Ord name => ModuleInstance name
emptyModuleInstance = mempty


-- XXX: Review all places this is used, that it actually makes sense
-- Probably shouldn't exist
mDecls :: ModuleG mname name -> [TopDecl name]
mDecls m =
  case mDef m of
    NormalModule ds         -> ds
    FunctorInstance _ _ _   -> []
    InterfaceModule {}      -> []

-- | Imports of top-level (i.e. "file" based) modules.
mImports :: ModuleG mname name -> [ Located Import ]
mImports m =
  case mDef m of
    NormalModule ds     -> mapMaybe topImp [ li | DImport li <- ds ]
    FunctorInstance {}  -> []
    InterfaceModule sig -> mapMaybe topImp (sigImports sig)
  where
  topImp li = case iModule i of
               ImpTop n -> Just li { thing = i { iModule = n } }
               _        -> Nothing
    where i = thing li


-- | Get the module parameters of a module (new module system)
mModParams :: ModuleG mname name -> [ ModParam name ]
mModParams m = [ p | DModParam p <- mDecls m ]

mIsFunctor :: ModuleG mname nmae -> Bool
mIsFunctor m = any isParamDecl (mDecls m)

isParamDecl :: TopDecl a -> Bool
isParamDecl d =
  case d of
    DModParam {} -> True
    DParamDecl {} -> True
    _ -> False


-- | A top-level module
type Module = ModuleG ModName

-- | A nested module.
newtype NestedModule name = NestedModule (ModuleG name name)
  deriving (Show,Generic,NFData)


modRange :: Module name -> Range
modRange m = rCombs $ catMaybes
    [ getLoc (mName m)
    , getLoc (mImports m)
    , getLoc (mDecls m)
    , Just (Range { from = start, to = start, source = "" })
    ]

-- | A declaration that may only appear at the top level of a module.
-- The module may be nested, however.
data TopDecl name =
    Decl (TopLevel (Decl name))
  | DPrimType (TopLevel (PrimType name))
  | TDNewtype (TopLevel (Newtype name)) -- ^ @newtype T as = t
  | TDEnum (TopLevel (EnumDecl name))   -- ^ @enum T as = cons@
  | Include (Located FilePath)          -- ^ @include File@ (until NoInclude)

  | DParamDecl Range (Signature name)   -- ^ @parameter ...@ (parser only)

  | DModule (TopLevel (NestedModule name))      -- ^ @submodule M where ...@
  | DImport (Located (ImportG (ImpName name)))  -- ^ @import X@
  | DModParam (ModParam name)                   -- ^ @import interface X ...@
  | DInterfaceConstraint (Maybe Text) (Located [Prop name])
    -- ^ @interface constraint@
    deriving (Show, Generic, NFData)


-- | Things that maybe appear in an interface/parameter block.
-- These only exist during parsering.
data ParamDecl name =

    DParameterType (ParameterType name) -- ^ @parameter type T : #@ (parser only)
  | DParameterFun  (ParameterFun name)  -- ^ @parameter someVal : [256]@
                                        -- (parser only)

  | DParameterDecl (SigDecl name)       -- ^ A delcaration in an interface

  | DParameterConstraint [Located (Prop name)]
    -- ^ @parameter type constraint (fin T)@

    deriving (Show, Generic, NFData)


-- | All arguments in a functor instantiation
data ModuleInstanceArgs name =
    DefaultInstArg (Located (ModuleInstanceArg name))
    -- ^ Single parameter instantitaion

  | DefaultInstAnonArg [TopDecl name]
    -- ^ Single parameter instantitaion using this anonymous module.
    -- (parser only)

  | NamedInstArgs  [ModuleInstanceNamedArg name]

    deriving (Show, Generic, NFData)

-- | A named argument in a functor instantiation
data ModuleInstanceNamedArg name =
  ModuleInstanceNamedArg (Located Ident) (Located (ModuleInstanceArg name))
  deriving (Show, Generic, NFData)

-- | An argument in a functor instantiation
data ModuleInstanceArg name =
    ModuleArg (ImpName name)  -- ^ An argument that is a module
  | ParameterArg Ident        -- ^ An argument that is a parameter
  | AddParams                 -- ^ Arguments adds extra parameters to decls.
                              -- ("backtick" import)
    deriving (Show, Generic, NFData)


-- | The name of an imported module
data ImpName name =
    ImpTop    ModName           -- ^ A top-level module
  | ImpNested name              -- ^ The module in scope with the given name
    deriving (Show, Generic, NFData, Eq, Ord)

impNameModPath :: ImpName Name -> ModPath
impNameModPath (ImpTop mn) = TopModule mn
impNameModPath (ImpNested n) = Nested (nameModPath n) (nameIdent n)

-- | A simple declaration.  Generally these are things that can appear
-- both at the top-level of a module and in `where` clauses.
data Decl name = DSignature [Located name] (Schema name)
                 -- ^ A type signature.  Eliminated in NoPat--after NoPat
                 -- signatures are in their associated Bind

               | DFixity !Fixity [Located name]
                 -- ^ A fixity declaration. Eliminated in NoPat---after NoPat
                 -- fixities are in their associated Bind

               | DPragma [Located name] Pragma
                 -- ^ A pragma declaration. Eliminated in NoPat---after NoPat
                 -- fixities are in their associated Bind

               | DBind (Bind name)
                -- ^ A non-recursive binding.

               | DRec [Bind name]
                 -- ^ A group of recursive bindings. Introduced by the renamer.

               | DPatBind (Pattern name) (Expr name)
                 -- ^ A pattern binding. Eliminated in NoPat---after NoPat
                 -- fixities are in their associated Bind

               | DType (TySyn name)
                 -- ^ A type synonym.

               | DProp (PropSyn name)
                 -- ^ A constraint synonym.

               | DLocated (Decl name) Range
                 -- ^ Keeps track of the location of a declaration.

                 deriving (Eq, Show, Generic, NFData, Functor)


-- | A type parameter for a module.
data ParameterType name = ParameterType
  { ptName    :: Located name     -- ^ name of type parameter
  , ptKind    :: Kind             -- ^ kind of parameter
  , ptDoc     :: Maybe Text       -- ^ optional documentation
  , ptFixity  :: Maybe Fixity     -- ^ info for infix use
  , ptNumber  :: !Int             -- ^ number of the parameter
  } deriving (Eq,Show,Generic,NFData)

-- | A value parameter for a module.
data ParameterFun name = ParameterFun
  { pfName   :: Located name      -- ^ name of value parameter
  , pfSchema :: Schema name       -- ^ schema for parameter
  , pfDoc    :: Maybe Text        -- ^ optional documentation
  , pfFixity :: Maybe Fixity      -- ^ info for infix use
  } deriving (Eq,Show,Generic,NFData)


{- | Interface Modules (aka types of functor arguments)

IMPORTANT: Interface Modules are a language construct and are different from
the notion of "interface" in the Cryptol implementation.

Note that the names *defined* in an interface module are only really used in the
other members of the interface module.  When an interface module  is "imported"
as a functor parameter these names are instantiated to new names,
because there could be multiple paramers using the same interface. -}
data Signature name = Signature
  { sigImports      :: ![Located (ImportG (ImpName name))]
    -- ^ Add things in scope
  , sigTypeParams   :: [ParameterType name]     -- ^ Type parameters
  , sigConstraints  :: [Located (Prop name)]
    -- ^ Constraints on the type parameters and type synonyms.
  , sigDecls        :: [SigDecl name]
    -- ^ Type and constraint synonyms
  , sigFunParams    :: [ParameterFun name]      -- ^ Value parameters
  } deriving (Show,Generic,NFData)

-- | A constraint or type synonym declared in an interface.
data SigDecl name =
    SigTySyn (TySyn name) (Maybe Text)
  | SigPropSyn (PropSyn name) (Maybe Text)
    deriving (Show,Generic,NFData)

{- | A module parameter declaration.

> import interface A
> import interface A as B

The name of the parameter is derived from the `as` clause.  If there
is no `as` clause then it is derived from the name of the interface module.

If there is no `as` clause, then the type/value parameters are unqualified,
and otherwise they are qualified.
-}
data ModParam name = ModParam
  { mpSignature     :: Located (ImpName name)  -- ^ Signature for parameter
  , mpAs            :: Maybe ModName        -- ^ Qualified for actual params
  , mpName          :: !Ident
    {- ^ Parameter name (for inst.)
    Note that this is not resolved in the renamer, and is only used
    when instantiating a functor. -}

  , mpDoc           :: Maybe (Located Text) -- ^ Optional documentation
  , mpRenaming      :: !(Map name name)
    {- ^ Filled in by the renamer.
      Maps the actual (value/type) parameter names to the names in the
      interface module. -}
  } deriving (Eq,Show,Generic,NFData)


-- | An import declaration.
data ImportG mname = Import
  { iModule    :: !mname
  , iAs        :: Maybe ModName
  , iSpec      :: Maybe ImportSpec
  , iInst      :: !(Maybe (ModuleInstanceArgs PName))
    -- ^ `iInst' exists only during parsing
  } deriving (Show, Generic, NFData)

type Import = ImportG ModName

-- | The list of names following an import.
data ImportSpec = Hiding [Ident]
                | Only   [Ident]
                  deriving (Eq, Show, Generic, NFData)

-- The 'Maybe Fixity' field is filled in by the NoPat pass.
data TySyn n = TySyn (Located n) (Maybe Fixity) [TParam n] (Type n)
                deriving (Eq, Show, Generic, NFData, Functor)

-- The 'Maybe Fixity' field is filled in by the NoPat pass.
data PropSyn n = PropSyn (Located n) (Maybe Fixity) [TParam n] [Prop n]
                 deriving (Eq, Show, Generic, NFData, Functor)

tsName :: TySyn name -> Located name
tsName (TySyn lqn _ _ _) = lqn

psName :: PropSyn name -> Located name
psName (PropSyn lqn _ _ _) = lqn

tsFixity :: TySyn name -> Maybe Fixity
tsFixity (TySyn _ f _ _) = f

psFixity :: PropSyn name -> Maybe Fixity
psFixity (PropSyn _ f _ _) = f

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
data Bind name = Bind
  { bName      :: Located name            -- ^ Defined thing
  , bParams    :: [Pattern name]          -- ^ Parameters
  , bDef       :: Located (BindDef name)  -- ^ Definition
  , bSignature :: Maybe (Schema name)     -- ^ Optional type sig
  , bInfix     :: Bool                    -- ^ Infix operator?
  , bFixity    :: Maybe Fixity            -- ^ Optional fixity info
  , bPragmas   :: [Pragma]                -- ^ Optional pragmas
  , bMono      :: Bool                    -- ^ Is this a monomorphic binding
  , bDoc       :: Maybe Text              -- ^ Optional doc string
  , bExport    :: !ExportType
  } deriving (Eq, Generic, NFData, Functor, Show)

type LBindDef = Located (BindDef PName)

data BindDef name = DPrim
                  -- | Foreign functions can have an optional cryptol
                  -- implementation
                  | DForeign (Maybe (BindImpl name))
                  | DImpl (BindImpl name)
                    deriving (Eq, Show, Generic, NFData, Functor)

bindImpl :: Bind name -> Maybe (BindImpl name)
bindImpl bind =
  case thing (bDef bind) of
    DPrim       -> Nothing
    DForeign mi -> mi
    DImpl i     -> Just i

data BindImpl name = DExpr (Expr name)
                   | DPropGuards [PropGuardCase name]
                     deriving (Eq, Show, Generic, NFData, Functor)

exprDef :: Expr name -> BindDef name
exprDef = DImpl . DExpr

data PropGuardCase name = PropGuardCase
  { pgcProps :: [Located (Prop name)]
  , pgcExpr  :: Expr name
  }
  deriving (Eq,Generic,NFData,Functor,Show)

data PropertyType = TestType
                  | ProveType
                  | SatType
  deriving (Eq, Show, Generic, NFData)

type PropertyOptions = Map Text (Located Literal)
data PropertyPragma = DefaultPropertyPragma
                    | ConfigurableProperty PropertyType PropertyOptions
                    deriving (Eq, Show, Generic, NFData)

data Pragma   = PragmaNote String
              | Property PropertyPragma

                deriving (Eq, Show, Generic, NFData)

data Newtype name = Newtype
  { nName     :: Located name        -- ^ Type name
  , nParams   :: [TParam name]       -- ^ Type params
  , nConName  :: !name               -- ^ Constructor function name
  , nBody     :: Rec (Type name)     -- ^ Body
  } deriving (Eq, Show, Generic, NFData)

data EnumDecl name = EnumDecl
  { eName     :: Located name               -- ^ Type name
  , eParams   :: [TParam name]              -- ^ Type params
  , eCons     :: [TopLevel (EnumCon name)]  -- ^ Value constructors
  } deriving (Show, Generic, NFData)

data EnumCon name = EnumCon
  { ecName    :: Located name
  , ecFields  :: [Type name]
  } deriving (Show, Generic, NFData)

-- | A declaration for a type with no implementation.
data PrimType name = PrimType { primTName :: Located name
                              , primTKind :: Located Kind
                              , primTCts  :: ([TParam name], [Prop name])
                                -- ^ parameters are in the order used
                                -- by the type constructor.
                              , primTFixity :: Maybe Fixity
                              } deriving (Show,Generic,NFData)

-- | Input at the REPL, which can be an expression, a @let@
-- statement, or empty (possibly a comment).
data ReplInput name = ExprInput (Expr name)
                    | LetInput [Decl name]
                    | EmptyInput
                      deriving (Eq, Show)

-- | Export information for a declaration.
data ExportType = Public
                | Private
                  deriving (Eq, Show, Ord, Generic, NFData)

-- | A top-level module declaration.
data TopLevel a = TopLevel { tlExport :: ExportType
                           , tlDoc    :: Maybe (Located Text)
                           , tlValue  :: a
                           }
  deriving (Show, Generic, NFData, Functor, Foldable, Traversable)


-- | Infromation about the representation of a numeric constant.
data NumInfo  = BinLit Text Int                 -- ^ n-digit binary literal
              | OctLit Text Int                 -- ^ n-digit octal  literal
              | DecLit Text                     -- ^ overloaded decimal literal
              | HexLit Text Int                 -- ^ n-digit hex literal
              | PolyLit Int                     -- ^ polynomial literal
                deriving (Eq, Show, Generic, NFData)

-- | Information about fractional literals.
data FracInfo = BinFrac Text
              | OctFrac Text
              | DecFrac Text
              | HexFrac Text
                deriving (Eq,Show,Generic,NFData)

-- | Literals.
data Literal  = ECNum Integer NumInfo           -- ^ @0x10@  (HexLit 2)
              | ECChar Char                     -- ^ @'a'@
              | ECFrac Rational FracInfo        -- ^ @1.2e3@
              | ECString String                 -- ^ @\"hello\"@
                deriving (Eq, Show, Generic, NFData)

data Expr n   = EVar n                          -- ^ @ x @
              | ELit Literal                    -- ^ @ 0x10 @
              | EGenerate (Expr n)              -- ^ @ generate f @
              | ETuple [Expr n]                 -- ^ @ (1,2,3) @
              | ERecord (Rec (Expr n))          -- ^ @ { x = 1, y = 2 } @
              | ESel (Expr n) Selector          -- ^ @ e.l @
              | EUpd (Maybe (Expr n)) [ UpdField n ]  -- ^ @ { r | x = e } @
              | EList [Expr n]                  -- ^ @ [1,2,3] @
              | EFromTo (Type n) (Maybe (Type n)) (Type n) (Maybe (Type n))
                                                -- ^ @ [1, 5 .. 117 : t] @
              | EFromToBy Bool (Type n) (Type n) (Type n) (Maybe (Type n))
                                                -- ^ @ [1 .. 10 by 2 : t ] @

              | EFromToDownBy Bool (Type n) (Type n) (Type n) (Maybe (Type n))
                                                -- ^ @ [10 .. 1 down by 2 : t ] @
              | EFromToLessThan (Type n) (Type n) (Maybe (Type n))
                                                -- ^ @ [ 1 .. < 10 : t ] @

              | EInfFrom (Expr n) (Maybe (Expr n))-- ^ @ [1, 3 ...] @
              | EComp (Expr n) [[Match n]]      -- ^ @ [ 1 | x <- xs ] @
              | EApp (Expr n) (Expr n)          -- ^ @ f x @
              | EAppT (Expr n) [(TypeInst n)]   -- ^ @ f `{x = 8}, f`{8} @
              | EIf (Expr n) (Expr n) (Expr n)  -- ^ @ if ok then e1 else e2 @
              | ECase (Expr n) [CaseAlt n]      -- ^ @ case e of { P -> e }@
              | EWhere (Expr n) [Decl n]        -- ^ @ 1 + x where { x = 2 } @
              | ETyped (Expr n) (Type n)        -- ^ @ 1 : [8] @
              | ETypeVal (Type n)               -- ^ @ `(x + 1)@, @x@ is a type
              | EFun (FunDesc n) [Pattern n] (Expr n) -- ^ @ \\x y -> x @
              | ELocated (Expr n) Range         -- ^ position annotation

              | ESplit (Expr n)                 -- ^ @ splitAt x @ (Introduced by NoPat)
              | EParens (Expr n)                -- ^ @ (e)   @ (Removed by Fixity)
              | EInfix (Expr n) (Located n) Fixity (Expr n)-- ^ @ a + b @ (Removed by Fixity)
              | EPrefix PrefixOp (Expr n)       -- ^ @ -1, ~1 @
                deriving (Eq, Show, Generic, NFData, Functor)

-- | Prefix operator.
data PrefixOp = PrefixNeg -- ^ @ - @
              | PrefixComplement -- ^ @ ~ @
                deriving (Eq, Show, Generic, NFData)

prefixFixity :: PrefixOp -> Fixity
prefixFixity op = Fixity { fAssoc = LeftAssoc, .. }
  where fLevel = case op of
          PrefixNeg        -> 80
          PrefixComplement -> 100

-- | Description of functions.  Only trivial information is provided here
--   by the parser.  The NoPat pass fills this in as required.
data FunDesc n =
  FunDesc
  { funDescrName      :: Maybe n   -- ^ Name of this function, if it has one
  , funDescrArgOffset :: Int -- ^ number of previous arguments to this function
                             --   bound in surrounding lambdas (defaults to 0)
  }
 deriving (Eq, Show, Generic, NFData, Functor)

emptyFunDesc :: FunDesc n
emptyFunDesc = FunDesc Nothing 0

data UpdField n = UpdField UpdHow [Located Selector] (Expr n)
                                                -- ^ non-empty list @ x.y = e@
                deriving (Eq, Show, Generic, NFData, Functor)

data UpdHow     = UpdSet | UpdFun   -- ^ Are we setting or updating a field.
                deriving (Eq, Show, Generic, NFData)

data TypeInst name = NamedInst (Named (Type name))
                   | PosInst (Type name)
                     deriving (Eq, Show, Generic, NFData, Functor)

data Match name = Match (Pattern name) (Expr name)              -- ^ p <- e
                | MatchLet (Bind name)
                  deriving (Eq, Show, Generic, NFData, Functor)

data Pattern n = PVar (Located n)              -- ^ @ x @
               | PWild                         -- ^ @ _ @
               | PTuple [Pattern n]            -- ^ @ (x,y,z) @
               | PRecord (Rec (Pattern n))     -- ^ @ { x = (a,b,c), y = z } @
               | PList [ Pattern n ]           -- ^ @ [ x, y, z ] @
               | PTyped (Pattern n) (Type n)   -- ^ @ x : [8] @
               | PSplit (Pattern n) (Pattern n)-- ^ @ (x # y) @
               | PCon (Located n) [Pattern n]  -- ^ @ Just x @
               | PLocated (Pattern n) Range    -- ^ Location information
                 deriving (Eq, Show, Generic, NFData, Functor)

data CaseAlt n = CaseAlt (Pattern n) (Expr n)
  deriving (Eq, Show, Generic, NFData, Functor)

data Named a = Named { name :: Located Ident, value :: a }
  deriving (Eq, Show, Foldable, Traversable, Generic, NFData, Functor)

data Schema n = Forall [TParam n] [Prop n] (Type n) (Maybe Range)
  deriving (Eq, Show, Generic, NFData, Functor)

data Kind = KProp | KNum | KType | KFun Kind Kind
  deriving (Eq, Show, Generic, NFData)

data TParam n = TParam { tpName  :: n
                       , tpKind  :: Maybe Kind
                       , tpRange :: Maybe Range
                       }
  deriving (Eq, Show, Generic, NFData, Functor)

data Type n = TFun (Type n) (Type n)  -- ^ @[8] -> [8]@
            | TSeq (Type n) (Type n)  -- ^ @[8] a@
            | TBit                    -- ^ @Bit@
            | TNum Integer            -- ^ @10@
            | TChar Char              -- ^ @'a'@
            | TUser n [Type n]        -- ^ A type variable or synonym
            | TTyApp [Named (Type n)] -- ^ @`{ x = [8], y = Integer }@
            | TRecord (Rec (Type n))  -- ^ @{ x : [8], y : [32] }@
            | TTuple [Type n]         -- ^ @([8], [32])@
            | TWild                   -- ^ @_@, just some type.
            | TLocated (Type n) Range -- ^ Location information
            | TParens (Type n) (Maybe Kind)       -- ^ @ (ty) @
            | TInfix (Type n) (Located n) Fixity (Type n) -- ^ @ ty + ty @
              deriving (Eq, Show, Generic, NFData, Functor)

-- | A 'Prop' is a 'Type' that represents a type constraint.
newtype Prop n = CType (Type n)
  deriving (Eq, Show, Generic, NFData, Functor)


--------------------------------------------------------------------------------
-- Note: When an explicit location is missing, we could use the sub-components
-- to try to estimate a location...


instance AddLoc (Expr n) where
  addLoc x@ELocated{} _ = x
  addLoc x            r = ELocated x r

  dropLoc (ELocated e _) = dropLoc e
  dropLoc e              = e

instance HasLoc (Expr name) where
  getLoc (ELocated _ r) = Just r
  getLoc _              = Nothing

instance HasLoc (TParam name) where
  getLoc (TParam _ _ r) = r

instance AddLoc (TParam name) where
  addLoc (TParam a b _) l = TParam a b (Just l)
  dropLoc (TParam a b _)  = TParam a b Nothing

instance HasLoc (Type name) where
  getLoc (TLocated _ r) = Just r
  getLoc _              = Nothing

instance AddLoc (Type name) where
  addLoc = TLocated

  dropLoc (TLocated e _) = dropLoc e
  dropLoc e              = e

instance AddLoc (Pattern name) where
  addLoc = PLocated

  dropLoc (PLocated e _) = dropLoc e
  dropLoc e              = e

instance HasLoc (Pattern name) where
  getLoc (PLocated _ r) = Just r
  getLoc (PTyped r _)   = getLoc r
  getLoc (PVar x)       = getLoc x
  getLoc _              = Nothing

instance HasLoc (Bind name) where
  getLoc b = getLoc (bName b, bDef b)

instance HasLoc (Match name) where
  getLoc (Match p e)    = getLoc (p,e)
  getLoc (MatchLet b)   = getLoc b

instance HasLoc a => HasLoc (Named a) where
  getLoc l = getLoc (name l, value l)

instance HasLoc (Schema name) where
  getLoc (Forall _ _ _ r) = r

instance AddLoc (Schema name) where
  addLoc  (Forall xs ps t _) r = Forall xs ps t (Just r)
  dropLoc (Forall xs ps t _)   = Forall xs ps t Nothing

instance HasLoc (Decl name) where
  getLoc (DLocated _ r) = Just r
  getLoc _              = Nothing

instance AddLoc (Decl name) where
  addLoc d r             = DLocated d r

  dropLoc (DLocated d _) = dropLoc d
  dropLoc d              = d

instance HasLoc a => HasLoc (TopLevel a) where
  getLoc = getLoc . tlValue

instance HasLoc (TopDecl name) where
  getLoc td =
    case td of
      Decl tld    -> getLoc tld
      DPrimType pt -> getLoc pt
      TDNewtype n -> getLoc n
      TDEnum n -> getLoc n
      Include lfp -> getLoc lfp
      DModule d -> getLoc d
      DImport d -> getLoc d
      DModParam d -> getLoc d
      DParamDecl r _ -> Just r
      DInterfaceConstraint _ ds -> getLoc ds

instance HasLoc (ParamDecl name) where
  getLoc pd =
    case pd of
      DParameterType d -> getLoc d
      DParameterFun d  -> getLoc d
      DParameterDecl d -> getLoc d
      DParameterConstraint d -> getLoc d

instance HasLoc (SigDecl name) where
  getLoc decl =
    case decl of
      SigTySyn ts _    -> getLoc ts
      SigPropSyn ps _  -> getLoc ps

instance HasLoc (ModParam name) where
  getLoc mp = getLoc (mpSignature mp)

instance HasLoc (PrimType name) where
  getLoc pt = Just (rComb (srcRange (primTName pt)) (srcRange (primTKind pt)))

instance HasLoc (ParameterType name) where
  getLoc a = getLoc (ptName a)

instance HasLoc (ParameterFun name) where
  getLoc a = getLoc (pfName a)

instance HasLoc (ModuleG mname name) where
  getLoc m
    | null locs = Nothing
    | otherwise = Just (rCombs locs)
    where
    locs = catMaybes [ getLoc (mName m)
                     , getLoc (mImports m)
                     , getLoc (mDecls m)
                     ]

instance HasLoc (NestedModule name) where
  getLoc (NestedModule m) = getLoc m

instance HasLoc (Newtype name) where
  getLoc n
    | null locs = Nothing
    | otherwise = Just (rCombs locs)
    where
    locs = catMaybes ([ getLoc (nName n)] ++ map (Just . fst . snd) (displayFields (nBody n)))

instance HasLoc (EnumDecl name) where
  getLoc n
    | null locs = Nothing
    | otherwise = Just (rCombs locs)
    where
    locs = catMaybes (getLoc (eName n) : map getLoc (eCons n))

instance HasLoc (EnumCon name) where
  getLoc c
    | null locs = Nothing
    | otherwise = Just (rCombs locs)
    where
    locs = catMaybes (getLoc (ecName c) : map getLoc (ecFields c))



instance HasLoc (TySyn name) where
  getLoc (TySyn x _ _ _) = getLoc x

instance HasLoc (PropSyn name) where
  getLoc (PropSyn x _ _ _) = getLoc x



--------------------------------------------------------------------------------





--------------------------------------------------------------------------------
-- Pretty printing


ppL :: PP a => Located a -> Doc
ppL = pp . thing

ppNamed :: PP a => String -> Named a -> Doc
ppNamed s x = ppL (name x) <+> text s <+> pp (value x)

ppNamed' :: PP a => String -> (Ident, (Range, a)) -> Doc
ppNamed' s (i,(_,v)) = pp i <+> text s <+> pp v



instance (Show name, PPName mname, PPName name) => PP (ModuleG mname name) where
  ppPrec _ = ppModule "module"

instance (Show name, PPName name) => PP (NestedModule name) where
  ppPrec _ (NestedModule m) = ppModule "submodule" m

ppModule :: (Show name, PPName mname, PPName name) =>
  Doc -> ModuleG mname name -> Doc
ppModule kw m = kw' <+> ppL (mName m) <+> pp (mDef m)
  $$ indent 2 (vcat ["/* In scope:", indent 2 (pp (mInScope m)), " */"])
  where
  kw' = case mDef m of
          InterfaceModule {} -> "interface" <+> kw
          _                  -> kw


instance (Show name, PPName name) => PP (ModuleDefinition name) where
  ppPrec _ def =
    case def of
      NormalModule ds -> "where" $$ indent 2 (vcat (map pp ds))
      FunctorInstance f as inst -> vcat ( ("=" <+> pp (thing f) <+> pp as)
                                        : ppInst
                                        )
        where
        ppInst    = if null inst then [] else [ indent 2
                                                  (vcat ("/* Instance:" :
                                                        instLines ++ [" */"]))
                                              ]
        instLines = [ " *" <+> pp k <+> "->" <+> pp v
                    | (k,v) <- Map.toList inst ]
      InterfaceModule s -> ppInterface "where" s


instance (Show name, PPName name) => PP (ModuleInstanceArgs name) where
  ppPrec _ arg =
    case arg of
      DefaultInstArg x -> braces (pp (thing x))
      DefaultInstAnonArg ds -> "where" $$ indent 2 (vcat (map pp ds))
      NamedInstArgs xs -> braces (commaSep (map pp xs))

instance (Show name, PPName name) => PP (ModuleInstanceNamedArg name) where
  ppPrec _ (ModuleInstanceNamedArg x y) = pp (thing x) <+> "=" <+> pp (thing y)


instance (Show name, PPName name) => PP (ModuleInstanceArg name) where
  ppPrec _ arg =
    case arg of
      ModuleArg x    -> pp x
      ParameterArg i -> "parameter" <+> pp i
      AddParams      -> "{}"


instance (Show name, PPName name) => PP (Program name) where
  ppPrec _ (Program ds) = vcat (map pp ds)

instance (Show name, PPName name) => PP (TopDecl name) where
  ppPrec _ top_decl =
    case top_decl of
      Decl    d   -> pp d
      DPrimType p -> pp p
      TDNewtype n -> pp n
      TDEnum n -> pp n
      Include l   -> text "include" <+> text (show (thing l))
      DModule d -> pp d
      DImport i -> pp (thing i)
      DModParam s -> pp s
      DParamDecl _ ds -> ppInterface "parameter" ds
      DInterfaceConstraint _ ds ->
        "interface constraint" <+>
        case map pp (thing ds) of
          [x] -> x
          []  -> "()"
          xs  -> nest 1 (parens (commaSepFill xs))

instance (Show name, PPName name) => PP (ParamDecl name) where
  ppPrec _ pd =
    case pd of
      DParameterFun d -> pp d
      DParameterType d -> pp d
      DParameterDecl d -> pp d
      DParameterConstraint d ->
        "type constraint" <+> parens (commaSep (map (pp . thing) d))

ppInterface :: (Show name, PPName name) => Doc -> Signature name -> Doc
ppInterface kw sig = kw $$ indent 2 (vcat (is ++ ds))
    where
    is = map pp (sigImports sig)
    cs = case sigConstraints sig of
           []  -> []
           cs' -> ["type constraint" <+>
                       parens (commaSep (map (pp . thing) cs'))]
    ds = map pp (sigTypeParams sig)
      ++ map pp (sigDecls sig)
      ++ cs
      ++ map pp (sigFunParams sig)

instance (Show name, PPName name) => PP (SigDecl name) where
  ppPrec p decl =
    case decl of
      SigTySyn ts _   -> ppPrec p ts
      SigPropSyn ps _ -> ppPrec p ps


instance (Show name, PPName name) => PP (ModParam name) where
  ppPrec _ mp = vcat ( mbDoc
                  ++ [ "import interface" <+>
                                    pp (thing (mpSignature mp)) <+> mbAs ]
                  ++ mbRen
                     )
    where
    mbDoc = case mpDoc mp of
              Nothing -> []
              Just d  -> [pp d]
    mbAs  = case mpAs mp of
              Nothing -> mempty
              Just d  -> "as" <+> pp d
    mbRen
      | Map.null (mpRenaming mp) = []
      | otherwise =
        [ indent 2 $ vcat $ "/* Parameters"
                          : [ " *" <+> pp x <+> "->" <+> pp y
                            | (x,y) <- Map.toList (mpRenaming mp) ]
                         ++ [" */"] ]

instance (Show name, PPName name) => PP (PrimType name) where
  ppPrec _ pt =
    "primitive" <+> "type" <+> pp (primTName pt) <+> ":" <+> pp (primTKind pt)

instance (Show name, PPName name) => PP (ParameterType name) where
  ppPrec _ a = text "type" <+>
               ppPrefixName (ptName a) <+> text ":" <+> pp (ptKind a)

instance (Show name, PPName name) => PP (ParameterFun name) where
  ppPrec _ a = ppPrefixName (pfName a) <+> text ":"
                  <+> pp (pfSchema a)


instance (Show name, PPName name) => PP (Decl name) where
  ppPrec n decl =
    case decl of
      DSignature xs s -> commaSep (map ppL xs) <+> text ":" <+> pp s
      DPatBind p e    -> pp p <+> text "=" <+> pp e
      DBind b         -> ppPrec n b
      DRec bs         -> nest 2 (vcat ("recursive" : map (ppPrec n) bs))
      DFixity f ns    -> ppFixity f ns
      DPragma xs p    -> ppPragma xs p
      DType ts        -> ppPrec n ts
      DProp ps        -> ppPrec n ps
      DLocated d _    -> ppPrec n d

ppFixity :: PPName name => Fixity -> [Located name] -> Doc
ppFixity (Fixity LeftAssoc  i) ns = text "infixl" <+> int i <+> commaSep (map pp ns)
ppFixity (Fixity RightAssoc i) ns = text "infixr" <+> int i <+> commaSep (map pp ns)
ppFixity (Fixity NonAssoc   i) ns = text "infix"  <+> int i <+> commaSep (map pp ns)

instance PPName name => PP (Newtype name) where
  ppPrec _ nt = nest 2 $ sep
    [ fsep $ [text "newtype", ppL (nName nt)] ++ map pp (nParams nt) ++ [char '=']
    , ppRecord (map (ppNamed' ":") (displayFields (nBody nt)))
    ]

instance (Show name, PPName name) => PP (EnumDecl name) where
  ppPrec _ ed = nest 2 $ sep
    [ fsep $ [text "enum", ppL (eName ed)] ++ map pp (eParams ed) ++ [char '=']
    , vcat [ pre <+> pp con | (pre, con) <- pres `zip` eCons ed ]
    ]
    where pres = " " : repeat "|"

instance (Show name, PPName name) => PP (EnumCon name) where
  ppPrec _ c = pp (ecName c) <+> hsep (map (ppPrec 1) (ecFields c))

instance (PP mname) => PP (ImportG mname) where
  ppPrec _ d = vcat [ text "import" <+> sep ([pp (iModule d)] ++ mbInst ++
                                                      mbAs ++ mbSpec)
                    , indent 2 mbWhere
                    ]
    where
    mbAs   = maybe [] (\ name -> [text "as" <+> pp name]) (iAs d)
    mbSpec = maybe [] (\x -> [pp x]) (iSpec d)
    mbInst = case iInst d of
                Just (DefaultInstArg x) -> [ braces (pp (thing x)) ]
                Just (NamedInstArgs xs) -> [ braces (commaSep (map pp xs)) ]
                _ -> []
    mbWhere = case iInst d of
                Just (DefaultInstAnonArg ds) ->
                  "where" $$ vcat (map pp ds)
                _ -> mempty
 

instance PP name => PP (ImpName name) where
  ppPrec _ nm =
    case nm of
      ImpTop x    -> pp x
      ImpNested x -> "submodule" <+> pp x

instance PP ImportSpec where
  ppPrec _ s = case s of
    Hiding names -> text "hiding" <+> parens (commaSep (map pp names))
    Only names   ->                   parens (commaSep (map pp names))

-- TODO: come up with a good way of showing the export specification here
instance PP a => PP (TopLevel a) where
  ppPrec _ tl = pp (tlValue tl)


instance PP Pragma where
  ppPrec _ (PragmaNote x) = text x
  ppPrec _ (Property DefaultPropertyPragma) = text "property"

ppPragma :: PPName name => [Located name] -> Pragma -> Doc
ppPragma xs p =
  text "/*" <+> text "pragma" <+> commaSep (map ppL xs) <+> text ":" <+> pp p
  <+> text "*/"

instance (Show name, PPName name) => PP (Bind name) where
  ppPrec _ b = vcat (sig ++ [ ppPragma [f] p | p <- bPragmas b ] ++
                     [hang (def <+> eq) 4 (pp (thing (bDef b)))])
    where def | bInfix b  = lhsOp
              | otherwise = lhs
          f = bName b
          sig = case bSignature b of
                  Nothing -> []
                  Just s  -> [pp (DSignature [f] s)]
          eq  = if bMono b then text ":=" else text "="
          lhs = fsep (ppL f : (map (ppPrec 3) (bParams b)))

          lhsOp = case bParams b of
                    [x,y] -> pp x <+> ppL f <+> pp y
                    xs -> parens (parens (ppL f) <+> fsep (map (ppPrec 0) xs))
                    -- _     -> panic "AST" [ "Malformed infix operator", show b ]


instance (Show name, PPName name) => PP (BindDef name) where
  ppPrec _ DPrim         = text "<primitive>"
  ppPrec p (DForeign mi) = case mi of
                             Just i  -> "(foreign)" <+> ppPrec p i
                             Nothing -> "<foreign>"
  ppPrec p (DImpl i)     = ppPrec p i

instance (Show name, PPName name) => PP (BindImpl name) where
  ppPrec p (DExpr e) = ppPrec p e
  ppPrec _p (DPropGuards _guards) = text "propguards"


instance PPName name => PP (TySyn name) where
  ppPrec _ (TySyn x _ xs t) =
    nest 2 $ sep $
      [ fsep $ [text "type", ppL x] ++ map (ppPrec 1) xs ++ [text "="]
      , pp t
      ]

instance PPName name => PP (PropSyn name) where
  ppPrec _ (PropSyn x _ xs ps) =
    nest 2 $ sep $
      [ fsep $ [text "constraint", ppL x] ++ map (ppPrec 1) xs ++ [text "="]
      , parens (commaSep (map pp ps))
      ]

instance PP Literal where
  ppPrec _ lit =
    case lit of
      ECNum n i     -> ppNumLit n i
      ECChar c      -> text (show c)
      ECFrac n i    -> ppFracLit n i
      ECString s    -> text (show s)

ppFracLit :: Rational -> FracInfo -> Doc
ppFracLit x i
  | toRational dbl == x =
    case i of
      BinFrac _ -> frac
      OctFrac _ -> frac
      DecFrac _ -> text (showFloat dbl "")
      HexFrac _ -> text (showHFloat dbl "")
  | otherwise = frac
  where
  dbl = fromRational x :: Double
  frac = "fraction`" <.> braces
                      (commaSep (map integer [ numerator x, denominator x ]))


ppNumLit :: Integer -> NumInfo -> Doc
ppNumLit n info =
  case info of
    DecLit _   -> integer n
    BinLit _ w -> pad 2  "0b" w
    OctLit _ w -> pad 8  "0o" w
    HexLit _ w -> pad 16 "0x" w
    PolyLit w  -> text "<|" <+> poly w <+> text "|>"
  where
  pad base pref w =
    let txt = showIntAtBase base ("0123456789abcdef" !!) n ""
    in text pref <.> text (replicate (w - length txt) '0') <.> text txt

  poly w = let (res,deg) = bits Nothing [] 0 n
               z | w == 0 = []
                 | Just d <- deg, d + 1 == w = []
                 | otherwise = [polyTerm0 (w-1)]
           in fsep $ intersperse (text "+") $ z ++ map polyTerm res

  polyTerm 0 = text "1"
  polyTerm 1 = text "x"
  polyTerm p = text "x" <.> text "^^" <.> int p

  polyTerm0 0 = text "0"
  polyTerm0 p = text "0" <.> text "*" <.> polyTerm p

  bits d res p num
    | num == 0  = (res,d)
    | even num  = bits d             res  (p + 1) (num `shiftR` 1)
    | otherwise = bits (Just p) (p : res) (p + 1) (num `shiftR` 1)

wrap :: Int -> Int -> Doc -> Doc
wrap contextPrec myPrec doc = optParens (myPrec < contextPrec) doc

isEApp :: Expr n -> Maybe (Expr n, Expr n)
isEApp (ELocated e _)     = isEApp e
isEApp (EApp e1 e2)       = Just (e1,e2)
isEApp _                  = Nothing

asEApps :: Expr n -> (Expr n, [Expr n])
asEApps expr = go expr []
    where go e es = case isEApp e of
                      Nothing       -> (e, es)
                      Just (e1, e2) -> go e1 (e2 : es)

instance PPName name => PP (TypeInst name) where
  ppPrec _ (PosInst t)   = pp t
  ppPrec _ (NamedInst x) = ppNamed "=" x

{- Precedences:
0: lambda, if, where, type annotation
2: infix expression   (separate precedence table)
3: application, prefix expressions
-}
instance (Show name, PPName name) => PP (Expr name) where
  -- Wrap if top level operator in expression is less than `n`
  ppPrec n expr =
    case expr of

      -- atoms
      EVar x        -> ppPrefixName x
      ELit x        -> pp x

      EGenerate x   -> wrap n 3 (text "generate" <+> ppPrec 4 x)

      ETuple es     -> parens (commaSep (map pp es))
      ERecord fs    -> braces (commaSep (map (ppNamed' "=") (displayFields fs)))
      EList es      -> brackets (commaSep (map pp es))
      EFromTo e1 e2 e3 t1 -> brackets (pp e1 <.> step <+> text ".." <+> end)
        where step = maybe mempty (\e -> comma <+> pp e) e2
              end = maybe (pp e3) (\t -> pp e3 <+> colon <+> pp t) t1
      EFromToBy isStrict e1 e2 e3 t1 -> brackets (pp e1 <+> dots <+> pp e2 <+> text "by" <+> end)
        where end = maybe (pp e3) (\t -> pp e3 <+> colon <+> pp t) t1
              dots | isStrict  = text ".. <"
                   | otherwise = text ".."
      EFromToDownBy isStrict e1 e2 e3 t1 -> brackets (pp e1 <+> dots <+> pp e2 <+> text "down by" <+> end)
        where end = maybe (pp e3) (\t -> pp e3 <+> colon <+> pp t) t1
              dots | isStrict  = text ".. >"
                   | otherwise = text ".."
      EFromToLessThan e1 e2 t1 -> brackets (strt <+> text ".. <" <+> end)
        where strt = maybe (pp e1) (\t -> pp e1 <+> colon <+> pp t) t1
              end  = pp e2
      EInfFrom e1 e2 -> brackets (pp e1 <.> step <+> text "...")
        where step = maybe mempty (\e -> comma <+> pp e) e2
      EComp e mss   -> brackets (pp e <> align (vcat (map arm mss)))
        where arm ms = text " |" <+> commaSep (map pp ms)
      EUpd mb fs    -> braces (hd <+> "|" <+> commaSep (map pp fs))
        where hd = maybe "_" pp mb

      ETypeVal t    -> text "`" <.> ppPrec 5 t     -- XXX
      EAppT e ts    -> ppPrec 4 e <.> text "`" <.> braces (commaSep (map pp ts))
      ESel    e l   -> ppPrec 4 e <.> text "." <.> pp l

      -- low prec
      EFun _ xs e   -> wrap n 0 ((text "\\" <.> hsep (map (ppPrec 3) xs)) <+>
                                 text "->" <+> pp e)

      EIf e1 e2 e3  -> wrap n 0 $ sep [ text "if"   <+> pp e1
                                      , text "then" <+> pp e2
                                      , text "else" <+> pp e3 ]

      ECase e as    -> wrap n 0 $ vcat [ "case" <+> pp e <+> "of"
                                       , nest 2 (vcat (map pp as))
                                       ]

      ETyped e t    -> wrap n 0 (ppPrec 2 e <+> text ":" <+> pp t)

      EWhere  e ds  -> wrap n 0 $ align $ vsep
                         [ pp e
                         , hang "where" 2 (vcat (map pp ds))
                         ]

      -- infix applications
      _ | Just ifix <- isInfix expr ->
              optParens (n > 2)
              $ ppInfix 2 isInfix ifix

      EApp _ _      -> let (e, es) = asEApps expr in
                       wrap n 3 (ppPrec 3 e <+> fsep (map (ppPrec 4) es))

      ELocated e _  -> ppPrec n e

      ESplit e      -> wrap n 3 (text "splitAt" <+> ppPrec 4 e)

      EParens e -> parens (pp e)

      -- NOTE: these don't produce correctly parenthesized expressions without
      -- explicit EParens nodes when necessary, since we don't check the actual
      -- fixities of the operators.
      EInfix e1 op _ e2 -> wrap n 0 (pp e1 <+> ppInfixName (thing op) <+> pp e2)

      EPrefix op e  -> wrap n 3 (text (prefixText op) <.> ppPrec 4 e)
   where
   isInfix (EApp (EApp (EVar ieOp) ieLeft) ieRight) = do
     ieFixity <- ppNameFixity ieOp
     return Infix { .. }
   isInfix _ = Nothing
   prefixText PrefixNeg        = "-"
   prefixText PrefixComplement = "~"

instance (Show name, PPName name) => PP (CaseAlt name) where
  ppPrec _ (CaseAlt p e) = vcat [ pp p <+> "->", nest 2 (pp e) ]

instance (Show name, PPName name) => PP (UpdField name) where
  ppPrec _ (UpdField h xs e) = ppNestedSels (map thing xs) <+> pp h <+> pp e

instance PP UpdHow where
  ppPrec _ h = case h of
                 UpdSet -> "="
                 UpdFun -> "->"

instance PPName name => PP (Pattern name) where
  ppPrec n pat =
    case pat of
      PVar x        -> pp (thing x)
      PCon c ps ->
        case ps of
          [] -> pp c
          _  -> wrap n 1 (pp c <+> hsep (map (ppPrec 1) ps))
      PWild         -> char '_'
      PTuple ps     -> ppTuple (map pp ps)
      PRecord fs    -> ppRecord (map (ppNamed' "=") (displayFields fs))
      PList ps      -> ppList (map pp ps)
      PTyped p t    -> wrap n 0 (ppPrec 1 p  <+> text ":" <+> pp t)
      PSplit p1 p2  -> wrap n 1 (ppPrec 1 p1 <+> text "#" <+> ppPrec 1 p2)
      PLocated p _  -> ppPrec n p

instance (Show name, PPName name) => PP (Match name) where
  ppPrec _ (Match p e)  = pp p <+> text "<-" <+> pp e
  ppPrec _ (MatchLet b) = pp b


instance PPName name => PP (Schema name) where
  ppPrec _ (Forall xs ps t _) = sep (vars ++ preds ++ [pp t])
    where vars = case xs of
                   [] -> []
                   _  -> [nest 1 (braces (commaSepFill (map pp xs)))]
          preds = case ps of
                    [] -> []
                    _  -> [nest 1 (parens (commaSepFill (map pp ps))) <+> text "=>"]

instance PP Kind where
  ppPrec _ KType  = text "*"
  ppPrec _ KNum   = text "#"
  ppPrec _ KProp  = text "@"
  ppPrec n (KFun k1 k2) = wrap n 1 (ppPrec 1 k1 <+> "->" <+> ppPrec 0 k2)

-- | "Conversational" printing of kinds (e.g., to use in error messages)
cppKind :: Kind -> Doc
cppKind KType     = text "a value type"
cppKind KNum      = text "a numeric type"
cppKind KProp     = text "a constraint type"
cppKind (KFun {}) = text "a type-constructor type"

instance PPName name => PP (TParam name) where
  ppPrec n (TParam p Nothing _)   = ppPrec n p
  ppPrec n (TParam p (Just k) _)  = wrap n 1 (pp p <+> text ":" <+> pp k)

-- 4: atomic type expression
-- 3: [_]t or application
-- 2: infix type
-- 1: function type
instance PPName name => PP (Type name) where
  ppPrec n ty =
    case ty of
      TWild          -> text "_"
      TTuple ts      -> parens $ commaSep $ map pp ts
      TTyApp fs      -> braces $ commaSep $ map (ppNamed " = ") fs
      TRecord fs     -> braces $ commaSep $ map (ppNamed' ":") (displayFields fs)
      TBit           -> text "Bit"
      TNum x         -> integer x
      TChar x        -> text (show x)
      TSeq t1 TBit   -> brackets (pp t1)
      TSeq t1 t2     -> optParens (n > 3)
                      $ brackets (pp t1) <.> ppPrec 3 t2

      TUser f []     -> ppPrefixName f

      TUser f ts     -> optParens (n > 3)
                      $ ppPrefixName f <+> fsep (map (ppPrec 4) ts)

      TFun t1 t2     -> optParens (n > 1)
                      $ sep [ppPrec 2 t1 <+> text "->", ppPrec 1 t2]

      TLocated t _   -> ppPrec n t

      TParens t mb   -> parens
                          case mb of
                            Nothing -> pp t
                            Just k  -> pp t <+> ":" <+> pp k

      TInfix t1 o _ t2 -> optParens (n > 2)
                        $ sep [ppPrec 2 t1 <+> ppInfixName o, ppPrec 3 t2]


instance PPName name => PP (Prop name) where
  ppPrec n (CType t) = ppPrec n t

instance PPName name => PP [Prop name] where
  ppPrec n props = parens . commaSep . fmap (ppPrec n) $ props

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

instance NoPos Range where
  noPos _ = Range { from = Position 0 0, to = Position 0 0, source = "" }

instance NoPos t => NoPos [t]       where noPos = fmap noPos
instance NoPos t => NoPos (Maybe t) where noPos = fmap noPos
instance (NoPos a, NoPos b) => NoPos (a,b) where
  noPos (a,b) = (noPos a, noPos b)

instance NoPos (Program name) where
  noPos (Program x) = Program (noPos x)

instance NoPos (ModuleG mname name) where
  noPos m = Module { mName      = mName m
                   , mDef       = noPos (mDef m)
                   , mInScope   = mInScope m
                   }

instance NoPos (ModuleDefinition name) where
  noPos m =
    case m of
      NormalModule ds         -> NormalModule (noPos ds)
      FunctorInstance f as ds -> FunctorInstance (noPos f) (noPos as) ds
      InterfaceModule s       -> InterfaceModule (noPos s)

instance NoPos (ModuleInstanceArgs name) where
  noPos as =
    case as of
      DefaultInstArg a      -> DefaultInstArg (noPos a)
      DefaultInstAnonArg ds -> DefaultInstAnonArg (noPos ds)
      NamedInstArgs xs      -> NamedInstArgs (noPos xs)

instance NoPos (ModuleInstanceNamedArg name) where
  noPos (ModuleInstanceNamedArg x y) =
    ModuleInstanceNamedArg (noPos x) (noPos y)

instance NoPos (NestedModule name) where
  noPos (NestedModule m) = NestedModule (noPos m)

instance NoPos (TopDecl name) where
  noPos decl =
    case decl of
      Decl    x   -> Decl     (noPos x)
      DPrimType t -> DPrimType (noPos t)
      TDNewtype n -> TDNewtype(noPos n)
      TDEnum n -> TDEnum (noPos n)
      Include x   -> Include  (noPos x)
      DModule d -> DModule (noPos d)
      DImport d -> DImport (noPos d)
      DModParam d -> DModParam (noPos d)
      DParamDecl _ ds -> DParamDecl rng (noPos ds)
        where rng = Range { from = Position 0 0, to = Position 0 0, source = "" }
      DInterfaceConstraint d ds -> DInterfaceConstraint d (noPos (noPos <$> ds))

instance NoPos (ParamDecl name) where
  noPos pd =
    case pd of
      DParameterFun d  -> DParameterFun (noPos d)
      DParameterType d -> DParameterType (noPos d)
      DParameterDecl d -> DParameterDecl (noPos d)
      DParameterConstraint d -> DParameterConstraint (noPos d)

instance NoPos (Signature name) where
  noPos sig = Signature { sigImports = sigImports sig
                        , sigTypeParams = map noPos (sigTypeParams sig)
                        , sigDecls = map noPos (sigDecls sig)
                        , sigConstraints = map noPos (sigConstraints sig)
                        , sigFunParams = map noPos (sigFunParams sig)
                        }

instance NoPos (SigDecl name) where
  noPos decl =
    case decl of
      SigTySyn ts mb   -> SigTySyn (noPos ts) mb
      SigPropSyn ps mb -> SigPropSyn (noPos ps) mb

instance NoPos (ModParam name) where
  noPos mp = ModParam { mpSignature = noPos (mpSignature mp)
                      , mpAs        = mpAs mp
                      , mpName      = mpName mp
                      , mpDoc       = noPos <$> mpDoc mp
                      , mpRenaming  = mpRenaming mp
                      }

instance NoPos (PrimType name) where
  noPos x = x

instance NoPos (ParameterType name) where
  noPos a = a

instance NoPos (ParameterFun x) where
  noPos x = x { pfSchema = noPos (pfSchema x) }

instance NoPos a => NoPos (TopLevel a) where
  noPos tl = tl { tlValue = noPos (tlValue tl) }

instance NoPos (Decl name) where
  noPos decl =
    case decl of
      DSignature x y   -> DSignature (noPos x) (noPos y)
      DPragma    x y   -> DPragma    (noPos x) (noPos y)
      DPatBind   x y   -> DPatBind   (noPos x) (noPos y)
      DFixity f ns     -> DFixity f (noPos ns)
      DBind      x     -> DBind      (noPos x)
      DRec       bs    -> DRec       (map noPos bs)
      DType      x     -> DType      (noPos x)
      DProp      x     -> DProp      (noPos x)
      DLocated   x _   -> noPos x

instance NoPos (Newtype name) where
  noPos n = Newtype { nName     = noPos (nName n)
                    , nParams   = nParams n
                    , nConName  = nConName n
                    , nBody     = fmap noPos (nBody n)
                    }

instance NoPos (EnumDecl name) where
  noPos n = EnumDecl { eName    = noPos (eName n)
                     , eParams  = eParams n
                     , eCons    = map noPos (eCons n)
                     }

instance NoPos (EnumCon name) where
  noPos c = EnumCon { ecName = noPos (ecName c), ecFields = noPos (ecFields c) }

instance NoPos (Bind name) where
  noPos x = Bind { bName      = noPos (bName      x)
                 , bParams    = noPos (bParams    x)
                 , bDef       = noPos (bDef       x)
                 , bSignature = noPos (bSignature x)
                 , bInfix     = bInfix x
                 , bFixity    = bFixity x
                 , bPragmas   = noPos (bPragmas   x)
                 , bMono      = bMono x
                 , bDoc       = bDoc x
                 , bExport    = bExport x
                 }

instance NoPos Pragma where
  noPos p@(PragmaNote {})   = p
  noPos p@(Property DefaultPropertyPragma)  = p



instance NoPos (TySyn name) where
  noPos (TySyn x f y z) = TySyn (noPos x) f (noPos y) (noPos z)

instance NoPos (PropSyn name) where
  noPos (PropSyn x f y z) = PropSyn (noPos x) f (noPos y) (noPos z)

instance NoPos (Expr name) where
  noPos expr =
    case expr of
      EVar x          -> EVar     x
      ELit x          -> ELit     x
      EGenerate x     -> EGenerate (noPos x)
      ETuple x        -> ETuple   (noPos x)
      ERecord x       -> ERecord  (fmap noPos x)
      ESel x y        -> ESel     (noPos x) y
      EUpd x y        -> EUpd     (noPos x) (noPos y)
      EList x         -> EList    (noPos x)
      EFromTo x y z t -> EFromTo  (noPos x) (noPos y) (noPos z) (noPos t)
      EFromToBy isStrict x y z t
                      -> EFromToBy isStrict (noPos x) (noPos y) (noPos z) (noPos t)
      EFromToDownBy isStrict x y z t
                      -> EFromToDownBy isStrict (noPos x) (noPos y) (noPos z) (noPos t)
      EFromToLessThan x y t -> EFromToLessThan (noPos x) (noPos y) (noPos t)
      EInfFrom x y    -> EInfFrom (noPos x) (noPos y)
      EComp x y       -> EComp    (noPos x) (noPos y)
      EApp  x y       -> EApp     (noPos x) (noPos y)
      EAppT x y       -> EAppT    (noPos x) (noPos y)
      EIf   x y z     -> EIf      (noPos x) (noPos y) (noPos z)
      EWhere x y      -> EWhere   (noPos x) (noPos y)
      ETyped x y      -> ETyped   (noPos x) (noPos y)
      ETypeVal x      -> ETypeVal (noPos x)
      EFun dsc x y    -> EFun dsc (noPos x) (noPos y)
      ELocated x _    -> noPos x

      ESplit x        -> ESplit (noPos x)
      EParens e       -> EParens (noPos e)
      EInfix x y f z  -> EInfix (noPos x) y f (noPos z)
      EPrefix op x    -> EPrefix op (noPos x)
      ECase x y       -> ECase (noPos x) (noPos y)

instance NoPos (UpdField name) where
  noPos (UpdField h xs e) = UpdField h xs (noPos e)

instance NoPos (TypeInst name) where
  noPos (PosInst ts)   = PosInst (noPos ts)
  noPos (NamedInst fs) = NamedInst (noPos fs)

instance NoPos (Match name) where
  noPos (Match x y)  = Match (noPos x) (noPos y)
  noPos (MatchLet b) = MatchLet (noPos b)

instance NoPos (CaseAlt name) where
  noPos (CaseAlt p e) = CaseAlt (noPos p) (noPos e)

instance NoPos (Pattern name) where
  noPos pat =
    case pat of
      PVar x       -> PVar    (noPos x)
      PWild        -> PWild
      PTuple x     -> PTuple  (noPos x)
      PRecord x    -> PRecord (fmap noPos x)
      PList x      -> PList   (noPos x)
      PTyped x y   -> PTyped  (noPos x) (noPos y)
      PSplit x y   -> PSplit  (noPos x) (noPos y)
      PLocated x _ -> noPos x
      PCon n ps    -> PCon n (noPos ps)

instance NoPos (Schema name) where
  noPos (Forall x y z _) = Forall (noPos x) (noPos y) (noPos z) Nothing

instance NoPos (TParam name) where
  noPos (TParam x y _)  = TParam x y Nothing

instance NoPos (Type name) where
  noPos ty =
    case ty of
      TWild         -> TWild
      TUser x y     -> TUser    x         (noPos y)
      TTyApp x      -> TTyApp   (noPos x)
      TRecord x     -> TRecord  (fmap noPos x)
      TTuple x      -> TTuple   (noPos x)
      TFun x y      -> TFun     (noPos x) (noPos y)
      TSeq x y      -> TSeq     (noPos x) (noPos y)
      TBit          -> TBit
      TNum n        -> TNum n
      TChar n       -> TChar n
      TLocated x _  -> noPos x
      TParens x k   -> TParens (noPos x) k
      TInfix x y f z-> TInfix (noPos x) y f (noPos z)

instance NoPos (Prop name) where
  noPos (CType t) = CType (noPos t)
