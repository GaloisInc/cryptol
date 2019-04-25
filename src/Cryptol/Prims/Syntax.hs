{-# Language DeriveGeneric, DeriveAnyClass #-}
module Cryptol.Prims.Syntax where

import GHC.Generics (Generic)
import Control.DeepSeq
import qualified Data.Map as Map

import Cryptol.Parser.Name
import Cryptol.Parser.Selector
import Cryptol.Parser.Fixity
import qualified Cryptol.ModuleSystem.Name as M
import Cryptol.Utils.Ident
import Cryptol.Utils.PP

-- | Information about a user visible built-in type.
data PrimTy = PrimTy
  { primTyCon     :: !TCon            -- ^ Use this ty-con (renamer)
  , primTyIdent   :: !Ident           -- ^ This is what it's called
  , primTyDoc     :: !String          -- ^ Documentation
  , primTyFixity  :: !(Maybe Fixity)  -- ^ Precedence, for infix ones
  }

instance Eq PrimTy where
  x == y = primTyCon x == primTyCon y

instance Ord PrimTy where
  compare x y = compare (primTyCon x) (primTyCon y)


-- | This list should contain all user-visible built-in types.
primTyList :: [ PrimTy ]
primTyList =
  [ -- Value type constructors -------------------------------------------------

    tPrefix "inf"             TC TCInf
    "A numeric type representing infinity."

  , tPrefix "Bit"             TC TCBit
    "The type of boolean values."

  , tPrefix "Integer"         TC TCInteger
    "The type of unbounded integers."

  , tPrefix "Z"               TC TCIntMod
    "'Z n' is the type of integers, modulo 'n'."


    -- Predicate constructors --------------------------------------------------

  , tInfix "=="                PC PEqual      (n 20)
    "Assert that two numeric types are equal."

  , tInfix "!="                PC PNeq        (n 20)
    "Assert that two numeric types are different."

  , tInfix ">="                PC PGeq        (n 30)
    "Assert that the first numeric type is larger than, or equal to the second."

  , tPrefix "fin"              PC PFin
    "Assert that a numeric type is a proper natural number (not 'inf')."

  , tPrefix "Zero"             PC PZero
    "Value types that have a notion of 'zero'."

  , tPrefix "Logic"            PC PLogic
    "Value types that support logical operations."

  , tPrefix "Arith"            PC PArith
    "Value types that support arithmetic."

  , tPrefix "Cmp"              PC PCmp
    "Value types that support unsigned comparisons."

  , tPrefix "SignedCmp"        PC PSignedCmp
    "Value types that support signed comparisons."

  , tPrefix "Literal"         PC PLiteral
    "'Literal n a' asserts that type 'a' contains the number 'n'."



    -- Type functions ------------------------------------------------

  , tInfix  "+"                TF TCAdd       (l 80)
    "Add numeric types."

  , tInfix  "-"                TF TCSub       (l 80)
    "Subtract numeric types."

  , tInfix  "*"                TF TCMul       (l 90)
    "Multiply numeric types."

  , tInfix  "/"                TF TCDiv       (l 90)
    "Divide numeric types, rounding down."

  , tInfix  "%"                TF TCMod       (l 90)
    "Remainder of numeric type division."

  , tInfix  "^^"               TF TCExp       (r 95)
    "Exponentiate numeric types."

  , tPrefix "width"            TF TCWidth
    "The number of bits required to represent the value of a numeric type."

  , tPrefix "min"              TF TCMin
    "The smaller of two numeric types."

  , tPrefix "max"              TF TCMax
    "The larger of two numeric types."

  , tInfix  "/^"               TF TCCeilDiv    (l 90)
    "Divide numeric types, rounding up."

  , tInfix  "%^"               TF TCCeilMod    (l 90)
    "How much we need to add to make a proper multiple of the second argument."

  , tPrefix "lengthFromThenTo" TF TCLenFromThenTo
    "The length of an enumeration."
  ]
  where
  r x = Fixity { fAssoc = RightAssoc, fLevel = x }
  l x = Fixity { fAssoc = LeftAssoc,  fLevel = x }
  n x = Fixity { fAssoc = NonAssoc,   fLevel = x }

  tPrefix x mk tc d =
    PrimTy { primTyCon    = mk tc
           , primTyIdent  = packIdent x
           , primTyDoc    = d
           , primTyFixity = Nothing
           }

  tInfix x mk tc f d =
    PrimTy { primTyCon    = mk tc
           , primTyIdent  = packInfix x
           , primTyDoc    = d
           , primTyFixity = Just f
           }

--------------------------------------------------------------------------------
-- Indexes for quick access

-- | Construct an index for quick lookup of primtys.
primTyIx :: Ord a => (PrimTy -> Maybe a) -> a -> Maybe PrimTy
primTyIx toKey = \x -> Map.lookup x mp
  where mp = Map.fromList [ (k,x) | x <- primTyList, Just k <- [ toKey x ] ]
{-# Inline primTyIx #-}


-- | Lookup a prim type by a parser name.
primTyFromPName :: PName -> Maybe PrimTy
primTyFromPName = primTyIx $ \t -> Just (mkUnqual (primTyIdent t))


-- | Lookup if a ty con is a primitive.
primTyFromTC :: TCon -> Maybe PrimTy
primTyFromTC = primTyIx $ \t -> Just (primTyCon t)

-- | Lookup a 'TFun' prim type.
primTyFromTF :: TFun -> Maybe PrimTy
primTyFromTF = primTyIx $ \t ->
  case primTyCon t of
    TF tf -> Just tf
    _     -> Nothing


-- | Lookup a 'PC' prim type.
primTyFromPC :: PC -> Maybe PrimTy
primTyFromPC = primTyIx $ \t ->
  case primTyCon t of
    PC tf -> Just tf
    _     -> Nothing



--------------------------------------------------------------------------------

infixr 5 :->

-- | Kinds, classify types.
data Kind   = KType
            | KNum
            | KProp
            | Kind :-> Kind
              deriving (Eq, Ord, Show, Generic, NFData)

class HasKind t where
  kindOf :: t -> Kind

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
      TCInteger -> KType
      TCIntMod  -> KNum :-> KType
      TCSeq     -> KNum :-> KType :-> KType
      TCFun     -> KType :-> KType :-> KType
      TCTuple n -> foldr (:->) KType (replicate n KType)
      TCNewtype x -> kindOf x
      TCAbstract x -> kindOf x

instance HasKind PC where
  kindOf pc =
    case pc of
      PEqual     -> KNum :-> KNum :-> KProp
      PNeq       -> KNum :-> KNum :-> KProp
      PGeq       -> KNum :-> KNum :-> KProp
      PFin       -> KNum :-> KProp
      PHas _     -> KType :-> KType :-> KProp
      PZero      -> KType :-> KProp
      PLogic     -> KType :-> KProp
      PArith     -> KType :-> KProp
      PCmp       -> KType :-> KProp
      PSignedCmp -> KType :-> KProp
      PLiteral   -> KNum :-> KType :-> KProp
      PAnd       -> KProp :-> KProp :-> KProp
      PTrue      -> KProp

instance HasKind TFun where
  kindOf tfun =
    case tfun of
      TCWidth   -> KNum :-> KNum

      TCAdd     -> KNum :-> KNum :-> KNum
      TCSub     -> KNum :-> KNum :-> KNum
      TCMul     -> KNum :-> KNum :-> KNum
      TCDiv     -> KNum :-> KNum :-> KNum
      TCMod     -> KNum :-> KNum :-> KNum
      TCExp     -> KNum :-> KNum :-> KNum
      TCMin     -> KNum :-> KNum :-> KNum
      TCMax     -> KNum :-> KNum :-> KNum
      TCCeilDiv -> KNum :-> KNum :-> KNum
      TCCeilMod -> KNum :-> KNum :-> KNum

      TCLenFromThenTo -> KNum :-> KNum :-> KNum :-> KNum



-- | Type constants.
data TCon   = TC TC | PC PC | TF TFun | TError Kind TCErrorMessage
              deriving (Show, Eq, Ord, Generic, NFData)


-- | Predicate symbols.
-- If you add additional user-visible constructors, please update 'primTys'.
data PC     = PEqual        -- ^ @_ == _@
            | PNeq          -- ^ @_ /= _@
            | PGeq          -- ^ @_ >= _@
            | PFin          -- ^ @fin _@

            -- classes
            | PHas Selector -- ^ @Has sel type field@ does not appear in schemas
            | PZero         -- ^ @Zero _@
            | PLogic        -- ^ @Logic _@
            | PArith        -- ^ @Arith _@
            | PCmp          -- ^ @Cmp _@
            | PSignedCmp    -- ^ @SignedCmp _@
            | PLiteral      -- ^ @Literal _ _@

            | PAnd          -- ^ This is useful when simplifying things in place
            | PTrue         -- ^ Ditto
              deriving (Show, Eq, Ord, Generic, NFData)

-- | 1-1 constants.
-- If you add additional user-visible constructors, please update 'primTys'.
data TC     = TCNum Integer            -- ^ Numbers
            | TCInf                    -- ^ Inf
            | TCBit                    -- ^ Bit
            | TCInteger                -- ^ Integer
            | TCIntMod                 -- ^ @Z _@
            | TCSeq                    -- ^ @[_] _@
            | TCFun                    -- ^ @_ -> _@
            | TCTuple Int              -- ^ @(_, _, _)@
            | TCAbstract UserTC        -- ^ An abstract type
            | TCNewtype UserTC         -- ^ user-defined, @T@
              deriving (Show, Eq, Ord, Generic, NFData)


data UserTC = UserTC M.Name Kind
              deriving (Show, Generic, NFData)

instance Eq UserTC where
  UserTC x _ == UserTC y _ = x == y

instance Ord UserTC where
  compare (UserTC x _) (UserTC y _) = compare x y




data TCErrorMessage = TCErrorMessage
  { tcErrorMessage :: !String
    -- XXX: Add location?
  } deriving (Show, Eq, Ord, Generic, NFData)


-- | Built-in type functions.
-- If you add additional user-visible constructors,
-- please update 'primTys' in "Cryptol.Prims.Types".
data TFun

  = TCAdd                 -- ^ @ : Num -> Num -> Num @
  | TCSub                 -- ^ @ : Num -> Num -> Num @
  | TCMul                 -- ^ @ : Num -> Num -> Num @
  | TCDiv                 -- ^ @ : Num -> Num -> Num @
  | TCMod                 -- ^ @ : Num -> Num -> Num @
  | TCExp                 -- ^ @ : Num -> Num -> Num @
  | TCWidth               -- ^ @ : Num -> Num @
  | TCMin                 -- ^ @ : Num -> Num -> Num @
  | TCMax                 -- ^ @ : Num -> Num -> Num @
  | TCCeilDiv             -- ^ @ : Num -> Num -> Num @
  | TCCeilMod             -- ^ @ : Num -> Num -> Num @

  -- Computing the lengths of explicit enumerations
  | TCLenFromThenTo       -- ^ @ : Num -> Num -> Num -> Num@
    -- Example: @[ 1, 5 .. 9 ] :: [lengthFromThenTo 1 5 9][b]@

    deriving (Show, Eq, Ord, Bounded, Enum, Generic, NFData)



--------------------------------------------------------------------------------
-- Pretty printing

instance PP Kind where
  ppPrec p k = case k of
    KType   -> char '*'
    KNum    -> char '#'
    KProp   -> text "Prop"
    l :-> r -> optParens (p >= 1) (sep [ppPrec 1 l, text "->", ppPrec 0 r])

instance PP TCon where
  ppPrec _ (TC tc)        = pp tc
  ppPrec _ (PC tc)        = pp tc
  ppPrec _ (TF tc)        = pp tc
  ppPrec _ (TError _ msg) = pp msg

instance PPName TCon where
  ppNameFixity (TC _)       = Nothing
  ppNameFixity (PC _)       = Nothing
  ppNameFixity (TF tf)      = ppNameFixity tf
  ppNameFixity (TError _ _) = Nothing

  ppPrefixName (TC tc) = pp tc
  ppPrefixName (PC pc) = pp pc
  ppPrefixName (TF tf) = ppPrefixName tf
  ppPrefixName (TError _ msg) = pp msg

  ppInfixName (TC tc) = pp tc
  ppInfixName (PC pc) = pp pc
  ppInfixName (TF tf) = ppInfixName tf
  ppInfixName (TError _ msg) = pp msg

instance PP TCErrorMessage where
  ppPrec _ tc = parens (text "error:" <+> text (tcErrorMessage tc))

instance PP PC where
  ppPrec _ x =
    case x of
      PEqual     -> text "(==)"
      PNeq       -> text "(/=)"
      PGeq       -> text "(>=)"
      PFin       -> text "fin"
      PHas sel   -> parens (ppSelector sel)
      PZero      -> text "Zero"
      PLogic     -> text "Logic"
      PArith     -> text "Arith"
      PCmp       -> text "Cmp"
      PSignedCmp -> text "SignedCmp"
      PLiteral   -> text "Literal"
      PTrue      -> text "True"
      PAnd       -> text "(&&)"

instance PP TC where
  ppPrec _ x =
    case x of
      TCNum n   -> integer n
      TCInf     -> text "inf"
      TCBit     -> text "Bit"
      TCInteger -> text "Integer"
      TCIntMod  -> text "Z"
      TCSeq     -> text "[]"
      TCFun     -> text "(->)"
      TCTuple 0 -> text "()"
      TCTuple 1 -> text "(one tuple?)"
      TCTuple n -> parens $ hcat $ replicate (n-1) comma
      TCNewtype u -> pp u
      TCAbstract u -> pp u

instance PP UserTC where
  ppPrec p (UserTC x _) = ppPrec p x




instance PPName TFun where

  ppNameFixity f =
    do pt <- primTyFromTF f
       fi <- primTyFixity pt
       return (fAssoc fi, fLevel fi)

  ppPrefixName TCAdd     = text "(+)"
  ppPrefixName TCSub     = text "(-)"
  ppPrefixName TCMul     = text "(*)"
  ppPrefixName TCDiv     = text "(/)"
  ppPrefixName TCMod     = text "(%)"
  ppPrefixName TCExp     = text "(^^)"
  ppPrefixName TCCeilDiv = text "(/^)"
  ppPrefixName TCCeilMod = text "(%^)"
  ppPrefixName f         = pp f

  ppInfixName TCAdd     = text "+"
  ppInfixName TCSub     = text "-"
  ppInfixName TCMul     = text "*"
  ppInfixName TCDiv     = text "/"
  ppInfixName TCMod     = text "%"
  ppInfixName TCExp     = text "^^"
  ppInfixName TCCeilDiv = text "/^"
  ppInfixName TCCeilMod = text "%^"
  ppInfixName f         = error $ "Not a prefix type function: " ++ show (pp f)

instance PP TFun where
  ppPrec _ tcon =
    case tcon of
      TCAdd             -> text "+"
      TCSub             -> text "-"
      TCMul             -> text "*"
      TCDiv             -> text "/"
      TCMod             -> text "%"
      TCExp             -> text "^^"
      TCWidth           -> text "width"
      TCMin             -> text "min"
      TCMax             -> text "max"
      TCCeilDiv         -> text "/^"
      TCCeilMod         -> text "%^"
      TCLenFromThenTo   -> text "lengthFromThenTo"
