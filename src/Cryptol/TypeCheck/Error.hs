{-# Language FlexibleInstances, DeriveGeneric, DeriveAnyClass #-}
module Cryptol.TypeCheck.Error where


import qualified Data.IntMap as IntMap
import qualified Data.Set as Set
import Control.DeepSeq(NFData)
import GHC.Generics(Generic)
import Data.List((\\))

import qualified Cryptol.Parser.AST as P
import Cryptol.Parser.Position(Range,Located)
import Cryptol.TypeCheck.PP
import Cryptol.TypeCheck.Type
import Cryptol.TypeCheck.InferTypes
import Cryptol.TypeCheck.Subst
import Cryptol.Utils.Ident(Ident)
import Cryptol.ModuleSystem.Name(Name)

data Warning  = DefaultingKind (P.TParam Name) P.Kind
              | DefaultingWildType P.Kind
              | DefaultingTo Doc Type
                deriving (Show, Generic, NFData)

-- | Various errors that might happen during type checking/inference
data Error    = ErrorMsg Doc
                -- ^ Just say this

              | KindMismatch Kind Kind
                -- ^ Expected kind, inferred kind

              | TooManyTypeParams Int Kind
                -- ^ Number of extra parameters, kind of result
                -- (which should not be of the form @_ -> _@)

              | TooManyTySynParams Name Int
                -- ^ Type-synonym, number of extra params

              | TooFewTySynParams Name Int
                -- ^ Type-synonym, number of missing params

              | RepeatedTyParams [P.TParam Name]
                -- ^ Type parameters with the same name (in definition)

              | RepeatedDefinitions Name [Range]
                -- ^ Multiple definitions for the same name

              | RecursiveTypeDecls [Name]
                -- ^ The type synonym declarations are recursive

              | UndefinedTypeSynonym Name
                -- ^ Use of a type synonym that was not defined

              | UndefinedVariable Name
                -- ^ Use of a variable that was not defined

              | UndefinedTypeParam (Located Ident)
                -- ^ Attempt to explicitly instantiate a non-existent param.

              | MultipleTypeParamDefs Ident [Range]
                -- ^ Multiple definitions for the same type parameter

              | TypeMismatch Type Type
                -- ^ Expected type, inferred type

              | RecursiveType Type Type
                -- ^ Unification results in a recursive type

              | UnsolvedGoals Bool [Goal]
                -- ^ A constraint that we could not solve
                -- The boolean indicates if we know that this constraint
                -- is impossible.

              | UnsolvedDelayedCt DelayedCt
                -- ^ A constraint (with context) that we could not solve

              | UnexpectedTypeWildCard
                -- ^ Type wild cards are not allowed in this context
                -- (e.g., definitions of type synonyms).

              | TypeVariableEscaped Type [TVar]
                -- ^ Unification variable depends on quantified variables
                -- that are not in scope.

              | NotForAll TVar Type
                -- ^ Quantified type variables (of kind *) need to
                -- match the given type, so it does not work for all types.

              | UnusableFunction Name [Prop]
                -- ^ The given constraints causes the signature of the
                -- function to be not-satisfiable.

              | TooManyPositionalTypeParams
                -- ^ Too many positional type arguments, in an explicit
                -- type instantiation

              | CannotMixPositionalAndNamedTypeParams

              | AmbiguousType [Name] [TVar]


                deriving (Show, Generic, NFData)

instance TVars Warning where
  apSubst su warn =
    case warn of
      DefaultingKind {}     -> warn
      DefaultingWildType {} -> warn
      DefaultingTo d ty     -> DefaultingTo d (apSubst su ty)

instance FVS Warning where
  fvs warn =
    case warn of
      DefaultingKind {}     -> Set.empty
      DefaultingWildType {} -> Set.empty
      DefaultingTo _ ty     -> fvs ty

instance TVars Error where
  apSubst su err =
    case err of
      ErrorMsg _                -> err
      KindMismatch {}           -> err
      TooManyTypeParams {}      -> err
      TooManyTySynParams {}     -> err
      TooFewTySynParams {}      -> err
      RepeatedTyParams {}       -> err
      RepeatedDefinitions {}    -> err
      RecursiveTypeDecls {}     -> err
      UndefinedTypeSynonym {}   -> err
      UndefinedVariable {}      -> err
      UndefinedTypeParam {}     -> err
      MultipleTypeParamDefs {}  -> err
      TypeMismatch t1 t2        -> TypeMismatch (apSubst su t1) (apSubst su t2)
      RecursiveType t1 t2       -> RecursiveType (apSubst su t1) (apSubst su t2)
      UnsolvedGoals x gs        -> UnsolvedGoals x (apSubst su gs)
      UnsolvedDelayedCt g       -> UnsolvedDelayedCt (apSubst su g)
      UnexpectedTypeWildCard    -> err
      TypeVariableEscaped t xs  -> TypeVariableEscaped (apSubst su t) xs
      NotForAll x t             -> NotForAll x (apSubst su t)
      UnusableFunction f ps      -> UnusableFunction f (apSubst su ps)
      TooManyPositionalTypeParams -> err
      CannotMixPositionalAndNamedTypeParams -> err
      AmbiguousType _ _vs       -> err
          -- XXX: shoudln't be applying to these vars,
          -- they are ambiguous, after all


instance FVS Error where
  fvs err =
    case err of
      ErrorMsg {}               -> Set.empty
      KindMismatch {}           -> Set.empty
      TooManyTypeParams {}      -> Set.empty
      TooManyTySynParams {}     -> Set.empty
      TooFewTySynParams {}      -> Set.empty
      RepeatedTyParams {}       -> Set.empty
      RepeatedDefinitions {}    -> Set.empty
      RecursiveTypeDecls {}     -> Set.empty
      UndefinedTypeSynonym {}   -> Set.empty
      UndefinedVariable {}      -> Set.empty
      UndefinedTypeParam {}     -> Set.empty
      MultipleTypeParamDefs {}  -> Set.empty
      TypeMismatch t1 t2        -> fvs (t1,t2)
      RecursiveType t1 t2       -> fvs (t1,t2)
      UnsolvedGoals _ gs        -> fvs gs
      UnsolvedDelayedCt g       -> fvs g
      UnexpectedTypeWildCard    -> Set.empty
      TypeVariableEscaped t _   -> fvs t
      NotForAll _ t             -> fvs t
      UnusableFunction _ p      -> fvs p
      TooManyPositionalTypeParams -> Set.empty
      CannotMixPositionalAndNamedTypeParams -> Set.empty
      AmbiguousType _ _vs       ->  Set.empty



instance PP Warning where
  ppPrec = ppWithNamesPrec IntMap.empty

instance PP Error where
  ppPrec = ppWithNamesPrec IntMap.empty


instance PP (WithNames Warning) where
  ppPrec _ (WithNames warn names) =
    addTVarsDescs names warn $
    case warn of
      DefaultingKind x k ->
        text "Assuming " <+> pp x <+> text "to have" <+> P.cppKind k

      DefaultingWildType k ->
        text "Assuming _ to have" <+> P.cppKind k

      DefaultingTo d ty ->
        text "Defaulting" <+> d $$ text "to" <+> ppWithNames names ty

instance PP (WithNames Error) where
  ppPrec _ (WithNames err names) =
    addTVarsDescs names err $
    case err of
      ErrorMsg msg -> msg

      RecursiveType t1 t2 ->
        nested (text "Matching would result in an infinite type.")
          (text "The type: " <+> ppWithNames names t1 $$
           text "occurs in:" <+> ppWithNames names t2)

      UnexpectedTypeWildCard ->
        nested (text "Wild card types are not allowed in this context")
          (text "(e.g., they cannot be used in type synonyms).")

      KindMismatch k1 k2 ->
        nested (text "Incorrect type form.")
          (text "Expected:" <+> cppKind k1 $$
           text "Inferred:" <+> cppKind k2)

      TooManyTypeParams extra k ->
        nested (text "Malformed type.")
          (text "Kind" <+> quotes (pp k) <+> text "is not a function," $$
           text "but it was applied to" <+> pl extra "parameter" <> text ".")

      TooManyTySynParams t extra ->
        nested (text "Malformed type.")
          (text "Type synonym" <+> nm t <+> text "was applied to" <+>
            pl extra "extra parameter" <> text ".")

      TooFewTySynParams t few ->
        nested (text "Malformed type.")
          (text "Type" <+> nm t <+> text "is missing" <+>
            int few <+> text "parameters.")

      RepeatedTyParams ps ->
        nested (text "Different type parameters use the same name:")
          (vmulti [ nm (P.tpName p) <+>
                    text "defined at" <+> mb (P.tpRange p) | p <- ps ] )
          where mb Nothing  = text "unknown location"
                mb (Just x) = pp x

      RepeatedDefinitions x ps ->
        nested (text "Multiple definitions for the same name:")
          (vmulti [ nm x <+> text "defined at" <+> pp p | p <- ps ])

      RecursiveTypeDecls ts ->
        nested (text "Recursive type declarations:")
               (fsep $ punctuate comma $ map nm ts)

      UndefinedTypeSynonym x ->
        text "Type synonym" <+> nm x <+> text "is not defined."

      UndefinedVariable x ->
        text "Variable" <+> nm x <+> text "was not defined."

      UndefinedTypeParam x ->
        text "Type variable" <+> nm x <+> text "was not defined."

      MultipleTypeParamDefs x ps ->
        nested (text "Multiple definitions for the same type parameter"
                                                        <+> nm x <> text ":")
               (vmulti [ text "defined at" <+> pp p | p <- ps ])


      TypeMismatch t1 t2 ->
        nested (text "Type mismatch:")
          (text "Expected type:" <+> ppWithNames names t1 $$
           text "Inferred type:" <+> ppWithNames names t2 $$
           mismatchHint t1 t2)

      UnsolvedGoals imp gs ->
        nested (word <+> text "constraints:")
               $ vcat $ map (ppWithNames names) gs
        where word = if imp then text "Unsolvable" else text "Unsolved"

      UnsolvedDelayedCt g ->
        nested (text "Failed to validate user-specified signature.")
               (ppWithNames names g)

      TypeVariableEscaped t xs ->
        nested (text "The type" <+> ppWithNames names t <+>
                text "is not sufficiently polymorphic.")
               (text "It cannot depend on quantified variables:" <+>
                sep (punctuate comma (map (ppWithNames names) xs)))

      NotForAll x t ->
        nested (text "Inferred type is not sufficiently polymorphic.")
          (text "Quantified variable:" <+> ppWithNames names x $$
           text "cannot match type:"   <+> ppWithNames names t)

      UnusableFunction f ps ->
        nested (text "The constraints in the type signature of"
                <+> quotes (pp f) <+> text "are unsolvable.")
               (text "Detected while analyzing constraints:"
                $$ vcat (map (ppWithNames names) ps))

      TooManyPositionalTypeParams ->
        text "Too many positional type-parameters in explicit type application"

      CannotMixPositionalAndNamedTypeParams ->
        text "Named and positional type applications may not be mixed."

      AmbiguousType xs vs ->
        (text "The inferred type for" <+> commaSep (map pp xs)
          <+> text "is ambiguous.")
          $$ text "Arising from:"
          $$ nest 2 (vcat [ text "*" <+> var v | v <- vs ])
        where var (TVFree _ _ _ d) = d
              var x = pp x

    where
    nested x y = x $$ nest 2 y

    pl 1 x     = text "1" <+> text x
    pl n x     = text (show n) <+> text x <> text "s"

    nm x       = text "`" <> pp x <> text "`"

    vmulti          = vcat . multi

    multi []        = []
    multi [x]       = [x <> text "."]
    multi [x,y]     = [x <> text ", and", y <> text "." ]
    multi (x : xs)  = x <> text "," : multi xs

    mismatchHint (TRec fs1) (TRec fs2) =
      hint "Missing" missing $$ hint "Unexpected" extra
      where
        missing = map fst fs1 \\ map fst fs2
        extra   = map fst fs2 \\ map fst fs1
        hint _ []  = mempty
        hint s [x] = text s <+> text "field" <+> pp x
        hint s xs  = text s <+> text "fields" <+> commaSep (map pp xs)
    mismatchHint _ _ = mempty


