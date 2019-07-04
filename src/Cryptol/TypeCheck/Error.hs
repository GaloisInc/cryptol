{-# Language FlexibleInstances, DeriveGeneric, DeriveAnyClass #-}
{-# Language OverloadedStrings #-}
module Cryptol.TypeCheck.Error where


import qualified Data.IntMap as IntMap
import qualified Data.Set as Set
import Control.DeepSeq(NFData)
import GHC.Generics(Generic)
import Data.List((\\),sortBy,groupBy,minimumBy)
import Data.Function(on)

import qualified Cryptol.Parser.AST as P
import Cryptol.Parser.Position(Located(..), Range(..))
import Cryptol.TypeCheck.PP
import Cryptol.TypeCheck.Type
import Cryptol.TypeCheck.InferTypes
import Cryptol.TypeCheck.Subst
import Cryptol.ModuleSystem.Name(Name)
import Cryptol.Utils.Ident(Ident)

cleanupErrors :: [(Range,Error)] -> [(Range,Error)]
cleanupErrors = dropErrorsFromSameLoc
              . sortBy (compare `on` (cmpR . fst))    -- order errors
              . dropSumbsumed
  where

  -- pick shortest error from each location.
  dropErrorsFromSameLoc = map chooseBestError
                        . groupBy ((==)    `on` fst)

  addErrorSize (r,e) = (length (show (pp e)), (r,e))
  chooseBestError    = snd . minimumBy (compare `on` fst) . map addErrorSize


  cmpR r  = ( source r    -- Frist by file
            , from r      -- Then starting position
            , to r        -- Finally end position
            )

  dropSumbsumed xs =
    case xs of
      (r,e) : rest -> (r,e) :
                        dropSumbsumed (filter (not .subsumes e . snd) rest)
      [] -> []

-- | Should the first error suppress the next one.
subsumes :: Error -> Error -> Bool
subsumes (NotForAll x _) (NotForAll y _) = x == y
subsumes _ _ = False

data Warning  = DefaultingKind (P.TParam Name) P.Kind
              | DefaultingWildType P.Kind
              | DefaultingTo TVarInfo Type
                deriving (Show, Generic, NFData)

-- | Various errors that might happen during type checking/inference
data Error    = ErrorMsg Doc
                -- ^ Just say this

              | KindMismatch Kind Kind
                -- ^ Expected kind, inferred kind

              | TooManyTypeParams Int Kind
                -- ^ Number of extra parameters, kind of result
                -- (which should not be of the form @_ -> _@)

              | TyVarWithParams
                -- ^ A type variable was applied to some arguments.

              | TooManyTySynParams Name Int
                -- ^ Type-synonym, number of extra params

              | TooFewTyParams Name Int
                -- ^ Who is missing params, number of missing params

              | RecursiveTypeDecls [Name]
                -- ^ The type synonym declarations are recursive

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

              | TypeVariableEscaped Type [TParam]
                -- ^ Unification variable depends on quantified variables
                -- that are not in scope.

              | NotForAll TVar Type
                -- ^ Quantified type variables (of kind *) need to
                -- match the given type, so it does not work for all types.

              | TooManyPositionalTypeParams
                -- ^ Too many positional type arguments, in an explicit
                -- type instantiation

              | CannotMixPositionalAndNamedTypeParams

              | UndefinedTypeParameter (Located Ident)

              | RepeatedTypeParameter Ident [Range]

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
      TyVarWithParams           -> err
      TooManyTySynParams {}     -> err
      TooFewTyParams {}         -> err
      RecursiveTypeDecls {}     -> err
      TypeMismatch t1 t2        -> TypeMismatch (apSubst su t1) (apSubst su t2)
      RecursiveType t1 t2       -> RecursiveType (apSubst su t1) (apSubst su t2)
      UnsolvedGoals x gs        -> UnsolvedGoals x (apSubst su gs)
      UnsolvedDelayedCt g       -> UnsolvedDelayedCt (apSubst su g)
      UnexpectedTypeWildCard    -> err
      TypeVariableEscaped t xs  -> TypeVariableEscaped (apSubst su t) xs
      NotForAll x t             -> NotForAll x (apSubst su t)
      TooManyPositionalTypeParams -> err
      CannotMixPositionalAndNamedTypeParams -> err

      UndefinedTypeParameter {} -> err
      RepeatedTypeParameter {} -> err


instance FVS Error where
  fvs err =
    case err of
      ErrorMsg {}               -> Set.empty
      KindMismatch {}           -> Set.empty
      TooManyTypeParams {}      -> Set.empty
      TyVarWithParams           -> Set.empty
      TooManyTySynParams {}     -> Set.empty
      TooFewTyParams {}         -> Set.empty
      RecursiveTypeDecls {}     -> Set.empty
      TypeMismatch t1 t2        -> fvs (t1,t2)
      RecursiveType t1 t2       -> fvs (t1,t2)
      UnsolvedGoals _ gs        -> fvs gs
      UnsolvedDelayedCt g       -> fvs g
      UnexpectedTypeWildCard    -> Set.empty
      TypeVariableEscaped t xs  -> fvs t `Set.union`
                                            Set.fromList (map TVBound xs)
      NotForAll x t             -> Set.insert x (fvs t)
      TooManyPositionalTypeParams -> Set.empty
      CannotMixPositionalAndNamedTypeParams -> Set.empty
      UndefinedTypeParameter {}             -> Set.empty
      RepeatedTypeParameter {}              -> Set.empty



instance PP Warning where
  ppPrec = ppWithNamesPrec IntMap.empty

instance PP Error where
  ppPrec = ppWithNamesPrec IntMap.empty


instance PP (WithNames Warning) where
  ppPrec _ (WithNames warn names) =
    addTVarsDescsAfter names warn $
    case warn of
      DefaultingKind x k ->
        text "Assuming " <+> pp x <+> text "to have" <+> P.cppKind k

      DefaultingWildType k ->
        text "Assuming _ to have" <+> P.cppKind k

      DefaultingTo d ty ->
        text "Defaulting" <+> pp (tvarDesc d) <+> text "to"
                                              <+> ppWithNames names ty

instance PP (WithNames Error) where
  ppPrec _ (WithNames err names) =
    case err of
      ErrorMsg msg ->
        addTVarsDescsAfter names err
        msg

      RecursiveType t1 t2 ->
        addTVarsDescsAfter names err $
        nested "Matching would result in an infinite type."
          ("The type: " <+> ppWithNames names t1 $$
           "occurs in:" <+> ppWithNames names t2)

      UnexpectedTypeWildCard ->
        addTVarsDescsAfter names err $
        nested "Wild card types are not allowed in this context"
          "(e.g., they cannot be used in type synonyms)."

      KindMismatch k1 k2 ->
        addTVarsDescsAfter names err $
        nested "Incorrect type form."
          ("Expected:" <+> cppKind k1 $$
           "Inferred:" <+> cppKind k2)

      TooManyTypeParams extra k ->
        addTVarsDescsAfter names err $
        nested "Malformed type."
          ("Kind" <+> quotes (pp k) <+> "is not a function," $$
           "but it was applied to" <+> pl extra "parameter" <.> ".")

      TyVarWithParams ->
        addTVarsDescsAfter names err $
        nested "Malformed type."
               "Type variables cannot be applied to parameters."

      TooManyTySynParams t extra ->
        addTVarsDescsAfter names err $
        nested "Malformed type."
          ("Type synonym" <+> nm t <+> "was applied to" <+>
            pl extra "extra parameters" <.> text ".")

      TooFewTyParams t few ->
        addTVarsDescsAfter names err $
        nested "Malformed type."
          ("Type" <+> nm t <+> "is missing" <+> int few <+> text "parameters.")

      RecursiveTypeDecls ts ->
        addTVarsDescsAfter names err $
        nested "Recursive type declarations:"
               (fsep $ punctuate comma $ map nm ts)

      TypeMismatch t1 t2 ->
        addTVarsDescsAfter names err $
        nested "Type mismatch:"
          ("Expected type:" <+> ppWithNames names t1 $$
           "Inferred type:" <+> ppWithNames names t2 $$
           mismatchHint t1 t2)

      UnsolvedGoals imp gs
        | imp ->
          addTVarsDescsAfter names err $
          nested "Unsolvable constraints:" $
          bullets (map (ppWithNames names) gs)

        | noUni ->
          addTVarsDescsAfter names err $
          nested "Unsolved constraints:" $
          bullets (map (ppWithNames names) gs)

        | otherwise ->
          addTVarsDescsBefore names err $
          nested "subject to the following constraints:" $
          bullets (map (ppWithNames names) gs)

      UnsolvedDelayedCt g
        | noUni ->
          addTVarsDescsAfter names err $
          nested "Failed to validate user-specified signature." $
          ppWithNames names g
        | otherwise ->
          addTVarsDescsBefore names err $
          nested "while validating user-specified signature" $
          ppWithNames names g

      TypeVariableEscaped t xs ->
        addTVarsDescsAfter names err $
        nested ("The type" <+> ppWithNames names t <+>
                                        "is not sufficiently polymorphic.")
               ("It cannot depend on quantified variables:" <+>
                sep (punctuate comma (map (ppWithNames names) xs)))

      NotForAll x t ->
        addTVarsDescsAfter names err $
        nested "Inferred type is not sufficiently polymorphic."
          ("Quantified variable:" <+> ppWithNames names x $$
           "cannot match type:"   <+> ppWithNames names t)

      TooManyPositionalTypeParams ->
        addTVarsDescsAfter names err $
        "Too many positional type-parameters in explicit type application"

      CannotMixPositionalAndNamedTypeParams ->
        addTVarsDescsAfter names err $
        "Named and positional type applications may not be mixed."

      UndefinedTypeParameter x ->
        addTVarsDescsAfter names err $
        "Undefined type parameter `" <.> pp (thing x) <.> "`."
          $$ "See" <+> pp (srcRange x)

      RepeatedTypeParameter x rs ->
        addTVarsDescsAfter names err $
        "Multiple definitions for type parameter `" <.> pp x <.> "`:"
          $$ nest 2 (bullets (map pp rs))

    where
    bullets xs = vcat [ "•" <+> d | d <- xs ]

    nested x y = x $$ nest 2 y

    pl 1 x     = text "1" <+> text x
    pl n x     = text (show n) <+> text x <.> text "s"

    nm x       = text "`" <.> pp x <.> text "`"

    mismatchHint (TRec fs1) (TRec fs2) =
      hint "Missing" missing $$ hint "Unexpected" extra
      where
        missing = map fst fs1 \\ map fst fs2
        extra   = map fst fs2 \\ map fst fs1
        hint _ []  = mempty
        hint s [x] = text s <+> text "field" <+> pp x
        hint s xs  = text s <+> text "fields" <+> commaSep (map pp xs)
    mismatchHint _ _ = mempty

    noUni = Set.null (Set.filter isFreeTV (fvs err))
