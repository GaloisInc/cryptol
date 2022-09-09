{-# Language FlexibleInstances, DeriveGeneric, DeriveAnyClass #-}
{-# Language OverloadedStrings #-}
{-# LANGUAGE Safe #-}
-- See Note [-Wincomplete-uni-patterns and irrefutable patterns] in Cryptol.TypeCheck.TypePat
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Cryptol.TypeCheck.Error where

import qualified Data.IntMap as IntMap
import qualified Data.Set as Set
import Control.DeepSeq(NFData)
import GHC.Generics(Generic)
import Data.List((\\),sortBy,groupBy,partition)
import Data.Function(on)

import qualified Cryptol.Parser.AST as P
import Cryptol.Parser.Position(Located(..), Range(..), rangeWithin)
import Cryptol.TypeCheck.PP
import Cryptol.TypeCheck.Type
import Cryptol.TypeCheck.InferTypes
import Cryptol.TypeCheck.Subst
import Cryptol.TypeCheck.Unify(Path,isRootPath)
import Cryptol.TypeCheck.FFI.Error
import Cryptol.ModuleSystem.Name(Name)
import Cryptol.Utils.Ident(Ident)
import Cryptol.Utils.RecordMap

cleanupErrors :: [(Range,Error)] -> [(Range,Error)]
cleanupErrors = dropErrorsFromSameLoc
              . sortBy (compare `on` (cmpR . fst))    -- order errors
              . dropSubsumed []
  where

  -- pick shortest error from each location.
  dropErrorsFromSameLoc = concatMap chooseBestError
                        . groupBy ((==)    `on` fst)

  addErrorRating (r,e) = (errorImportance e, (r,e))
  chooseBestError    = map snd
                     . head
                     . groupBy ((==) `on` fst)
                     . sortBy (flip compare `on` fst)
                     . map addErrorRating


  cmpR r  = ( source r    -- First by file
            , from r      -- Then starting position
            , to r        -- Finally end position
            )

  dropSubsumed survived xs =
    case xs of
      err : rest ->
         let keep e = not (subsumes err e)
         in dropSubsumed (err : filter keep survived) (filter keep rest)
      [] -> survived

-- | Should the first error suppress the next one.
subsumes :: (Range,Error) -> (Range,Error) -> Bool
subsumes (_,NotForAll _ _ x _) (_,NotForAll _ _ y _) = x == y
subsumes (r1,UnexpectedTypeWildCard) (r2,UnsupportedFFIType{}) =
  r1 `rangeWithin` r2
subsumes (r1,KindMismatch {}) (r2,err) =
  case err of
    KindMismatch {} -> r1 == r2
    _               -> True
subsumes _ _ = False

data Warning  = DefaultingKind (P.TParam Name) P.Kind
              | DefaultingWildType P.Kind
              | DefaultingTo !TVarInfo Type
                deriving (Show, Generic, NFData)

-- | Various errors that might happen during type checking/inference
data Error    = KindMismatch (Maybe TypeSource) Kind Kind
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

              | TypeMismatch TypeSource Path Type Type
                -- ^ Expected type, inferred type

              | RecursiveType TypeSource Path Type Type
                -- ^ Unification results in a recursive type

              | UnsolvedGoals [Goal]
                -- ^ A constraint that we could not solve, usually because
                -- there are some left-over variables that we could not infer.

              | UnsolvableGoals [Goal]
                -- ^ A constraint that we could not solve and we know
                -- it is impossible to do it.

              | UnsolvedDelayedCt DelayedCt
                -- ^ A constraint (with context) that we could not solve

              | UnexpectedTypeWildCard
                -- ^ Type wild cards are not allowed in this context
                -- (e.g., definitions of type synonyms).

              | TypeVariableEscaped TypeSource Path Type [TParam]
                -- ^ Unification variable depends on quantified variables
                -- that are not in scope.

              | NotForAll TypeSource Path TVar Type
                -- ^ Quantified type variables (of kind *) need to
                -- match the given type, so it does not work for all types.

              | TooManyPositionalTypeParams
                -- ^ Too many positional type arguments, in an explicit
                -- type instantiation

              | BadParameterKind TParam Kind
                -- ^ Kind other than `*` or `#` given to parameter of
                --   type synonym, newtype, function signature, etc.

              | CannotMixPositionalAndNamedTypeParams

              | UndefinedTypeParameter (Located Ident)

              | RepeatedTypeParameter Ident [Range]

              | AmbiguousSize TVarInfo (Maybe Type)
                -- ^ Could not determine the value of a numeric type variable,
                --   but we know it must be at least as large as the given type
                --   (or unconstrained, if Nothing).

              | BareTypeApp
                -- ^ Bare expression of the form `{_}

              | UndefinedExistVar Name
              | TypeShadowing String Name String
              | MissingModTParam (Located Ident)
              | MissingModVParam (Located Ident)

              | UnsupportedFFIKind TypeSource TParam Kind
                -- ^ Kind is not supported for FFI
              | UnsupportedFFIType TypeSource FFITypeError
                -- ^ Type is not supported for FFI

              | TemporaryError Doc
                -- ^ This is for errors that don't fit other cateogories.
                -- We should not use it much, and is generally to be used
                -- for transient errors, which are due to incomplete
                -- implementation.
                deriving (Show, Generic, NFData)

-- | When we have multiple errors on the same location, we show only the
-- ones with the has highest rating according to this function.
errorImportance :: Error -> Int
errorImportance err =
  case err of
    BareTypeApp                                      -> 11 -- basically a parse error
    TemporaryError {}                                -> 11
    -- show these as usually means the user used something that doesn't work


    KindMismatch {}                                  -> 10
    TyVarWithParams {}                               -> 9
    TypeMismatch {}                                  -> 8
    RecursiveType {}                                 -> 7
    NotForAll {}                                     -> 6
    TypeVariableEscaped {}                           -> 5

    UndefinedExistVar {}                             -> 10
    TypeShadowing {}                                 -> 2
    MissingModTParam {}                              -> 10
    MissingModVParam {}                              -> 10

    BadParameterKind{}                               -> 9
    CannotMixPositionalAndNamedTypeParams {}         -> 8
    TooManyTypeParams {}                             -> 8
    TooFewTyParams {}                                -> 8
    TooManyPositionalTypeParams {}                   -> 8
    UndefinedTypeParameter {}                        -> 8
    RepeatedTypeParameter {}                         -> 8

    TooManyTySynParams {}                            -> 8
    UnexpectedTypeWildCard {}                        -> 8

    RecursiveTypeDecls {}                            -> 9

    UnsolvableGoals g
      | any tHasErrors (map goal g)                  -> 0
      | otherwise                                    -> 4

    UnsolvedGoals g
      | any tHasErrors (map goal g)                  -> 0
      | otherwise                                    -> 4

    UnsolvedDelayedCt dt
      | any tHasErrors (map goal (dctGoals dt))      -> 0
      | otherwise                                    -> 3

    AmbiguousSize {}                                 -> 2

    UnsupportedFFIKind {}                            -> 10
    UnsupportedFFIType {}                            -> 7
    -- less than UnexpectedTypeWildCard


instance TVars Warning where
  apSubst su warn =
    case warn of
      DefaultingKind {}     -> warn
      DefaultingWildType {} -> warn
      DefaultingTo d ty     -> DefaultingTo d $! (apSubst su ty)

instance FVS Warning where
  fvs warn =
    case warn of
      DefaultingKind {}     -> Set.empty
      DefaultingWildType {} -> Set.empty
      DefaultingTo _ ty     -> fvs ty

instance TVars Error where
  apSubst su err =
    case err of
      KindMismatch {}           -> err
      TooManyTypeParams {}      -> err
      TyVarWithParams           -> err
      TooManyTySynParams {}     -> err
      TooFewTyParams {}         -> err
      RecursiveTypeDecls {}     -> err
      TypeMismatch src pa t1 t2 -> TypeMismatch src pa !$ (apSubst su t1) !$ (apSubst su t2)
      RecursiveType src pa t1 t2   -> RecursiveType src pa !$ (apSubst su t1) !$ (apSubst su t2)
      UnsolvedGoals gs          -> UnsolvedGoals !$ apSubst su gs
      UnsolvableGoals gs        -> UnsolvableGoals !$ apSubst su gs
      UnsolvedDelayedCt g       -> UnsolvedDelayedCt !$ (apSubst su g)
      UnexpectedTypeWildCard    -> err
      TypeVariableEscaped src pa t xs ->
                                 TypeVariableEscaped src pa !$ (apSubst su t) .$ xs
      NotForAll src pa x t        -> NotForAll src pa x !$ (apSubst su t)
      TooManyPositionalTypeParams -> err
      CannotMixPositionalAndNamedTypeParams -> err

      BadParameterKind{} -> err
      UndefinedTypeParameter {} -> err
      RepeatedTypeParameter {} -> err
      AmbiguousSize x t -> AmbiguousSize x !$ (apSubst su t)

      BareTypeApp -> err

      UndefinedExistVar {} -> err
      TypeShadowing {}     -> err
      MissingModTParam {}  -> err
      MissingModVParam {}  -> err

      UnsupportedFFIKind {}    -> err
      UnsupportedFFIType src e -> UnsupportedFFIType src !$ apSubst su e

      TemporaryError {} -> err


instance FVS Error where
  fvs err =
    case err of
      KindMismatch {}           -> Set.empty
      TooManyTypeParams {}      -> Set.empty
      TyVarWithParams           -> Set.empty
      TooManyTySynParams {}     -> Set.empty
      TooFewTyParams {}         -> Set.empty
      RecursiveTypeDecls {}     -> Set.empty
      TypeMismatch _ _ t1 t2    -> fvs (t1,t2)
      RecursiveType _ _ t1 t2   -> fvs (t1,t2)
      UnsolvedGoals gs          -> fvs gs
      UnsolvableGoals gs        -> fvs gs
      UnsolvedDelayedCt g       -> fvs g
      UnexpectedTypeWildCard    -> Set.empty
      TypeVariableEscaped _ _ t xs-> fvs t `Set.union`
                                            Set.fromList (map TVBound xs)
      NotForAll _ _ x t             -> Set.insert x (fvs t)
      TooManyPositionalTypeParams -> Set.empty
      CannotMixPositionalAndNamedTypeParams -> Set.empty
      UndefinedTypeParameter {}             -> Set.empty
      RepeatedTypeParameter {}              -> Set.empty
      AmbiguousSize _ t -> fvs t
      BadParameterKind tp _ -> Set.singleton (TVBound tp)

      BareTypeApp -> Set.empty

      UndefinedExistVar {} -> Set.empty
      TypeShadowing {}     -> Set.empty
      MissingModTParam {}  -> Set.empty
      MissingModVParam {}  -> Set.empty

      UnsupportedFFIKind {}  -> Set.empty
      UnsupportedFFIType _ t -> fvs t

      TemporaryError {} -> Set.empty

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

      RecursiveType src pa t1 t2 ->
        addTVarsDescsAfter names err $
        nested "Matching would result in an infinite type." $
          vcat ( [ "The type: " <+> ppWithNames names t1
                 , "occurs in:" <+> ppWithNames names t2
                 ] ++ ppCtxt pa ++
                 [ "When checking" <+> pp src ] )

      UnexpectedTypeWildCard ->
        addTVarsDescsAfter names err $
        nested "Wild card types are not allowed in this context"
          "(e.g., they cannot be used in type synonyms or FFI declarations)."

      KindMismatch mbsrc k1 k2 ->
        addTVarsDescsAfter names err $
        nested "Incorrect type form." $
         vcat $
           [ "Expected:" <+> cppKind k1
           , "Inferred:" <+> cppKind k2
           ] ++ kindMismatchHint k1 k2
             ++ maybe [] (\src -> ["When checking" <+> pp src]) mbsrc

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
               (commaSep $ map nm ts)

      TypeMismatch src pa t1 t2 ->
        addTVarsDescsAfter names err $
        nested "Type mismatch:" $
        vcat $
          [ "Expected type:" <+> ppWithNames names t1
          , "Inferred type:" <+> ppWithNames names t2
          ] ++ mismatchHint t1 t2
            ++ ppCtxt pa
            ++ ["When checking" <+> pp src]

      UnsolvableGoals gs -> explainUnsolvable names gs

      UnsolvedGoals gs
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

      TypeVariableEscaped src pa t xs ->
        addTVarsDescsAfter names err $
        nested ("The type" <+> ppWithNames names t <+>
                                        "is not sufficiently polymorphic.") $
          vcat ( [ "It cannot depend on quantified variables:" <+>
                       (commaSep (map (ppWithNames names) xs))
                 ] ++ ppCtxt pa
                   ++ [ "When checking" <+> pp src ]
               )

      NotForAll src pa x t ->
        addTVarsDescsAfter names err $
        nested "Inferred type is not sufficiently polymorphic." $
          vcat ( [ "Quantified variable:" <+> ppWithNames names x
                 , "cannot match type:"   <+> ppWithNames names t
                 ] ++ ppCtxt pa
                   ++ [ "When checking" <+> pp src ]
               )

      BadParameterKind tp k ->
        addTVarsDescsAfter names err $
        vcat [ "Illegal kind assigned to type variable:" <+> ppWithNames names tp
             , "Unexpected:" <+> pp k
             ]

      TooManyPositionalTypeParams ->
        addTVarsDescsAfter names err $
        "Too many positional type-parameters in explicit type application."

      CannotMixPositionalAndNamedTypeParams ->
        addTVarsDescsAfter names err $
        "Named and positional type applications may not be mixed."

      UndefinedTypeParameter x ->
        addTVarsDescsAfter names err $
        "Undefined type parameter `" <.> pp (thing x) <.> "`."
          $$ "See" <+> pp (srcRange x)

      RepeatedTypeParameter x rs ->
        addTVarsDescsAfter names err $ nest 2 $
          "Multiple definitions for type parameter `" <.> pp x <.> "`:"
          $$ bullets (map pp rs)

      AmbiguousSize x t ->
        let sizeMsg =
               case t of
                 Just t' -> ["Must be at least:" <+> ppWithNames names t']
                 Nothing -> []
         in addTVarsDescsAfter names err
              (vcat (["Ambiguous numeric type:" <+> pp (tvarDesc x)] ++ sizeMsg))

      BareTypeApp ->
        "Unexpected bare type application." $$
        "Perhaps you meant `( ... ) instead."

      UndefinedExistVar x -> "Undefined type" <+> quotes (pp x)
      TypeShadowing this new that ->
        "Type" <+> text this <+> quotes (pp new) <+>
        "shadowing an existing" <+> text that <+> "with the same name."
      MissingModTParam x ->
        "Missing definition for type parameter" <+> quotes (pp (thing x))
      MissingModVParam x ->
        "Missing definition for value parameter" <+> quotes (pp (thing x))

      UnsupportedFFIKind src param k ->
        nested "Kind of type variable unsupported for FFI: " $
        vcat
          [ pp param <+> colon <+> pp k
          , "Only type variables of kind" <+> pp KNum <+> "are supported"
          , "When checking" <+> pp src ]

      UnsupportedFFIType src t -> vcat
        [ ppWithNames names t
        , "When checking" <+> pp src ]

      TemporaryError doc -> doc
    where
    bullets xs = vcat [ "•" <+> d | d <- xs ]

    nested x y = nest 2 (x $$ y)

    pl 1 x     = text "1" <+> text x
    pl n x     = text (show n) <+> text x <.> text "s"

    nm x       = text "`" <.> pp x <.> text "`"

    kindMismatchHint k1 k2 =
      case (k1,k2) of
        (KType,KProp) -> [text "Possibly due to a missing `=>`"]
        _ -> []

    mismatchHint (TRec fs1) (TRec fs2) =
      hint "Missing" missing ++ hint "Unexpected" extra
      where
        missing = displayOrder fs1 \\ displayOrder fs2
        extra   = displayOrder fs2 \\ displayOrder fs1
        hint _ []  = []
        hint s [x] = [text s <+> text "field" <+> pp x]
        hint s xs  = [text s <+> text "fields" <+> commaSep (map pp xs)]
    mismatchHint _ _ = []

    noUni = Set.null (Set.filter isFreeTV (fvs err))

    ppCtxt pa = if isRootPath pa then [] else [ "Context:" <+> pp pa ]




explainUnsolvable :: NameMap -> [Goal] -> Doc
explainUnsolvable names gs =
  addTVarsDescsAfter names gs (bullets (map explain gs))

  where
  bullets xs = vcat [ "•" <+> d | d <- xs ]



  explain g =
    let useCtr = hang "Unsolvable constraint:" 2 (ppWithNames names g)

    in
    case tNoUser (goal g) of
      TCon (PC pc) ts ->
        let tys = [ backticks (ppWithNames names t) | t <- ts ]
            doc1 = case tys of
                     (doc1' : _) -> doc1'
                     [] -> error "explainUnsolvable: Expected TCon to have at least one argument"
            custom msg = hang msg
                            2 (text "arising from" $$
                               pp (goalSource g)   $$
                               text "at" <+> pp (goalRange g))
        in
        case pc of
          PEqual      -> useCtr
          PNeq        -> useCtr
          PGeq        -> useCtr
          PFin        -> useCtr
          PPrime      -> useCtr

          PHas sel ->
            custom ("Type" <+> doc1 </> "does not have field" <+> f
                    <+> "of type" <+> (tys !! 1))
            where f = case sel of
                        P.TupleSel n _ -> int n
                        P.RecordSel fl _ -> backticks (pp fl)
                        P.ListSel n _ -> int n

          PZero  ->
            custom ("Type" <+> doc1 </> "does not have `zero`")

          PLogic ->
            custom ("Type" <+> doc1 </> "does not support logical operations.")

          PRing ->
            custom ("Type" <+> doc1 </> "does not support ring operations.")

          PIntegral ->
            custom (doc1 </> "is not an integral type.")

          PField ->
            custom ("Type" <+> doc1 </> "does not support field operations.")

          PRound ->
            custom ("Type" <+> doc1 </> "does not support rounding operations.")

          PEq ->
            custom ("Type" <+> doc1 </> "does not support equality.")

          PCmp        ->
            custom ("Type" <+> doc1 </> "does not support comparisons.")

          PSignedCmp  ->
            custom ("Type" <+> doc1 </> "does not support signed comparisons.")

          PLiteral ->
            let doc2 = tys !! 1
            in custom (doc1 </> "is not a valid literal of type" <+> doc2)

          PLiteralLessThan ->
            let doc2 = tys !! 1
            in custom ("Type" <+> doc2 </> "does not contain all literals below" <+> (doc1 <> "."))

          PFLiteral ->
            case ts of
              ~[m,n,_r,_a] ->
                 let frac = backticks (ppWithNamesPrec names 4 m <> "/" <>
                                       ppWithNamesPrec names 4 n)
                     ty   = tys !! 3
                 in custom (frac </> "is not a valid literal of type" </> ty)

          PValidFloat ->
            case ts of
              ~[e,p] ->
                custom (hang "Unsupported floating point parameters:"
                           2 ("exponent =" <+> ppWithNames names e $$
                              "precision =" <+> ppWithNames names p))


          PAnd        -> useCtr
          PTrue       -> useCtr

      _ -> useCtr




-- | This picks the names to use when showing errors and warnings.
computeFreeVarNames :: [(Range,Warning)] -> [(Range,Error)] -> NameMap
computeFreeVarNames warns errs =
  mkMap numRoots numVaras `IntMap.union` mkMap otherRoots otherVars

  {- XXX: Currently we pick the names based on the unique of the variable:
     smaller uniques get an earlier name (e.g., 100 might get `a` and 200 `b`)
     This may still lead to changes in the names if the uniques got reordered
     for some reason.  A more stable approach might be to order the variables
     on their location in the error/warning, but that's quite a bit more code
     so for now we just go with the simple approximation. -}

  where
  mkName x v = (tvUnique x, v)
  mkMap roots vs = IntMap.fromList (zipWith mkName vs (variants roots))

  (numVaras,otherVars) = partition ((== KNum) . kindOf)
                       $ Set.toList
                       $ Set.filter isFreeTV
                       $ fvs (map snd warns, map snd errs)

  otherRoots = [ "a", "b", "c", "d" ]
  numRoots   = [ "m", "n", "u", "v" ]

  useUnicode = True

  suff n
    | n < 10 && useUnicode = [toEnum (0x2080 + n)]
    | otherwise = show n

  variant n x = if n == 0 then x else x ++ suff n

  variants roots = [ variant n r | n <- [ 0 .. ], r <- roots ]
