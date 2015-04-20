-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- This module contains types used during type inference.

{-# LANGUAGE Safe #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}

module Cryptol.TypeCheck.InferTypes where

import           Cryptol.TypeCheck.AST
import           Cryptol.TypeCheck.Subst
import           Cryptol.TypeCheck.TypeMap
import           Cryptol.Parser.Position
import qualified Cryptol.Parser.AST as P
import           Cryptol.Parser.AST(LQName)
import           Cryptol.Prims.Syntax(ECon(..))
import           Cryptol.Utils.PP
import           Cryptol.TypeCheck.PP
import           Cryptol.Utils.Panic(panic)

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap



data SolverConfig = SolverConfig
  { solverPath    :: FilePath   -- ^ The SMT solver to invoke
  , solverArgs    :: [String]   -- ^ Additional arguments to pass to the solver
  , solverVerbose :: Int        -- ^ How verbose to be when type-checking
  } deriving Show


-- | The types of variables in the environment.
data VarType = ExtVar Schema      -- ^ Known type
             | CurSCC Expr Type   -- ^ Part of current SCC

newtype Goals = Goals (TypeMap Goal)
                deriving (Show)

emptyGoals :: Goals
emptyGoals  = Goals emptyTM

nullGoals :: Goals -> Bool
nullGoals (Goals tm) = nullTM tm

fromGoals :: Goals -> [Goal]
fromGoals (Goals tm) = membersTM tm

insertGoal :: Goal -> Goals -> Goals
insertGoal g (Goals tm) = Goals (insertTM (goal g) g tm)

-- | Something that we need to find evidence for.
data Goal = Goal
  { goalSource :: ConstraintSource  -- ^ With it is about
  , goalRange  :: Range             -- ^ Part of source code that caused goal
  , goal       :: Prop              -- ^ What needs to be proved
  } deriving Show

data HasGoal = HasGoal
  { hasName :: !Int
  , hasGoal :: Goal
  } deriving Show

-- | Delayed implication constraints, arising from user-specified type sigs.
data DelayedCt = DelayedCt
  { dctSource :: LQName   -- ^ Signature that gave rise to this constraint
  , dctForall :: [TParam]
  , dctAsmps  :: [Prop]
  , dctGoals  :: [Goal]
  } deriving Show

data Solved = Solved (Maybe Subst) [Goal] -- ^ Solved, assuming the sub-goals.
            | Unsolved                    -- ^ We could not solved the goal.
            | Unsolvable                  -- ^ The goal can never be solved
              deriving (Show)

data Warning  = DefaultingKind P.TParam P.Kind
              | DefaultingWildType P.Kind
              | DefaultingTo Doc Type
                deriving Show

-- | Various errors that might happen during type checking/inference
data Error    = ErrorMsg Doc
                -- ^ Just say this

              | KindMismatch Kind Kind
                -- ^ Expected kind, inferred kind

              | TooManyTypeParams Int Kind
                -- ^ Number of extra parameters, kind of resut
                -- (which should not be of the form @_ -> _@)

              | TooManyTySynParams QName Int
                -- ^ Type-synonym, number of extra params

              | TooFewTySynParams QName Int
                -- ^ Type-synonym, number of missing params

              | RepeatedTyParams [P.TParam]
                -- ^ Type parameters with the same name (in definition)

              | RepeatedDefinitions QName [Range]
                -- ^ Multiple definitions for the same name

              | RecursiveTypeDecls [LQName]
                -- ^ The type synonym declarations are recursive

              | UndefinedTypeSynonym QName
                -- ^ Use of a type synonym that was not defined

              | UndefinedVariable QName
                -- ^ Use of a variable that was not defined

              | UndefinedTypeParam QName
                -- ^ Attempt to explicitly instantiate a non-existent param.

              | MultipleTypeParamDefs QName [Range]
                -- ^ Multiple definitions for the same type parameter

              | TypeMismatch Type Type
                -- ^ Expected type, inferred type

              | RecursiveType Type Type
                -- ^ Unification results in a recursive type

              | UnsolvedGoal Goal
                -- ^ A constraint that we could not solve

              | UnsolvedDelcayedCt DelayedCt
                -- ^ A constraint (with context) that we could not solve

              | UnexpectedTypeWildCard
                -- ^ Type wild cards are not allowed in this context
                -- (e.g., definitions of type synonyms).

              | TypeVariableEscaped Type [TVar]
                -- ^ Unification variable depends on quantified variables
                -- that are not in scope.

              | NotForAll TVar Type
                -- ^ Quantified type variables (of kind *) needs to
                -- match the given type, so it does not work for all types.

              | UnusableFunction QName [Prop]
                -- ^ The given constraints causes the signature of the
                -- function to be not-satisfiable.

              | TooManyPositionalTypeParams
                -- ^ Too many positional type arguments, in an explicit
                -- type instantiation

              | CannotMixPositionalAndNamedTypeParams

              | AmbiguousType [QName]


                deriving Show

-- | Information about how a constraint came to be, used in error reporting.
data ConstraintSource
  = CtComprehension       -- ^ Computing shape of list comprehension
  | CtSplitPat            -- ^ Use of a split pattern
  | CtTypeSig             -- ^ A type signature in a pattern or expression
  | CtInst Expr           -- ^ Instantiation of this expreesion
  | CtSelector
  | CtExactType
  | CtEnumeration
  | CtDefaulting          -- ^ Just defaulting on the command line
  | CtPartialTypeFun TyFunName -- ^ Use of a partial type function.
  | CtImprovement
    deriving Show

data TyFunName = UserTyFun QName | BuiltInTyFun TFun
                deriving Show

instance PP TyFunName where
  ppPrec c (UserTyFun x)    = ppPrec c x
  ppPrec c (BuiltInTyFun x) = ppPrec c x

instance TVars ConstraintSource where
  apSubst su src =
    case src of
      CtComprehension -> src
      CtSplitPat      -> src
      CtTypeSig       -> src
      CtInst e        -> CtInst (apSubst su e)
      CtSelector      -> src
      CtExactType     -> src
      CtEnumeration   -> src
      CtDefaulting    -> src
      CtPartialTypeFun _ -> src
      CtImprovement    -> src

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
      UnsolvedGoal g            -> UnsolvedGoal (apSubst su g)
      UnsolvedDelcayedCt g      -> UnsolvedDelcayedCt (apSubst su g)
      UnexpectedTypeWildCard    -> err
      TypeVariableEscaped t xs  -> TypeVariableEscaped (apSubst su t) xs
      NotForAll x t             -> NotForAll x (apSubst su t)
      UnusableFunction f ps      -> UnusableFunction f (apSubst su ps)
      TooManyPositionalTypeParams -> err
      CannotMixPositionalAndNamedTypeParams -> err
      AmbiguousType _           -> err

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
      UnsolvedGoal g            -> fvs g
      UnsolvedDelcayedCt g      -> fvs g
      UnexpectedTypeWildCard    -> Set.empty
      TypeVariableEscaped t _   -> fvs t
      NotForAll _ t             -> fvs t
      UnusableFunction _ p      -> fvs p
      TooManyPositionalTypeParams -> Set.empty
      CannotMixPositionalAndNamedTypeParams -> Set.empty
      AmbiguousType _           ->  Set.empty

instance FVS Goal where
  fvs g = fvs (goal g)

instance FVS DelayedCt where
  fvs d = fvs (dctAsmps d, dctGoals d) `Set.difference`
                            Set.fromList (map tpVar (dctForall d))


-- This first applies the substitution to the keys of the goal map, then to the
-- values that remain, as applying the substitution to the keys will only ever
-- reduce the number of values that remain.
instance TVars Goals where
  apSubst su (Goals goals) =
    Goals (mapWithKeyTM setGoal (apSubstTypeMapKeys su goals))
    where
    -- as the key for the goal map is the same as the goal, and the substitution
    -- has been applied to the key already, just replace the existing goal with
    -- the key.
    setGoal key g = g { goalSource = apSubst su (goalSource g)
                      , goal       = key
                      }

instance TVars Goal where
  apSubst su g = Goal { goalSource = apSubst su (goalSource g)
                      , goalRange  = goalRange g
                      , goal       = apSubst su (goal g)
                      }

instance TVars HasGoal where
  apSubst su h = h { hasGoal = apSubst su (hasGoal h) }

instance TVars DelayedCt where
  apSubst su g
    | Set.null captured =
       DelayedCt { dctSource = dctSource g
                 , dctForall = dctForall g
                 , dctAsmps  = apSubst su1 (dctAsmps g)
                 , dctGoals  = apSubst su1 (dctGoals g)
                 }
    | otherwise = panic "Cryptol.TypeCheck.Subst.apSubst (DelayedCt)"
                    [ "Captured quantified variables:"
                    , "Substitution: " ++ show m1
                    , "Variables:    " ++ show captured
                    , "Constraint:   " ++ show g
                    ]

    where
    used  = fvs (dctAsmps g, map goal (dctGoals g)) `Set.difference`
                                          Set.fromList (map tpVar (dctForall g))
    m1    = Map.filterWithKey (\k _ -> k `Set.member` used) (suMap su)
    su1   = S { suMap = m1, suDefaulting = suDefaulting su }

    captured = Set.fromList (map tpVar (dctForall g)) `Set.intersection`
                                                          fvs (Map.elems m1)



-- | For use in error messages
cppKind :: Kind -> Doc
cppKind ki =
  case ki of
    KNum  -> text "a numeric type"
    KType -> text "a value type"
    KProp -> text "a constraint"
    _     -> pp ki

addTVarsDescs :: FVS t => NameMap -> t -> Doc -> Doc
addTVarsDescs nm t d
  | Set.null vs = d
  | otherwise   = d $$ text "where" $$ vcat (map desc (Set.toList vs))
  where
  vs                      = Set.filter isFreeTV (fvs t)
  desc v@(TVFree _ _ _ x) = ppWithNames nm v <+> text "is" <+> x
  desc (TVBound {})       = empty



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
           text "Inferred type:" <+> ppWithNames names t2)

      UnsolvedGoal g ->
        nested (text "Unsolved constraint:") (ppWithNames names g)

      UnsolvedDelcayedCt g ->
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

      AmbiguousType xs ->
        text "The inferred type for" <+> commaSep (map pp xs)
          <+> text "is ambiguous." 

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



instance PP ConstraintSource where
  ppPrec _ src =
    case src of
      CtComprehension -> text "list comprehension"
      CtSplitPat      -> text "split (#) pattern"
      CtTypeSig       -> text "type signature"
      CtInst e        -> text "use of" <+> ppUse e
      CtSelector      -> text "use of selector"
      CtExactType     -> text "matching types"
      CtEnumeration   -> text "list enumeration"
      CtDefaulting    -> text "defaulting"
      CtPartialTypeFun f -> text "use of partial type function" <+> pp f
      CtImprovement   -> text "examination of collected goals"

ppUse :: Expr -> Doc
ppUse expr =
  case expr of
    ECon ECDemote       -> text "literal or demoted expression"
    ECon ECInfFrom      -> text "infinite enumeration"
    ECon ECInfFromThen  -> text "infinite enumeration (with step)"
    ECon ECFromThen     -> text "finite enumeration"
    ECon ECFromTo       -> text "finite enumeration"
    ECon ECFromThenTo   -> text "finite enumeration"
    _                   -> text "expression" <+> pp expr

instance PP (WithNames Goal) where
  ppPrec _ (WithNames g names) =
      (ppWithNames names (goal g)) $$
               nest 2 (text "arising from" $$
                       pp (goalSource g)   $$
                       text "at" <+> pp (goalRange g))

instance PP (WithNames DelayedCt) where
  ppPrec _ (WithNames d names) =
    sig $$ nest 2 (vars $$ asmps $$ vcat (map (ppWithNames ns1) (dctGoals d)))
    where
    sig = text "In the definition of" <+> quotes (pp (thing name)) <>
          comma <+> text "at" <+> pp (srcRange name) <> colon

    name  = dctSource d
    vars = case dctForall d of
             [] -> empty
             xs -> text "for any type" <+>
                      fsep (punctuate comma (map (ppWithNames ns1 ) xs))
    asmps = case dctAsmps d of
              [] -> empty
              xs -> nest 2 (vcat (map (ppWithNames ns1) xs)) $$ text "=>"

    ns1 = addTNames (dctForall d) names


instance PP Solved where
  ppPrec _ res =
    case res of
      Solved mb gs  -> text "solved" $$ nest 2 (suDoc $$ vcat (map (pp . goal) gs))
        where suDoc = maybe empty pp mb
      Unsolved      -> text "unsolved"
      Unsolvable    -> text "unsolvable"

