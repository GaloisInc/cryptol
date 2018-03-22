-- |
-- Module      :  Cryptol.TypeCheck.InferTypes
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- This module contains types used during type inference.

{-# LANGUAGE Safe #-}

{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
module Cryptol.TypeCheck.InferTypes where

import           Cryptol.TypeCheck.AST
import           Cryptol.TypeCheck.Subst
import           Cryptol.Parser.Position
import           Cryptol.Utils.PP
import           Cryptol.ModuleSystem.Name (asPrim,nameLoc)
import           Cryptol.TypeCheck.PP
import           Cryptol.Utils.Ident (ModName, identText)
import           Cryptol.Utils.Panic(panic)
import           Cryptol.Utils.Misc(anyJust)

import           Data.Set ( Set )
import qualified Data.Set as Set

import GHC.Generics (Generic)
import Control.DeepSeq

data SolverConfig = SolverConfig
  { solverPath    :: FilePath   -- ^ The SMT solver to invoke
  , solverArgs    :: [String]   -- ^ Additional arguments to pass to the solver
  , solverVerbose :: Int        -- ^ How verbose to be when type-checking
  , solverPreludePath :: [FilePath]
    -- ^ Look for the solver prelude in these locations.
  } deriving (Show, Generic, NFData)

-- | The types of variables in the environment.
data VarType = ExtVar Schema
               -- ^ Known type

             | CurSCC {- LAZY -} Expr Type
               {- ^ Part of current SCC.  The expression will replace the
               variable, after we are done with the SCC.  In this way a
               variable that gets generalized is replaced with an approproate
               instantiations of itslef. -}

-- XXX: Temporary, until we figure out, how to apply substitutions
-- with normalization to the type Map
newtype Goals = Goals (Set Goal) -- Goals (TypeMap Goal)
                deriving (Show)

emptyGoals :: Goals
emptyGoals  = Goals Set.empty -- emptyTM

nullGoals :: Goals -> Bool
nullGoals (Goals tm) = Set.null tm -- nullTM tm

fromGoals :: Goals -> [Goal]
fromGoals (Goals tm) = Set.toList tm -- membersTM tm

insertGoal :: Goal -> Goals -> Goals
insertGoal g (Goals tm) = Goals (Set.insert g tm) -- (insertTM (goal g) g tm)

-- | Something that we need to find evidence for.
data Goal = Goal
  { goalSource :: ConstraintSource  -- ^ What it is about
  , goalRange  :: Range             -- ^ Part of source code that caused goal
  , goal       :: Prop              -- ^ What needs to be proved
  } deriving (Show, Generic, NFData)

instance Eq Goal where
  x == y = goal x == goal y

instance Ord Goal where
  compare x y = compare (goal x) (goal y)

data HasGoal = HasGoal
  { hasName :: !Int
  , hasGoal :: Goal
  } deriving Show

-- | Delayed implication constraints, arising from user-specified type sigs.
data DelayedCt = DelayedCt
  { dctSource :: Maybe Name   -- ^ Signature that gave rise to this constraint
                              -- Nothing means module top-level
  , dctForall :: [TParam]
  , dctAsmps  :: [Prop]
  , dctGoals  :: [Goal]
  } deriving (Show, Generic, NFData)

-- | Information about how a constraint came to be, used in error reporting.
data ConstraintSource
  = CtComprehension       -- ^ Computing shape of list comprehension
  | CtSplitPat            -- ^ Use of a split pattern
  | CtTypeSig             -- ^ A type signature in a pattern or expression
  | CtInst Expr           -- ^ Instantiation of this expression
  | CtSelector
  | CtExactType
  | CtEnumeration
  | CtDefaulting          -- ^ Just defaulting on the command line
  | CtPartialTypeFun TyFunName -- ^ Use of a partial type function.
  | CtImprovement
  | CtPattern Doc         -- ^ Constraints arising from type-checking patterns
  | CtModuleInstance ModName -- ^ Instantiating a parametrized module
    deriving (Show, Generic, NFData)

data TyFunName = UserTyFun Name | BuiltInTyFun TFun
                deriving (Show, Generic, NFData)

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
      CtPattern _      -> src
      CtModuleInstance _ -> src


instance FVS Goal where
  fvs g = fvs (goal g)

instance FVS DelayedCt where
  fvs d = fvs (dctAsmps d, dctGoals d) `Set.difference`
                            Set.fromList (map tpVar (dctForall d))


-- This first applies the substitution to the keys of the goal map, then to the
-- values that remain, as applying the substitution to the keys will only ever
-- reduce the number of values that remain.
instance TVars Goals where
  apSubst su (Goals gs) = case anyJust apG (Set.toList gs) of
                            Nothing -> Goals gs
                            Just gs1 -> Goals $ Set.fromList
                                              $ concatMap norm gs1
    where
    norm g = [ g { goal = p } | p <- pSplitAnd (goal g) ]
    apG g  = mk g <$> apSubstMaybe su (goal g)
    mk g p = g { goal = p }

{-
  apSubst su (Goals gs) = Goals (Set.fromList . mapAp

  apSubst su (Goals goals) =
    Goals (mapWithKeyTM setGoal (apSubstTypeMapKeys su goals))
    where
    -- as the key for the goal map is the same as the goal, and the substitution
    -- has been applied to the key already, just replace the existing goal with
    -- the key.
    setGoal key g = g { goalSource = apSubst su (goalSource g)
                      , goal       = key
                      }
-}

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
                 , dctAsmps  = apSubst su (dctAsmps g)
                 , dctGoals  = apSubst su (dctGoals g)
                 }

    | otherwise = panic "Cryptol.TypeCheck.Subst.apSubst (DelayedCt)"
                    [ "Captured quantified variables:"
                    , "Substitution: " ++ show su
                    , "Variables:    " ++ show captured
                    , "Constraint:   " ++ show g
                    ]

    where
    captured = Set.fromList (map tpVar (dctForall g))
               `Set.intersection`
               subVars
    subVars = Set.unions
                $ map (fvs . applySubstToVar su)
                $ Set.toList used
    used = fvs (dctAsmps g, map goal (dctGoals g)) `Set.difference`
                Set.fromList (map tpVar (dctForall g))

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
      CtPattern desc  -> text "checking a pattern:" <+> desc
      CtModuleInstance n -> text "module instantiation" <+> pp n

ppUse :: Expr -> Doc
ppUse expr =
  case expr of
    EVar (asPrim -> Just prim)
      | identText prim == "demote"       -> text "literal or demoted expression"
      | identText prim == "infFrom"      -> text "infinite enumeration"
      | identText prim == "infFromThen"  -> text "infinite enumeration (with step)"
      | identText prim == "fromThen"     -> text "finite enumeration"
      | identText prim == "fromTo"       -> text "finite enumeration"
      | identText prim == "fromThenTo"   -> text "finite enumeration"
    _                          -> text "expression" <+> pp expr

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
    sig = case name of
            Just n -> text "In the definition of" <+> quotes (pp n) <>
                          comma <+> text "at" <+> pp (nameLoc n) <> colon
            Nothing -> text "When checking the module's parameters."

    name  = dctSource d
    vars = case dctForall d of
             [] -> empty
             xs -> text "for any type" <+>
                      fsep (punctuate comma (map (ppWithNames ns1 ) xs))
    asmps = case dctAsmps d of
              [] -> empty
              xs -> nest 2 (vcat (map (ppWithNames ns1) xs)) $$ text "=>"

    ns1 = addTNames (dctForall d) names



