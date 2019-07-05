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

import           Cryptol.Parser.Position
import           Cryptol.ModuleSystem.Name (asPrim,nameLoc)
import           Cryptol.TypeCheck.AST
import           Cryptol.TypeCheck.PP
import           Cryptol.TypeCheck.Subst
import           Cryptol.TypeCheck.TypePat
import           Cryptol.TypeCheck.SimpType(tMax)
import           Cryptol.Utils.Ident (ModName, identText)
import           Cryptol.Utils.Panic(panic)
import           Cryptol.Utils.Misc(anyJust)
import           Cryptol.Utils.Patterns(matchMaybe)

import           Data.Set ( Set )
import qualified Data.Set as Set
import           Data.Map ( Map )
import qualified Data.Map as Map

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
               variable that gets generalized is replaced with an appropriate
               instantiation of itself. -}

data Goals = Goals
  { goalSet :: Set Goal
    -- ^ A bunch of goals, not including the ones in 'literalGoals'.

  , literalGoals :: Map TVar LitGoal
    -- ^ An entry @(a,t)@ corresponds to @Literal t a@.
  } deriving (Show)

-- | This abuses the type 'Goal' a bit. The 'goal' field contains
-- only the numeric part of the Literal constraint.  For example,
-- @(a, Goal { goal = t })@ representats the goal for @Literal t a@
type LitGoal = Goal

litGoalToGoal :: (TVar,LitGoal) -> Goal
litGoalToGoal (a,g) = g { goal = pLiteral (goal g) (TVar a) }

goalToLitGoal :: Goal -> Maybe (TVar,LitGoal)
goalToLitGoal g =
  do (tn,a) <- matchMaybe $ do (tn,b) <- aLiteral (goal g)
                               a      <- aTVar b
                               return (tn,a)
     return (a, g { goal = tn })



emptyGoals :: Goals
emptyGoals  = Goals { goalSet = Set.empty, literalGoals = Map.empty }

nullGoals :: Goals -> Bool
nullGoals gs = Set.null (goalSet gs) && Map.null (literalGoals gs)

fromGoals :: Goals -> [Goal]
fromGoals gs = map litGoalToGoal (Map.toList (literalGoals gs)) ++
               Set.toList (goalSet gs)

goalsFromList :: [Goal] -> Goals
goalsFromList = foldr insertGoal emptyGoals

insertGoal :: Goal -> Goals -> Goals
insertGoal g gs
  | Just (a,newG) <- goalToLitGoal g =
                gs { literalGoals = Map.insertWith jn a newG (literalGoals gs) }
  | otherwise = gs { goalSet = Set.insert g (goalSet gs) }

  where
  jn g1 g2 = g1 { goal = tMax (goal g1) (goal g2) }
  -- XXX: here we are arbitrarily using the info of the first goal,
  -- which could lead to a confusing location for a constraint.

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


-- | A solution for a 'HasGoal'
data HasGoalSln = HasGoalSln
  { hasDoSelect :: Expr -> Expr
    -- ^ Select a specific field from the input expsression.

  , hasDoSet    :: Expr -> Expr -> Expr
    -- ^ Set a field of the first expression to the second expression
  }


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
  | CtPartialTypeFun Name -- ^ Use of a partial type function.
  | CtImprovement
  | CtPattern Doc         -- ^ Constraints arising from type-checking patterns
  | CtModuleInstance ModName -- ^ Instantiating a parametrized module
    deriving (Show, Generic, NFData)



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


instance TVars Goals where
  -- XXX: could be more efficient
  apSubst su gs = case anyJust apG (fromGoals gs) of
                    Nothing  -> gs
                    Just gs1 -> goalsFromList (concatMap norm gs1)
    where
    norm g = [ g { goal = p } | p <- pSplitAnd (goal g) ]
    apG g  = mk g <$> apSubstMaybe su (goal g)
    mk g p = g { goal = p }


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

addTVarsDescsAfter :: FVS t => NameMap -> t -> Doc -> Doc
addTVarsDescsAfter nm t d
  | Set.null vs = d
  | otherwise   = d $$ text "where" $$ vcat (map desc (Set.toList vs))
  where
  vs     = fvs t
  desc v = ppWithNames nm v <+> text "is" <+> pp (tvInfo v)

addTVarsDescsBefore :: FVS t => NameMap -> t -> Doc -> Doc
addTVarsDescsBefore nm t d = frontMsg $$ d $$ backMsg
  where
  (vs1,vs2)  = Set.partition isFreeTV (fvs t)

  frontMsg | null vs1  = empty
           | otherwise = "Failed to infer the following types:"
                         $$ nest 2 (vcat (map desc1 (Set.toList vs1)))
  desc1 v    = "•" <+> ppWithNames nm v <.> comma <+> pp (tvInfo v)

  backMsg  | null vs2  = empty
           | otherwise = "where"
                         $$ nest 2 (vcat (map desc2 (Set.toList vs2)))
  desc2 v    = ppWithNames nm v <+> text "is" <+> pp (tvInfo v)



instance PP ConstraintSource where
  ppPrec _ src =
    case src of
      CtComprehension -> "list comprehension"
      CtSplitPat      -> "split (#) pattern"
      CtTypeSig       -> "type signature"
      CtInst e        -> "use of" <+> ppUse e
      CtSelector      -> "use of selector"
      CtExactType     -> "matching types"
      CtEnumeration   -> "list enumeration"
      CtDefaulting    -> "defaulting"
      CtPartialTypeFun f -> "use of partial type function" <+> pp f
      CtImprovement   -> "examination of collected goals"
      CtPattern desc  -> "checking a pattern:" <+> desc
      CtModuleInstance n -> "module instantiation" <+> pp n

ppUse :: Expr -> Doc
ppUse expr =
  case expr of
    EVar (asPrim -> Just prim)
      | identText prim == "number"       -> "literal or demoted expression"
      | identText prim == "infFrom"      -> "infinite enumeration"
      | identText prim == "infFromThen"  -> "infinite enumeration (with step)"
      | identText prim == "fromTo"       -> "finite enumeration"
      | identText prim == "fromThenTo"   -> "finite enumeration"
    _                                    -> "expression" <+> pp expr

instance PP (WithNames Goal) where
  ppPrec _ (WithNames g names) =
      (ppWithNames names (goal g)) $$
               nest 2 (text "arising from" $$
                       pp (goalSource g)   $$
                       text "at" <+> pp (goalRange g))

instance PP (WithNames DelayedCt) where
  ppPrec _ (WithNames d names) =
    sig $$ "we need to show that" $$
    nest 2 (vcat [ vars, asmps, "the following constraints hold:"
                 , nest 2 $ vcat
                          $ bullets
                          $ map (ppWithNames ns1)
                          $ dctGoals d ])
    where
    bullets xs = [ "•" <+> x | x <- xs ]

    sig = case name of
            Just n -> "in the definition of" <+> quotes (pp n) <.>
                      comma <+> "at" <+> pp (nameLoc n) <.> comma
            Nothing -> "when checking the module's parameters,"

    name  = dctSource d
    vars = case dctForall d of
             [] -> empty
             xs -> "for any type" <+>
                      fsep (punctuate comma (map (ppWithNames ns1 ) xs))
    asmps = case dctAsmps d of
              [] -> empty
              xs -> "assuming" $$
                    nest 2 (vcat (bullets (map (ppWithNames ns1) xs)))

    ns1 = addTNames (dctForall d) names



