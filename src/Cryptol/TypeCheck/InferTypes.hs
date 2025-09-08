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

import           Control.Monad(guard)

import           Cryptol.Parser.Position
import           Cryptol.ModuleSystem.Name (asPrim,nameLoc,nameIdent)
import           Cryptol.TypeCheck.AST
import           Cryptol.TypeCheck.PP
import           Cryptol.TypeCheck.Subst
import           Cryptol.TypeCheck.TypePat
import           Cryptol.TypeCheck.SimpType(tMax)
import           Cryptol.Utils.Ident (PrimIdent(..), preludeName)
import           Cryptol.Utils.Panic(panic)
import           Cryptol.Utils.Misc(anyJust)

import           Data.List(mapAccumL,partition)
import           Data.Maybe(mapMaybe)
import           Data.Set ( Set )
import qualified Data.Set as Set
import           Data.Map ( Map )
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap

import GHC.Generics (Generic)
import Control.DeepSeq

data SolverConfig = SolverConfig
  { solverPath    :: FilePath   -- ^ The SMT solver to invoke
  , solverArgs    :: [String]   -- ^ Additional arguments to pass to the solver
  , solverVerbose :: Int        -- ^ How verbose to be when type-checking
  , solverPreludePath :: [FilePath]
    -- ^ Look for the solver prelude in these locations.
  , solverSmtFile :: Maybe FilePath
    -- ^ The optional file to record SMT solver interactions in the type
    -- checker. If 'Nothing', this will print to @stdout@ instead.
  } deriving (Show, Generic, NFData)


-- | A default configuration for using Z3, where
--   the solver prelude is expected to be found
--   in the given search path.
defaultSolverConfig :: [FilePath] -> SolverConfig
defaultSolverConfig searchPath =
  SolverConfig
  { solverPath = "z3"
  , solverArgs = [ "-smt2", "-in" ]
  , solverVerbose = 0
  , solverPreludePath = searchPath
  , solverSmtFile = Nothing
  }

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

  , saturatedPropSet :: Set Prop
    -- ^ The set of nonliteral goals, saturated by all superclass implications

  , literalGoals :: Map TVar LitGoal
    -- ^ An entry @(a,t)@ corresponds to @Literal t a@.

  , literalLessThanGoals :: Map TVar LitGoal
    -- ^ An entry @(a,t)@ corresponds to @LiteralLessThan t a@.

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


litLessThanGoalToGoal :: (TVar,LitGoal) -> Goal
litLessThanGoalToGoal (a,g) = g { goal = pLiteralLessThan (goal g) (TVar a) }

goalToLitLessThanGoal :: Goal -> Maybe (TVar,LitGoal)
goalToLitLessThanGoal g =
  do (tn,a) <- matchMaybe $ do (tn,b) <- aLiteralLessThan (goal g)
                               a      <- aTVar b
                               return (tn,a)
     return (a, g { goal = tn })


emptyGoals :: Goals
emptyGoals  =
  Goals
  { goalSet = Set.empty
  , saturatedPropSet = Set.empty
  , literalGoals = Map.empty
  , literalLessThanGoals = Map.empty
  }

nullGoals :: Goals -> Bool
nullGoals gs =
  Set.null (goalSet gs) &&
  Map.null (literalGoals gs) &&
  Map.null (literalLessThanGoals gs)

fromGoals :: Goals -> [Goal]
fromGoals gs = map litGoalToGoal (Map.toList (literalGoals gs)) ++
               map litLessThanGoalToGoal (Map.toList (literalLessThanGoals gs)) ++
               Set.toList (goalSet gs)

goalsFromList :: [Goal] -> Goals
goalsFromList = foldr insertGoal emptyGoals

insertGoal :: Goal -> Goals -> Goals
insertGoal g gls
  | Just (a,newG) <- goalToLitGoal g =
       -- XXX: here we are arbitrarily using the info of the first goal,
       -- which could lead to a confusing location for a constraint.
       let jn g1 g2 = g1 { goal = tMax (goal g1) (goal g2) } in
       gls { literalGoals = Map.insertWith jn a newG (literalGoals gls)
           , saturatedPropSet = Set.insert (pFin (TVar a)) (saturatedPropSet gls)
           }

  | Just (a,newG) <- goalToLitLessThanGoal g =
       let jn g1 g2 = g1 { goal = tMax (goal g1) (goal g2) } in
       gls { literalLessThanGoals = Map.insertWith jn a newG (literalLessThanGoals gls)
           }

  -- If the goal is already implied by some other goal, skip it
  | Set.member (goal g) (saturatedPropSet gls) = gls

  -- Otherwise, it is not already implied, add it and saturate
  | otherwise =
       gls { goalSet = gs', saturatedPropSet = sps'  }

       where
       ips  = superclassSet (goal g)
       igs  = Set.map (\p -> g{ goal = p}) ips

       -- remove all the goals that are implied by ips
       gs'  = Set.insert g (Set.difference (goalSet gls) igs)

       -- add the goal and all its implied toals to the saturated set
       sps' = Set.insert (goal g) (Set.union (saturatedPropSet gls) ips)


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
  { hasName :: !Int -- ^ This is the "name" of the constraint,
                    -- used to find the solution for ellaboration.
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
  | CtPattern TypeSource  -- ^ Constraints arising from type-checking patterns
  | CtModuleInstance Range -- ^ Instantiating a parametrized module
  | CtPropGuardsExhaustive Name -- ^ Checking that a use of prop guards is exhastive
  | CtFFI Name            -- ^ Constraints on a foreign declaration required
                          --   by the FFI (e.g. sequences must be finite)
    deriving (Show, Generic, NFData)

selSrc :: Selector -> TypeSource
selSrc l = case l of
             RecordSel la _ -> TypeOfRecordField la
             TupleSel n _   -> TypeOfTupleField n
             ListSel _ _    -> TypeOfSeqElement





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
      CtPropGuardsExhaustive _ -> src
      CtFFI _          -> src


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
addTVarsDescsAfter nm t = addTVarsDescsAfterFVS nm (fvs t)

addTVarsDescsAfterFVS :: NameMap -> Set TVar -> Doc -> Doc
addTVarsDescsAfterFVS nm vs d
  | Set.null vs = d
-- TODO? use `hang` here instead to indent things after "where"
  | otherwise   = d $$ text "where" $$ vcat (map desc (Set.toList vs))
  where
  desc v = ppWithNames nm v <+> text "is" <+> pp (tvInfo v)


addTVarsDescsBefore :: FVS t => NameMap -> t -> Doc -> Doc
addTVarsDescsBefore nm t d = vcat (frontMsg ++ [d] ++ backMsg)
  where
  (vs1,vs2)  = Set.partition isFreeTV (fvs t)

  frontMsg | null vs1  = []
           | otherwise = [hang "Failed to infer the following types:"
                             2 (vcat (map desc1 (Set.toList vs1)))]
  desc1 v    = "•" <+> ppWithNames nm v <.> comma <+> pp (tvInfo v)

  backMsg  | null vs2  = []
           | otherwise = [hang "where"
                             2 (vcat (map desc2 (Set.toList vs2)))]
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
      CtPattern ad    -> "checking a pattern:" <+> pp ad
      CtModuleInstance r -> "module instantiation at" <+> pp r
      CtPropGuardsExhaustive n -> "exhaustion check for prop guards used in defining" <+> pp n
      CtFFI f         -> "declaration of foreign function" <+> pp f

ppUse :: Expr -> Doc
ppUse expr =
  case expr of
    EVar (isPrelPrim -> Just prim)
      | prim == "number"       -> "literal or demoted expression"
      | prim == "fraction"     -> "fractional literal"
      | prim == "infFrom"      -> "infinite enumeration"
      | prim == "infFromThen"  -> "infinite enumeration (with step)"
      | prim == "fromTo"       -> "finite enumeration"
      | prim == "fromThenTo"   -> "finite enumeration"
    _                          -> "expression" <+> pp expr
  where
  isPrelPrim x = do PrimIdent p i <- asPrim x
                    guard (p == preludeName)
                    pure i

instance PP (WithNames Goal) where
  ppPrec _ (WithNames g names) =
      hang (ppWithNames names (goal g))
         2 (text "arising from" $$
            pp (goalSource g)   $$
            text "at" <+> pp (goalRange g))

instance PP (WithNames DelayedCt) where
  ppPrec _ (WithNames d names) =
    withPPCfg $ \cfg ->
    let
      bullets xs = [ "•" <+> x | x <- xs ]
  
      sig = case name of
              Just n -> "in the definition of" <+> quotes (pp n) <.>
                        comma <+> "at" <+> pp (nameLoc n) <.> comma
              Nothing -> "when checking the module's parameters,"
  
      name  = dctSource d
      vars = case otherTPs of
               [] -> []
               xs -> ["for any type" <+> commaSep (map (ppWithNames ns1) xs)]
      asmps = case dctAsmps d of
                [] -> []
                xs -> [hang "assuming"
                         2 (vcat (bullets (map (ppWithNames ns1) xs)))]
  
      tvars = fvs (dctAsmps d, dctGoals d)
      used = filter ((`Set.member` tvars) . TVBound) (dctForall d)
      isModP tp =
        case tpFlav tp of
          TPModParam {} -> True
          _ -> False
      (mpTPs,otherTPs) = partition isModP used
      explain = addTVarsDescsAfterFVS ns1 (Set.fromList (map TVBound mpTPs))
      mps = computeModParamNames cfg mpTPs names
      ns1 = addTNames cfg otherTPs mps
    in
    sig $$
    hang "we need to show that"
    
       2 (explain (vcat ( vars ++ asmps ++
               [ hang "the following constraints hold:"
                    2 (vcat
                       $ bullets
                       $ map (ppWithNames ns1)
                       $ dctGoals d )])))
 
    
 



-- | Add a suffix to a name to make a different label.
nameVariant :: Int -> String -> String
nameVariant n x = if n == 0 then x else x ++ suff
  where
  useUnicode = True

  suff
    | n < 10 && useUnicode = [toEnum (0x2080 + n)]
    | otherwise = show n

  

-- | Pick names for the type parameters that correspond to module parameters,
-- avoiding strings that already appear in the given name map.
-- Returns an extended name map.
computeModParamNames :: PPCfg -> [TParam] -> NameMap -> NameMap
computeModParamNames cfg tps names = IntMap.fromList newNames `IntMap.union` names
  where
  newNames = snd (mapAccumL pickName used0 (mapMaybe isModP tps))

  used0 = Set.fromList (map (show . fixPPCfg cfg) (IntMap.elems names))

  pickName used (u,i) =
    let ns   = filter (not . (`Set.member` used))
              $ map (`nameVariant` i) [0..]
        name = case ns of
                 x : _ -> x
                 []    -> panic "computeModParamNames" ["Out of names!"]
    in (Set.insert name used, (u,text name))

  isModP tp =
    case tpFlav tp of
      TPModParam x -> Just (tpUnique tp, show (pp (nameIdent x)))
      _ -> Nothing
