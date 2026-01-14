{-# LANGUAGE Safe #-}

module Cryptol.TypeCheck.Default where

import qualified Data.Set as Set
import           Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe(mapMaybe, isJust)
import Data.List((\\),nub)
import Control.Monad(guard,mzero)

import Cryptol.TypeCheck.Type
import Cryptol.TypeCheck.SimpType(tMax)
import Cryptol.TypeCheck.Error(Warning(..), Error(..))
import Cryptol.TypeCheck.Subst(Subst,apSubst,listSubst,substBinds,uncheckedSingleSubst)
import Cryptol.TypeCheck.InferTypes(Goal,goal,Goals(..),goalsFromList)
import Cryptol.TypeCheck.Solver.SMT(Solver,tryGetModel,shrinkModel)
import Cryptol.Utils.Panic(panic)

--------------------------------------------------------------------------------

-- | We default constraints of the form @Literal t a@ and @FLiteral m n r a@.
--
--   For @Literal t a@ we examine the context of constraints on the type @a@
--   to decide how to default.
-- 
--   We do NOT default if:
--     * `Logic t` and `a` in `fvs t`
--     * `Integral t`, and `t /= a`, and `a` in `fvs t`
--
--   Otherwise, we default to either @Integer@ or @Rational@.
--   In particular, if we need to satisfy the @Field a@, constraint, we choose
--   @Rational@ and otherwise we choose @Integer@.
--
--   For @FLiteral t a@ we always default to @Rational@.
defaultLiterals :: [TVar] -> [Goal] -> ([TVar], Subst, [Warning])
defaultLiterals as gs = let (binds,warns) = unzip (mapMaybe tryDefVar as)
                        in (as \\ map fst binds, listSubst binds, warns)
  where
  gSet = goalsFromList gs
  allProps = saturatedPropSet gSet
  has p a  = Set.member (p (TVar a)) allProps

  isLiteralGoal a = isJust (Map.lookup a (literalGoals gSet)) ||
                    isJust (Map.lookup a (literalLessThanGoals gSet))

  disableDefaultPred a p =
    case pIsLogic p of
      Just t -> a `Set.member` fvs t
      Nothing ->
        case pIsIntegral p of
          Just t ->
            case tIsVar t of
              Just _  -> False 
              Nothing -> a `Set.member` fvs t
          Nothing -> False

  disableDefault a = any (disableDefaultPred a) allProps

  tryDefVar a =
    -- If there is an `FLiteral` constraint we use that for defaulting.
    case Map.lookup a (flitDefaultCandidates gSet) of
      Just m -> m

      -- Otherwise we try to use a `Literal`
      Nothing
        | isLiteralGoal a && not (disableDefault a)  -> do
           defT <- 
                   if has pField a && not (has pIntegral a)
                      then pure tRational
                   else if not (has pField a) then pure tInteger
                   else mzero
           let d    = tvInfo a
               w    = DefaultingTo d defT
           guard (not (Set.member a (fvs defT)))  -- Currently shouldn't happen
                                                  -- but future proofing.
           -- XXX: Make sure that `defT` has only variables that `a` is allowed
           -- to depend on
           return ((a,defT),w)

        | otherwise -> mzero

flitDefaultCandidates :: Goals -> Map TVar (Maybe ((TVar,Type),Warning))
flitDefaultCandidates gs =
  Map.fromList (mapMaybe flitCandidate (Set.toList (goalSet gs)))
  where
  allProps = saturatedPropSet gs
  has p a  = Set.member (p (TVar a)) allProps

  flitCandidate g =
    do (_,_,_,x) <- pIsFLiteral (goal g)
       a         <- tIsVar x
       pure (a, do guard (not (has pLogic a) && not (has pIntegral a))
                   let defT = tRational
                   let w    = DefaultingTo (tvInfo a) defT
                   pure ((a,defT),w))


--------------------------------------------------------------------------------

-- This is what we use to avoid ambiguity when generalizing.

{- If a variable, `a`, is:
    1. Of kind KNum
    2. Generic (i.e., does not appear in the environment)
    3. It appears only in constraints but not in the resulting type
       (i.e., it is not on the RHS of =>)
    4. It (say, the variable 'a') appears only in constraints like this:
        3.1 `a >= t` with (`a` not in `fvs t`)
        3.2 in the `s` of `fin s`

  Then we replace `a` with `max(t1 .. tn)` where the `ts`
  are from the constraints `a >= t`.

  If `t1 .. tn` is empty, then we replace `a` with 0.

  This function assumes that 1-3 have been checked, and implements the rest.
  So, given some variables and constraints that are about to be generalized,
  we return:
      1. a new (same or smaller) set of variables to quantify,
      2. a new set of constraints,
      3. a substitution which indicates what got defaulted.
-}





improveByDefaultingWithPure :: [TVar] -> [Goal] ->
    ( [TVar]    -- non-defaulted
    , [Goal]    -- new constraints
    , Subst     -- improvements from defaulting
    , [Error]   -- width defaulting errors
    )
improveByDefaultingWithPure as ps =
  classify (Map.fromList [ (a,([],Set.empty)) | a <- as ]) [] [] ps

  where
  -- leq: candidate definitions (i.e. of the form x >= t, x `notElem` fvs t)
  --      for each of these, we keep the list of `t`, and the free vars in them.
  -- fins: all `fin` constraints
  -- others: any other constraints
  classify leqs fins others [] =
    let -- First, we use the `leqs` to choose some definitions.
        (defs, newOthers)  = select [] [] (fvs others) (Map.toList leqs)
        su                 = listSubst defs
        names              = substBinds su
        mkErr (x,t) =
          case x of
            TVFree _ _ _ d
              | Just 0 <- tIsNum t -> AmbiguousSize d Nothing
              | otherwise -> AmbiguousSize d (Just t)
            TVBound {} -> panic "Crypto.TypeCheck.Infer"
                 [ "tryDefault attempted to default a quantified variable."
                 ]

    in ( [ a | a <- as, not (a `Set.member` names) ]
       , newOthers ++ others ++ nub (apSubst su fins)
       , su
       , map mkErr defs
       )


  classify leqs fins others (prop : more) =
      case tNoUser (goal prop) of

        -- We found a `fin` constraint.
        TCon (PC PFin) [ _ ] -> classify leqs (prop : fins) others more

        -- Things of the form: x >= T(x) are not defaulted.
        TCon (PC PGeq) [ TVar x, t ]
          | x `elem` as && x `Set.notMember` freeRHS ->
           classify leqs' fins others more
           where freeRHS = fvs t
                 add (xs1,vs1) (xs2,vs2) = (xs1 ++ xs2, Set.union vs1 vs2)
                 leqs' = Map.insertWith add x ([(t,prop)],freeRHS) leqs

        _ -> classify leqs fins (prop : others) more


  -- Pickout which variables may be defaulted and how.
    -- XXX: simpType t
  select yes no _ [] = ([ (x, t) | (x,t) <- yes ] ,no)
  select yes no otherFree ((x,(rhsG,vs)) : more) =
    select newYes newNo newFree newMore

    where
    (ts,gs) = unzip rhsG

    -- `x` selected only if appears nowehere else.
    -- this includes other candidates for defaulting.
    (newYes,newNo,newFree,newMore)

        -- Mentioned in other constraints, definately not defaultable.
        | x `Set.member` otherFree = noDefaulting

        | otherwise =
            let deps = [ y | (y,(_,yvs)) <- more, x `Set.member` yvs ]
                recs = filter (`Set.member` vs) deps
            in if not (null recs) || isBoundTV x -- x >= S(y), y >= T(x)
                                 then noDefaulting

                                  -- x >= S,    y >= T(x)   or
                                  -- x >= S(y), y >= S
                                  else yesDefaulting

        where
        noDefaulting = ( yes, gs ++ no, vs `Set.union` otherFree, more )

        yesDefaulting =
          let ty  = case ts of
                      [] -> tNum (0::Int)
                      _  -> foldr1 tMax ts
              su1 = uncheckedSingleSubst x ty
          in ( (x,ty) : [ (y,apSubst su1 t) | (y,t) <- yes ]
             , no         -- We know that `x` does not appear here
             , otherFree  -- We know that `x` did not appear here either

             -- No need to update the `vs` because we've already
             -- checked that there are no recursive dependencies.
             , [ (y, (apSubst su1 ts1, vs1)) | (y,(ts1,vs1)) <- more ]
             )


{- | Try to pick a reasonable instantiation for an expression with
the given type.  This is useful when we do evaluation at the REPL.
The resulting types should satisfy the constraints of the schema.
The parameters should be all of numeric kind, and the props should als
be numeric -}
defaultReplExpr' :: Solver -> [TParam] -> [Prop] -> IO (Maybe [ (TParam,Type) ])
defaultReplExpr' sol as props =
  do let params = map tpVar as
     mb <- tryGetModel sol params props
     case mb of
       Nothing -> return Nothing
       Just mdl0 ->
         do mdl <- shrinkModel sol params props mdl0
            let su = listSubst [ (x, tNat' n) | (x,n) <- mdl ]
            return $
              do guard (null (concatMap pSplitAnd (apSubst su props)))
                 tys <- mapM (bindParam su) params
                 return (zip as tys)
  where
  bindParam su tp =
    do let ty  = TVar tp
           ty' = apSubst su ty
       guard (ty /= ty')
       return ty'






