-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE PatternGuards, BangPatterns, RecordWildCards #-}
{-# LANGUAGE Safe #-}
module Cryptol.TypeCheck.Solve
  ( simplifyAllConstraints
  , proveImplication
  , wfType
  , wfTypeFunction
  , improveByDefaultingWithPure
  , defaultReplExpr
  ) where

import           Cryptol.TypeCheck.PP(pp)
import           Cryptol.TypeCheck.AST
import           Cryptol.TypeCheck.Monad
import           Cryptol.TypeCheck.Subst
                    (apSubst, singleSubst, isEmptySubst, substToList,
                          emptySubst,Subst,listSubst, (@@), Subst,
                           substBinds)
import qualified Cryptol.TypeCheck.SimpleSolver as Simplify
import           Cryptol.TypeCheck.Solver.Types
import           Cryptol.TypeCheck.Solver.Selector(tryHasGoal)
import           Cryptol.TypeCheck.SimpType(tMax)


import           Cryptol.TypeCheck.Solver.SMT(Solver,proveImp,tryGetModel)
import           Cryptol.TypeCheck.Solver.Improve(improveProp,improveProps)
import           Cryptol.TypeCheck.Solver.Numeric.Interval
import           Cryptol.Utils.PP (text,vcat,(<+>))
import           Cryptol.Utils.Panic(panic)
import           Cryptol.Utils.Patterns(matchMaybe)

import           Control.Applicative ((<|>))
import           Control.Monad(mzero,guard)
import qualified Data.Map as Map
import           Data.Set ( Set )
import qualified Data.Set as Set



{- | Add additional constraints that ensure validity of type function.
Note that these constraints do not introduce additional malformed types,
so the well-formedness constraints are guaranteed to be well-formed.
This assumes that the parameters are well-formed. -}
wfTypeFunction :: TFun -> [Type] -> [Prop]
wfTypeFunction TCSub [a,b]             = [ a >== b, pFin b]
wfTypeFunction TCDiv [a,b]             = [ b >== tOne, pFin a ]
wfTypeFunction TCMod [a,b]             = [ b >== tOne, pFin a ]
wfTypeFunction TCLenFromThen   [a,b,w] =
         [ pFin a, pFin b, pFin w, a =/= b, w >== tWidth a ]
wfTypeFunction TCLenFromThenTo [a,b,c] = [ pFin a, pFin b, pFin c, a =/= b ]
wfTypeFunction _ _                     = []

-- | Add additional constraints that ensure the validity of a type.
wfType :: Type -> [Prop]
wfType t =
  case t of
    TCon c ts ->
      let ps = concatMap wfType ts
      in case c of
           TF f -> wfTypeFunction f ts ++ ps
           _    -> ps

    TVar _      -> []
    TUser _ _ s -> wfType s
    TRec fs     -> concatMap (wfType . snd) fs




--------------------------------------------------------------------------------


quickSolverIO :: Ctxt -> [Goal] -> IO (Either Goal (Subst,[Goal]))
quickSolverIO _ [] = return (Right (emptySubst, []))
quickSolverIO ctxt gs =
  case quickSolver ctxt gs of
    Left err ->
      do msg (text "Contradiction:" <+> pp (goal err))
         return (Left err)
    Right (su,gs') ->
      do msg (vcat (map (pp . goal) gs' ++ [pp su]))
         return (Right (su,gs'))
  where
  msg _ = return ()
{-
  shAsmps = case [ pp x <+> text "in" <+> ppInterval i |
               (x,i) <- Map.toList ctxt ] of
              [] -> text ""
              xs -> text "ASMPS:" $$ nest 2 (vcat xs $$ text "===")
  msg d = putStrLn $ show (
             text "quickSolver:" $$ nest 2 (vcat
                [ shAsmps
                , vcat (map (pp.goal) gs)
                , text "==>"
                , d
                ])) -- -}

quickSolver :: Ctxt   -- ^ Facts we can know
            -> [Goal] -- ^ Need to solve these
            -> Either Goal (Subst,[Goal])
            -- ^ Left: contradicting goals,
            --   Right: inferred types, unsolved goals.
quickSolver ctxt gs0 = go emptySubst [] gs0
  where
  go su [] [] = Right (su,[])

  go su unsolved [] =
    case matchMaybe (findImprovement unsolved) of
      Nothing            -> Right (su,unsolved)
      Just (newSu, subs) -> go (newSu @@ su) [] (subs ++ apSubst newSu unsolved)

  go su unsolved (g : gs) =
    case Simplify.simplifyStep ctxt (goal g) of
      Unsolvable _        -> Left g
      Unsolved            -> go su (g : unsolved) gs
      SolvedIf subs       ->
        let cvt x = g { goal = x }
        in go su unsolved (map cvt subs ++ gs)

  -- Probably better to find more than one.
  findImprovement []       = mzero
  findImprovement (g : gs) =
    do (su,ps) <- improveProp False ctxt (goal g)
       return (su, [ g { goal = p } | p <- ps ])
    <|> findImprovement gs





--------------------------------------------------------------------------------

simplifyAllConstraints :: InferM ()
simplifyAllConstraints =
  do simpHasGoals
     gs <- getGoals
     case gs of
       [] -> return ()
       _ ->
        case quickSolver Map.empty gs of
          Left badG      -> recordError (UnsolvedGoals True [badG])
          Right (su,gs1) ->
            do extendSubst su
               addGoals gs1

-- | Simplify @Has@ constraints as much as possible.
simpHasGoals :: InferM ()
simpHasGoals = go False [] =<< getHasGoals
  where
  go _     []       []  = return ()
  go True  unsolved []  = go False [] unsolved
  go False unsolved []  = mapM_ addHasGoal unsolved

  go changes unsolved (g : todo) =
    do (ch,solved) <- tryHasGoal g
       let changes'  = ch || changes
           unsolved' = if solved then unsolved else g : unsolved
       changes' `seq` unsolved `seq` go changes' unsolved' todo




proveImplication :: Name -> [TParam] -> [Prop] -> [Goal] -> InferM Subst
proveImplication lnam as ps gs =
  do evars <- varsWithAsmps
     solver <- getSolver
     (mbErr,su) <- io (proveImplicationIO solver lnam evars as ps gs)
     case mbErr of
       Right ws -> mapM_ recordWarning ws
       Left err -> recordError err
     return su


proveImplicationIO :: Solver
                   -> Name     -- ^ Checking this function
                   -> Set TVar -- ^ These appear in the env., and we should
                               -- not try to default the
                   -> [TParam] -- ^ Type parameters
                   -> [Prop]   -- ^ Assumed constraint
                   -> [Goal]   -- ^ Collected constraints
                   -> IO (Either Error [Warning], Subst)
proveImplicationIO _   _     _         _  [] [] = return (Right [], emptySubst)
proveImplicationIO s f varsInEnv ps asmps0 gs0 =
  do let ctxt = assumptionIntervals Map.empty asmps
     res <- quickSolverIO ctxt gs
     case res of
       Left bad -> return (Left (UnsolvedGoals True [bad]), emptySubst)
       Right (su,[]) -> return (Right [], su)
       Right (su,gs1) ->
         do gs2 <- proveImp s asmps gs1
            case gs2 of
              [] -> return (Right [], su)
              gs3 ->
                do let free = Set.toList
                            $ Set.difference (fvs (map goal gs3)) varsInEnv
                   case improveByDefaultingWithPure free gs3 of
                     (_,_,newSu,_)
                        | isEmptySubst newSu -> return (err gs3, su) -- XXX: Old?
                     (_,newGs,newSu,ws) ->
                       do let su1 = newSu @@ su
                          (res1,su2) <- proveImplicationIO s f varsInEnv ps
                                                 (apSubst su1 asmps0) newGs
                          let su3 = su2 @@ su1
                          case res1 of
                            Left bad -> return (Left bad, su3)
                            Right ws1 -> return (Right (ws++ws1),su3)
  where
  err us =  Left $ cleanupError
                 $ UnsolvedDelayedCt
                 $ DelayedCt { dctSource = f
                              , dctForall = ps
                              , dctAsmps  = asmps0
                              , dctGoals  = us
                              }


  asmps1 = concatMap pSplitAnd asmps0
  (asmps,gs) =
     let gs1 = [ g { goal = p } | g <- gs0, p <- pSplitAnd (goal g)
                                , notElem p asmps1 ]
     in case matchMaybe (improveProps True Map.empty asmps1) of
          Nothing -> (asmps1,gs1)
          Just (newSu,newAsmps) ->
             ( [ TVar x =#= t | (x,t) <- substToList newSu ]
               ++ newAsmps
             , [ g { goal = apSubst newSu (goal g) } | g <- gs1 ]
             )




cleanupError :: Error -> Error
cleanupError err =
  case err of
    UnsolvedDelayedCt d ->
      let noInferVars = Set.null . Set.filter isFreeTV . fvs . goal
          without = filter noInferVars (dctGoals d)
      in UnsolvedDelayedCt $
            if not (null without) then d { dctGoals = without } else d

    _ -> err









assumptionIntervals :: Ctxt -> [Prop] -> Ctxt
assumptionIntervals as ps =
  case computePropIntervals as ps of
    NoChange -> as
    InvalidInterval {} -> as -- XXX: say something
    NewIntervals bs -> Map.union bs as






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
    , [Warning] -- warnings about defaulting
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
        warn (x,t) =
          case x of
            TVFree _ _ _ d -> DefaultingTo d t
            TVBound {} -> panic "Crypto.TypeCheck.Infer"
                 [ "tryDefault attempted to default a quantified variable."
                 ]

        names = substBinds su

    in ( [ a | a <- as, not (a `Set.member` names) ]
       , newOthers ++ others ++ apSubst su fins
       , su
       , map warn defs
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
              su1 = singleSubst x ty
          in ( (x,ty) : [ (y,apSubst su1 t) | (y,t) <- yes ]
             , no         -- We know that `x` does not appear here
             , otherFree  -- We know that `x` did not appear here either

             -- No need to update the `vs` because we've already
             -- checked that there are no recursive dependencies.
             , [ (y, (apSubst su1 ts1, vs1)) | (y,(ts1,vs1)) <- more ]
             )


-- | Try to pick a reasonable instantiation for an expression, with
-- the given type.  This is useful when we do evaluation at the REPL.
-- The resulting types should satisfy the constraints of the schema.
defaultReplExpr :: Solver -> Expr -> Schema
             -> IO (Maybe ([(TParam,Type)], Expr))
defaultReplExpr sol e s =
  if all (\v -> kindOf v == KNum) (sVars s)
     then do let params = map tpVar (sVars s)
                 props  = sProps s
             mbSubst <- tryGetModel sol params props
             return $ do su <- mbSubst
                         guard (null (concatMap pSplitAnd (apSubst su props)))
                         tys <- mapM (bindParam su) params
                         return (zip (sVars s) tys, appExpr tys)
     else return Nothing
  where
  bindParam su tp =
    do let ty  = TVar tp
           ty' = apSubst su ty
       guard (ty /= ty')
       return ty'

  appExpr tys = foldl (\e1 _ -> EProofApp e1) (foldl ETApp e tys) (sProps s)





