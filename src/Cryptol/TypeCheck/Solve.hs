-- |
-- Module      :  Cryptol.TypeCheck.Solve
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
  , proveModuleTopLevel
  , wfType
  , wfTypeFunction
  , wfTC
  , improveByDefaultingWithPure
  , defaultReplExpr
  ) where

import           Cryptol.Parser.Position(thing)
import           Cryptol.TypeCheck.PP(pp)
import           Cryptol.TypeCheck.AST
import           Cryptol.TypeCheck.Monad
import           Cryptol.TypeCheck.Default
import           Cryptol.TypeCheck.Error(Error(..),Warning(..))
import           Cryptol.TypeCheck.Subst
                    (apSubst, isEmptySubst, substToList,
                          emptySubst,Subst,(@@), Subst)
import qualified Cryptol.TypeCheck.SimpleSolver as Simplify
import           Cryptol.TypeCheck.Solver.Types
import           Cryptol.TypeCheck.Solver.Selector(tryHasGoal)


import           Cryptol.TypeCheck.Solver.SMT(Solver,proveImp)
import           Cryptol.TypeCheck.Solver.Improve(improveProp,improveProps)
import           Cryptol.TypeCheck.Solver.Numeric.Interval
import           Cryptol.Utils.PP (text,vcat,(<+>))
import           Cryptol.Utils.Patterns(matchMaybe)

import           Control.Applicative ((<|>))
import           Control.Monad(mzero)
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

-- | Add additional constraints that ensure validity of a type
-- constructor application. Note that the constraints do not use any
-- partial type functions, so the new constraints are guaranteed to be
-- well-formed. This assumes that the parameters are well-formed.
wfTC :: TC -> [Type] -> [Prop]
wfTC TCIntMod [n] = [ pFin n, n >== tOne ]
wfTC _ _          = []

-- | Add additional constraints that ensure the validity of a type.
wfType :: Type -> [Prop]
wfType t =
  case t of
    TCon c ts ->
      let ps = concatMap wfType ts
      in case c of
           TF f -> wfTypeFunction f ts ++ ps
           TC f -> wfTC f ts ++ ps
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


-- | Try to clean-up any left-over constraints after we've checked everything
-- in a module.  Typically these are either trivial things, or constraints
-- on the module's type parameters.
proveModuleTopLevel :: InferM ()
proveModuleTopLevel =
  do -- io $ putStrLn "Module top level"
     simplifyAllConstraints
     cs <- getParamConstraints
     case cs of
       [] -> return ()
       _  -> do gs <- getGoals
                su <- proveImplication Nothing [] [] gs
                extendSubst su


proveImplication :: Maybe Name -> [TParam] -> [Prop] -> [Goal] -> InferM Subst
proveImplication lnam as ps gs =
  do evars <- varsWithAsmps
     solver <- getSolver

     extraAs <- (map mtpParam . Map.elems) <$> getParamTypes
     extra   <- map thing <$> getParamConstraints

     (mbErr,su) <- io (proveImplicationIO solver lnam evars
                            (extraAs ++ as) (extra ++ ps) gs)
     case mbErr of
       Right ws -> mapM_ recordWarning ws
       Left err -> recordError err
     return su


proveImplicationIO :: Solver
                   -> Maybe Name     -- ^ Checking this function
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







