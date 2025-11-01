-- |
-- Module      :  Cryptol.TypeCheck.Solve
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE PatternGuards, BangPatterns, RecordWildCards #-}
module Cryptol.TypeCheck.Solve
  ( simplifyAllConstraints
  , proveImplication
  , tryProveImplication
  , proveModuleTopLevel
  , defaultAndSimplify
  , defaultReplExpr
  , quickSolver
  , buildSolverCtxt
  ) where

import           Cryptol.Parser.Position(thing,emptyRange)
import           Cryptol.TypeCheck.PP -- (pp)
import           Cryptol.TypeCheck.AST
import           Cryptol.TypeCheck.Monad
import           Cryptol.TypeCheck.Default
import           Cryptol.TypeCheck.SimpType(tWidth)
import           Cryptol.TypeCheck.Error(Error(..),Warning(..))
import           Cryptol.TypeCheck.Subst
                    (apSubst, isEmptySubst, substToList,
                          emptySubst,Subst,(@@), Subst, listParamSubst)
import qualified Cryptol.TypeCheck.SimpleSolver as Simplify
import           Cryptol.TypeCheck.Solver.Types
import           Cryptol.TypeCheck.Solver.Selector(tryHasGoal)

import           Cryptol.TypeCheck.Solver.SMT(Solver,proveImp,isNumeric)
import           Cryptol.TypeCheck.Solver.Improve(improveProp,improveProps)
import           Cryptol.TypeCheck.Solver.Numeric.Interval
import           Cryptol.Utils.Patterns(matchMaybe)

import           Control.Applicative ((<|>))
import           Control.Monad(mzero)
import           Data.Containers.ListUtils (nubOrd)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set ( Set )
import qualified Data.Set as Set
import           Data.List(partition)
import           Data.Maybe(listToMaybe,fromMaybe)





quickSolverIO :: Ctxt -> [Goal] -> IO (Either Error (Subst,[Goal]))
quickSolverIO _ [] = return (Right (emptySubst, []))
quickSolverIO ctxt gs =
  case quickSolver ctxt gs of
    Left err -> return (Left err)
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
            -> Either Error (Subst,[Goal])
            -- ^ Left: contradicting goals,
            --   Right: inferred types, unsolved goals.
quickSolver ctxt gs0 = go emptySubst [] gs0
  where
  go su [] [] = Right (su,[])

  go su unsolved [] =
    case matchMaybe (findImprovement noIncompatible unsolved) of
      Nothing -> Right (su,unsolved)
      Just imp ->
        case imp of
          Right (newSu, subs) ->
            go (newSu @@ su) [] (subs ++ apSubst newSu unsolved)
          Left err -> Left err

  go su unsolved (g : gs)
    | Set.member (goal g) (saturatedAsmps ctxt) = go su unsolved gs

  go su unsolved (g : gs) =
    case Simplify.simplifyStep ctxt (goal g) of
      Unsolvable          -> Left (UnsolvableGoals [g])
      Unsolved            -> go su (g : unsolved) gs
      SolvedIf subs       ->
        let cvt x = g { goal = x }
        in go su unsolved (map cvt subs ++ gs)

  -- Probably better to find more than one.
  findImprovement inc [] =
    do let bad = Map.intersectionWith (,) (integralTVars inc) (fracTVars inc)
       case Map.minView bad of
         Just ((g1,g2),_) -> pure $ Left $ UnsolvableGoals [g1,g2]
         Nothing -> mzero

  findImprovement inc (g : gs) =
    do (su,ps) <- improveProp False ctxt (goal g)
       return (Right (su, [ g { goal = p } | p <- ps ]))
    <|>
    findImprovement (addIncompatible g inc) gs


--------------------------------------------------------------------------------
-- Look for type variable with incompatible constraints

data Incompatible = Incompatible
  { integralTVars :: Map TVar Goal    -- ^ Integral a
  , fracTVars     :: Map TVar Goal    -- ^ Field a or FLiteral 
  }

noIncompatible :: Incompatible
noIncompatible = Incompatible
  { integralTVars = Map.empty
  , fracTVars     = Map.empty
  }

addIncompatible :: Goal -> Incompatible -> Incompatible
addIncompatible g i =
  fromMaybe i $
  do tv <- tIsVar =<< pIsIntegral (goal g)
     pure i { integralTVars = Map.insert tv g (integralTVars i) }
  <|>
  do tv <- tIsVar =<< pIsField (goal g)
     pure i { fracTVars = Map.insert tv g (fracTVars i) }
  <|>
  do (_,_,_,t) <- pIsFLiteral (goal g)
     tv        <- tIsVar t
     pure i { fracTVars = Map.insert tv g (fracTVars i) }





--------------------------------------------------------------------------------


defaultReplExpr :: Solver -> Expr -> Schema ->
                    IO (Maybe ([(TParam,Type)], Expr))

defaultReplExpr sol expr sch =
  do mb <- defaultReplExpr' sol numVs numPs
     case mb of
       Nothing -> return Nothing
       Just numBinds -> return $
         do let optss = map tryDefVar otherVs
            su    <- listToMaybe
                       [ binds | nonSu <- sequence optss
                               , let binds = nonSu ++ numBinds
                               , validate binds ]
            tys <- sequence [ lookup v su | v <- sVars sch ]
            return (su, appExpr tys)

  where
  validate binds =
    let su = listParamSubst binds
    in null (concatMap pSplitAnd (apSubst su (sProps sch)))

  (numVs,otherVs) = partition (kindIs KNum) (sVars sch)
  (numPs,otherPs) = partition isNumeric (sProps sch)


  kindIs k x = kindOf x == k

  gSet  = goalsFromList
           [ Goal { goal = p
                  , goalRange = emptyRange
                  , goalSource = CtDefaulting } | p <- otherPs ]

  fLitGoals = flitDefaultCandidates gSet

  tryDefVar :: TParam -> [(TParam, Type)]
  tryDefVar a
    -- REPL defaulting for floating-point literals
    | Just m <- Map.lookup (TVBound a) fLitGoals
    = case m of
        Just ((_,t),_) -> [(a,t)]
        Nothing        -> []

    -- REPL defaulting for integer literals
    | Just gt <- Map.lookup (TVBound a) (literalGoals gSet)
    = let ok p = not (Set.member (TVBound a) (fvs p)) in
      [ (a,t) | t <- [ tInteger, tWord (tWidth (goal gt)) ]
              , ok t ]

    -- REPL defaulting for variables unconstrained by a literal constraint
    | otherwise = [ (a,t) | t <- [tInteger, tRational, tBit] ]

  appExpr tys = foldl (\e1 _ -> EProofApp e1)
                      (foldl ETApp expr tys)
                      (sProps sch)


defaultAndSimplify :: [TVar] -> [Goal] -> ([TVar],[Goal],Subst,[Warning],[Error])
defaultAndSimplify as gs =
  let (as1, gs1, su1, ws) = defLit
      (as2, gs2, su2, errs) = improveByDefaultingWithPure as1 gs1
  in (as2,gs2,su2 @@ su1, ws, errs)

  where
  defLit
    | isEmptySubst su = nope
    | otherwise       = case quickSolver mempty (apSubst su gs) of
                          Left _ -> nope -- hm?
                          Right (su1,gs1) -> (as1,gs1,su1@@su,ws)
    where (as1,su,ws) = defaultLiterals as gs
          nope        = (as,gs,emptySubst,[])



simplifyAllConstraints :: InferM ()
simplifyAllConstraints =
  do simpHasGoals
     gs <- getGoals
     case gs of
       [] -> return ()
       _ ->
        case quickSolver mempty gs of
          Left err -> recordError err
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
  do simplifyAllConstraints
     gs <- getGoals
     let vs = Set.toList (Set.filter isFreeTV (fvs gs))
         (_,gs1,su1,ws,errs) = defaultAndSimplify vs gs
     extendSubst su1
     mapM_ recordWarning ws
     mapM_ recordError errs

     cs <- getParamConstraints
     case cs of
       [] -> addGoals gs1
       _  -> do su2 <- proveImplication False Nothing [] [] gs1
                extendSubst su2

-- | Prove an implication, and return any improvements that we computed.
-- Records errors, if any of the goals couldn't be solved.
proveImplication :: Bool -> Maybe Name ->
  [TParam] -> [Prop] -> [Goal] -> InferM Subst
proveImplication dedupErrs lnam as ps gs =
  do evars <- varsWithAsmps
     solver <- getSolver

     extraAs <- (map mtpParam . Map.elems) <$> getParamTypes
     extra   <- map thing <$> getParamConstraints

     (mbErr,su) <- io (proveImplicationIO solver dedupErrs lnam evars
                            (extraAs ++ as) (extra ++ ps) gs)
     case mbErr of
       Right ws  -> mapM_ recordWarning ws
       Left errs -> mapM_ recordError errs
     return su

-- | Tries to prove an implication. If proved, then returns
-- a (possibly-empty) list of warnings raised during proving.
-- If not proved, then returns `Left errs`, which records all errors
-- raised during proving.
tryProveImplication :: 
  Maybe Name -> [TParam] -> [Prop] -> [Goal] -> InferM (Either [Error] [Warning])
tryProveImplication lnam as ps gs =
  do evars <- varsWithAsmps
     solver <- getSolver

     extraAs <- (map mtpParam . Map.elems) <$> getParamTypes
     extra   <- map thing <$> getParamConstraints

     (res,_su) <- io (proveImplicationIO solver False lnam evars
                            (extraAs ++ as) (extra ++ ps) gs)
     return res


proveImplicationIO :: Solver
                   -> Bool     -- ^ Whether to remove duplicate goals in errors
                   -> Maybe Name     -- ^ Checking this function
                   -> Set TVar -- ^ These appear in the env., and we should
                               -- not try to default them
                   -> [TParam] -- ^ Type parameters
                   -> [Prop]   -- ^ Assumed constraint
                   -> [Goal]   -- ^ Collected constraints
                   -> IO (Either [Error] [Warning], Subst)
proveImplicationIO _ _         _ _         _  []     []  = return (Right [], emptySubst)
proveImplicationIO s dedupErrs f varsInEnv ps asmps0 gs0 =
  do let ctxt = buildSolverCtxt asmps
     res <- quickSolverIO ctxt gs
     case res of
       Left erro -> return (Left [erro], emptySubst)
       Right (su,[]) -> return (Right [], su)
       Right (su,gs1) ->
         do gs2 <- proveImp s asmps gs1
            case gs2 of
              [] -> return (Right [], su)
              gs3 ->
                do let free = filter isFreeTV
                            $ Set.toList
                            $ Set.difference (fvs (map goal gs3)) varsInEnv
                   case defaultAndSimplify free gs3 of
                     (_,_,newSu,_,errs)
                        | isEmptySubst newSu ->
                                 return (Left (err gs3:errs), su) -- XXX: Old?
                     (_,newGs,newSu,ws,errs) ->
                       do let su1 = newSu @@ su
                          (res1,su2) <- proveImplicationIO s dedupErrs f varsInEnv ps
                                                 (apSubst su1 asmps0) newGs
                          let su3 = su2 @@ su1
                          case res1 of
                            Left bad -> return (Left (bad ++ errs), su3)
                            Right ws1
                              | null errs -> return (Right (ws++ws1),su3)
                              | otherwise -> return (Left errs, su3)
  where
  err us = cleanupError
           $ UnsolvedDelayedCt
           $ DelayedCt { dctSource = f
                       , dctForall = ps
                       , dctAsmps  = asmps0
                       , dctGoals  = if dedupErrs then nubOrd us else us
                       }


  asmps1 = concatMap pSplitAnd asmps0
  (asmps,gs) =
     let gs1 = [ g { goal = p } | g <- gs0, p <- pSplitAnd (goal g)
                                , notElem p asmps1 ]
     in case matchMaybe (improveProps True mempty asmps1) of
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



buildSolverCtxt :: [Prop] -> Ctxt
buildSolverCtxt ps0 =
  let ps = saturateProps mempty ps0
      ivals = assumptionIntervals mempty (Set.toList ps)
   in SolverCtxt
      { intervals = ivals
      , saturatedAsmps = ps
      }

 where
 saturateProps gs [] = gs
 saturateProps gs (p:ps)
   | Set.member p gs = saturateProps gs ps
   | Just (n,_) <- pIsLiteral p =
       let gs' = Set.fromList [p, pFin n] <> gs
        in saturateProps gs' ps
   | otherwise =
        let gs' = Set.singleton p <> superclassSet p <> gs
         in saturateProps gs' ps

 assumptionIntervals as ps =
   case computePropIntervals as ps of
     NoChange -> as
     InvalidInterval {} -> as -- XXX: say something
     NewIntervals bs -> Map.union bs as
