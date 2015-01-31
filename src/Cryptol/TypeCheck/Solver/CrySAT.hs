{-# LANGUAGE Safe #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
module Cryptol.TypeCheck.Solver.CrySAT
  ( withScope, withSolver
  , assumeProps, checkDefined, simplifyProps
  , check
  , Solver, logger
  , DefinedProp(..)
  , debugBlock
  , DebugLog(..)
  ) where

import qualified Cryptol.TypeCheck.AST as Cry
import           Cryptol.TypeCheck.PP(pp)
import           Cryptol.TypeCheck.InferTypes(Goal(..))
import qualified Cryptol.TypeCheck.Subst as Cry

import           Cryptol.TypeCheck.Solver.Numeric.AST
import           Cryptol.TypeCheck.Solver.Numeric.ImportExport
import           Cryptol.TypeCheck.Solver.Numeric.Defined
import           Cryptol.TypeCheck.Solver.Numeric.Simplify
import           Cryptol.TypeCheck.Solver.Numeric.NonLin
import           Cryptol.TypeCheck.Solver.Numeric.SMT
import           Cryptol.Utils.Panic ( panic )

import           MonadLib
import           Data.Maybe ( mapMaybe, fromMaybe )
import           Data.Map ( Map )
import qualified Data.Map as Map
import           Data.Traversable ( traverse )
import           Data.Set ( Set )
import qualified Data.Set as Set
import           Data.IORef ( IORef, newIORef, readIORef, modifyIORef',
                              atomicModifyIORef' )

import qualified SimpleSMT as SMT
import           Text.PrettyPrint(Doc)

-- | We use this to rememebr what we simplified
newtype SimpProp = SimpProp Prop

simpProp :: Prop -> SimpProp
simpProp p = SimpProp (crySimplify p)


data DefinedProp a = DefinedProp
  { dpData         :: a
  , dpSimpProp     :: SimpProp
    -- ^ Fully simplified (may have ORs)
    -- These are used in the proofs, and may not be translatable back
    -- into Cryptol.

  , dpSimpExprProp :: Prop
    -- ^ Expressions are simplified (no ORs)
    -- These should be importable back into Cryptol props.
  }

type ImpMap = Map Name Expr

{- | Check if a collection of things are defined.
It does not modify the solver's state.

The result is like this:
  * 'Nothing': The properties are inconsistent
  * 'Just' info:  The properties may be consistent, and here is some info. -}
checkDefined :: Solver                                    ->
                (Prop -> a -> a) {- ^ Update a goal -}    ->
                Set Name   {- ^ Unification variables -}  ->
                [(a,Prop)] {- ^ Goals                 -}  ->
                IO (Maybe ( [a]             -- could not prove
                          , [DefinedProp a] -- proved ok and simplified terms
                          , Subst           -- computed improvements
                          ))
checkDefined s updCt uniVars props0 = withScope s (go Map.empty [] props0)
  where
  go knownImps done notDone =
    do (newNotDone, novelDone) <- checkDefined' s updCt notDone
       (possible,  imps)       <- check s uniVars
       if not possible
         then return Nothing
         else
           do let novelImps = Map.difference imps knownImps
                  newDone   = novelDone ++ done

              if Map.null novelImps
                then return $ Just ( map fst newNotDone
                                   , newDone
                                   , knownImps
                                   )
                else
                  do mapM_ addImpProp (Map.toList novelImps)
                     -- Apply subst to knownImps?
                     let newImps    = Map.union novelImps knownImps
                         impDone    = map (updDone novelImps) newDone
                         impNotDone = map (updNotDone novelImps) newNotDone
                     go newImps impDone impNotDone

  addImpProp (x,e) = assert s (simpProp (Var x :== e))


  updDone su ct =
    case apSubst su (dpSimpExprProp ct) of
      Nothing -> ct
      Just p' ->
        let p2 = crySimpPropExpr p'
        in DefinedProp { dpData = updCt p2 (dpData ct)
                       , dpSimpExprProp = p2
                       , dpSimpProp = simpProp p2
                       }

  updNotDone su (g,p) =
    case apSubst su p of
      Nothing -> (g,p)
      Just p' -> (updCt p' g,p')


-- | Check that a bunch of constraints are all defined.
--  * We return constraints that are not necessarily defined in the first
--    component, and the ones that are defined in the second component.
--  * Well defined constraints are asserted at this point.
--  * The expressions in the defined constraints are simplified.
checkDefined' :: Solver -> (Prop -> a -> a) ->
                [(a,Prop)] -> IO ([(a,Prop)], [DefinedProp a])
checkDefined' s updCt props0 =
  do let ps = [ (a,p,simpProp (cryDefinedProp p)) | (a,p) <- props0 ]
     go False [] [] ps

  where


  -- Everything is defined: keep going.
  go _    isDef []       [] = return ([], isDef)

  -- We have possibly non-defined, but we also added a new fact: go again.
  go True isDef isNotDef [] = go False isDef [] isNotDef

  -- We have possibly non-defined predicates and nothing changed.
  go False isDef isNotDef [] = return ([ (a,p) | (a,p,_) <- isNotDef ], isDef)

  -- Process one constraint.
  go ch isDef isNotDef ((ct,p,q@(SimpProp defCt)) : more) =
    do proved <- prove s defCt
       if proved then do let r = case crySimpPropExprMaybe p of
                                   Nothing ->
                                     DefinedProp
                                        { dpData = ct
                                        , dpSimpExprProp = p
                                        , dpSimpProp = simpProp p
                                        }
                                   Just p' ->
                                     DefinedProp
                                       { dpData = updCt p' ct
                                       , dpSimpExprProp = p'
                                       , dpSimpProp = simpProp p'
                                       }
                         -- add defined prop as an assumption
                         assert s (dpSimpProp r)
                         go True (r : isDef) isNotDef  more
                 else go ch isDef ((ct,p,q) : isNotDef) more







-- | Simplify a bunch of well-defined properties.
-- Eliminates properties that are implied by the rest.
-- Does not modify the set of assumptions.
simplifyProps :: Solver -> [DefinedProp a] -> IO [a]
simplifyProps s props = withScope s (go [] props)
  where
  go survived [] = return survived

  go survived (DefinedProp { dpSimpProp = SimpProp PTrue } : more) =
                                                          go survived more

  go survived (p : more) =
    case dpSimpProp p of
      SimpProp PTrue -> go survived more
      SimpProp p' ->
        do proved <- withScope s $ do mapM_ (assert s . dpSimpProp) more
                                      prove s p'
           if proved
             then go survived more
             else do assert s (SimpProp p')
                     go (dpData p : survived) more


-- | Add the given constraints as assumptions.
-- We also assume that the constraints are well-defined.
-- Modifies the set of assumptions.
assumeProps :: Solver -> [Cry.Prop] -> IO VarMap
assumeProps s props =
  do mapM_ (assert s . simpProp) (map cryDefinedProp ps ++ ps)
     return (Map.unions varMaps)
  where (ps,varMaps) = unzip (mapMaybe exportProp props)
  -- XXX: Instead of asserting one at a time, perhaps we should
  -- assert a conjunction.  That way, we could simplify the whole thing
  -- in one go, and would avoid having to assert 'true' many times.





--------------------------------------------------------------------------------


-- | An SMT solver, and some info about declared variables.
data Solver = Solver
  { solver    :: SMT.Solver
  , declared  :: IORef VarInfo
  , logger    :: SMT.Logger
  }


-- | Keeps track of what variables we've already declared.
data VarInfo = VarInfo
  { curScope    :: Scope
  , otherScopes :: [Scope]
  } deriving Show

data Scope = Scope
  { scopeNames    :: [Name]         -- ^ Variables declared in this scope
  , scopeMarked   :: Set Name       -- ^ These are not interesting names
                                    -- (e.g., they were defined)
  , scopeNonLinS  :: NonLinS        -- ^ Info about non-linear terms
  } deriving Show

scopeEmpty :: Scope
scopeEmpty = Scope { scopeNames = []
                   , scopeMarked = Set.empty
                   , scopeNonLinS = initialNonLinS
                   }

scopeUnmarkedNames :: Scope -> [Name]
scopeUnmarkedNames Scope { .. } = filter unmarked scopeNames
  where unmarked x = not (x `Set.member` scopeMarked)

scopeElem :: Name -> Scope -> Bool
scopeElem x Scope { .. } = x `elem` scopeNames

scopeInsert :: Name -> Scope -> Scope
scopeInsert x Scope { .. } = Scope { scopeNames = x : scopeNames, .. }

scopeMark :: Name -> Scope -> Scope
scopeMark x Scope { .. } = Scope { scopeMarked = Set.insert x scopeMarked, .. }

scopeLookupNL :: Name -> Scope -> Maybe Expr
scopeLookupNL x Scope { .. } = lookupNL x scopeNonLinS

scopeSubstNL :: Subst -> Scope -> Maybe (Subst, Scope)
scopeSubstNL su Scope { .. } =
  do (lsu,newNL) <- apSubstNL su scopeNonLinS
     return (lsu, Scope { scopeNonLinS = newNL, .. })


-- | Given a *simplified* prop, separate linear and non-linear parts
-- and return the linear ones.
scopeAssert :: SimpProp -> Scope -> (SimpProp,Scope)
scopeAssert (SimpProp p) Scope { .. } =
  let (p1,s1) = nonLinProp scopeNonLinS p
  in (SimpProp p1, Scope { scopeNonLinS = s1, ..  })


-- | No scopes.
viEmpty :: VarInfo
viEmpty = VarInfo { curScope = scopeEmpty, otherScopes = [] }

-- | Check if a name is any of the scopes.
viElem :: Name -> VarInfo -> Bool
viElem x VarInfo { .. } = any (x `scopeElem`) (curScope : otherScopes)

-- | Add a name to a scope.
viInsert :: Name -> VarInfo -> VarInfo
viInsert x VarInfo { .. } = VarInfo { curScope = scopeInsert x curScope, .. }

-- | Mark a name in the current scope.
viMark :: Name -> VarInfo -> VarInfo
viMark x VarInfo { .. } = VarInfo { curScope = scopeMark x curScope, .. }

-- | Add an assertion to the current scope. Returns the lienar part.
viAssert :: SimpProp -> VarInfo -> (VarInfo, SimpProp)
viAssert p VarInfo { .. } = ( VarInfo { curScope = s1, .. }, p1)
  where (p1, s1) = scopeAssert p curScope

-- | Enter a scope.
viPush :: VarInfo -> VarInfo
viPush VarInfo { .. } =
  VarInfo { curScope = scopeEmpty { scopeNonLinS = scopeNonLinS curScope }
          , otherScopes = curScope : otherScopes
          }

-- | Exit a scope.
viPop :: VarInfo -> VarInfo
viPop VarInfo { .. } = case otherScopes of
                         c : cs -> VarInfo { curScope = c, otherScopes = cs }
                         _ -> panic "viPop" ["no more scopes"]


-- | All declared names, that have not been "marked".
-- These are the variables whose values we are interested in.
viUnmarkedNames :: VarInfo -> [ Name ]
viUnmarkedNames VarInfo { .. } = concatMap scopeUnmarkedNames
                                                    (curScope : otherScopes)

viLookupNL :: Name -> VarInfo -> Maybe Expr
viLookupNL x VarInfo { .. } = scopeLookupNL x curScope

viSubstNL :: Subst -> VarInfo -> Maybe (Subst, VarInfo)
viSubstNL su VarInfo { .. } =
  do (lsu,sc) <- scopeSubstNL su curScope
     return (lsu, VarInfo { curScope = sc, .. })


-- | Check if this is a non-linear var.  If so, returns its definition.
lookupNLVar :: Solver -> Name -> IO (Maybe Expr)
lookupNLVar Solver { .. } x = viLookupNL x `fmap` readIORef declared

-- | Mark a variable is being defined, so we don't look for further
-- improvements to it.
markDefined :: Solver -> Name -> IO ()
markDefined Solver { .. } x = modifyIORef' declared (viMark x)

-- | Apply a substituition to the non-linear assignment.
substNL :: Solver -> Subst -> IO (Maybe Subst)
substNL s@Solver { .. } su =
  do mb <- atomicModifyIORef' declared $ \vi ->
           case viSubstNL su vi of
             Nothing        -> (vi, Nothing)
             Just (lsu,vi1) -> (vi1, Just lsu)
     case mb of
       Nothing -> return Nothing
       Just lsu -> do mapM_ addFact (Map.toList lsu)
                      return (Just lsu)
  where
  addFact (x,e) = do assert s (simpProp (Var x :== e))
                     markDefined s x




-- | Execute a computation with a fresh solver instance.
withSolver :: (Solver -> IO a) -> IO a
withSolver k =
  do logger <- SMT.newLogger
     solver <- SMT.newSolver "cvc4" ["--lang=smt2", "--incremental"]
                                                   Nothing --} (Just logger)
     SMT.setLogic solver "QF_LIA"
     declared <- newIORef viEmpty
     a <- k Solver { .. }
     _ <- SMT.stop solver

     return a

-- | Execute a computation in a new solver scope.
withScope :: Solver -> IO a -> IO a
withScope Solver { .. } k =
  do SMT.push solver
     SMT.logTab logger
     modifyIORef' declared viPush
     a <- k
     modifyIORef' declared viPop
     SMT.logUntab logger
     SMT.pop solver
     return a

-- | Declare a variable.
declareVar :: Solver -> Name -> IO ()
declareVar Solver { .. } a =
  do done <- fmap (a `viElem`) (readIORef declared)
     unless done $
       do e  <- SMT.declare solver (smtName a)    SMT.tInt
          let fin_a = smtFinName a
          _  <- SMT.declare solver fin_a SMT.tBool
          SMT.assert solver (SMT.geq e (SMT.int 0))
          modifyIORef' declared (viInsert a)

-- | Add an assertion to the current context.
-- INVARIANT: Assertion is simplified.
assert :: Solver -> SimpProp -> IO ()
assert _ (SimpProp PTrue) = return ()
assert s@Solver { .. } p =
  do SimpProp p1 <- atomicModifyIORef' declared (viAssert p)
     mapM_ (declareVar s) (Set.toList (cryPropFVS p1))
     SMT.assert solver $ ifPropToSmtLib $ desugarProp p1


-- | Try to prove a property.  The result is 'True' when we are sure that
-- the property holds, and 'False' otherwise.  In other words, getting `False`
-- *does not* mean that the proposition does not hold.
prove :: Solver -> Prop -> IO Bool
prove _ PTrue = return True
prove s@(Solver { .. }) p =
  withScope s $
  do assert s (simpProp (Not p))
     res <- SMT.check solver
     case res of
       SMT.Unsat   -> return True
       SMT.Unknown -> return False  -- We are not sure
       SMT.Sat     -> return False
        -- XXX: If the answer is Sat, it is possible that this is a
        -- a fake example, as we need to evaluate the nonLinear constraints.
        -- If they are all satisfied, then we have a genuine counter example.
        -- Otherwise, we could look for another one...


{- | Check if the current set of assumptions is satisifiable, and find
some facts that must hold in any models of the current assumptions.
The 'Bool' is 'True' if the current asumptions *may be* satisifiable.
The 'Bool' is 'False' if the current assumptions are *definately*
not satisfiable. -}
check :: Solver -> Set Name -> IO (Bool, Subst)
check s@Solver { .. } uniVars =
  debugBlock s "check" $
  do res <- SMT.check solver
     case res of
       SMT.Unsat   -> return (False, Map.empty)
       SMT.Unknown -> return (True, Map.empty)
       SMT.Sat     -> debugBlock s "improvements" (getImpSubst s uniVars)

getImpSubst :: Solver -> Set Name -> IO (Bool,Subst)
getImpSubst s@Solver { .. } uniVars =
  do names <- viUnmarkedNames `fmap` readIORef declared
     m     <- fmap Map.fromList (mapM getVal names)
     model <- cryImproveModel solver uniVars m
     let imps = Map.toList (toSubst model)
     debugBlock s "before" $
        mapM_ (\(x,e) -> debugLog s (Var x :== e)) imps

     res <- mapM (checkImpBind s) imps
     let (agains,eqs) = unzip res

     debugBlock s "after" $
        mapM_ (\(x,e) -> debugLog s (Var x :== e)) (concat eqs)

     (possible,more) <- if or agains then check s uniVars
                                     else return (True,Map.empty)
     return (possible, Map.union more (Map.fromList (concat eqs)))

  where
  getVal a =
    do yes <- isInf a
       if yes then return (a, K Inf)
              else do v <- SMT.getConst solver (smtName a)
                      case v of
                        SMT.Int x | x >= 0 -> return (a, K (Nat x))
                        _ -> panic "cryCheck.getVal"
                                [ "Not a natural number", show v ]

  isInf a = do yes <- SMT.getConst solver (smtFinName a)
               case yes of
                 SMT.Bool ans -> return (not ans)
                 _            -> panic "cryCheck.isInf"
                                       [ "Not a boolean value", show yes ]




-- | Given a computed improvement `x = e`, check to see if we can get
-- some additional information by interacting with the non-linear assignment.
checkImpBind :: Solver -> (Name, Expr) -> IO (Bool, [(Name,Expr)])
checkImpBind s (x,e) =
  do mbNL <- lookupNLVar s x
     case (mbNL,e) of

       -- non-lin expression `x = e` equals constant `K`.
       --   * new constraint: e = K
       --   * su: `x = K`; eliminates `x`
       (Just nlE, K {}) ->
          do assert s (simpProp (nlE :== e))
             markDefined s x
             return (True, [(x,e)])

       (Just nlE, Var a) -> setNLVar x nlE a

       -- ordinary var, `?a`, equals constant, `K`:
       --   * su `?a = K`; eliminates `?a`
       (Nothing, K {}) -> setNormalVar x e

       -- ordinary var = some var
       (Nothing, Var a) ->
          do mbNL2 <- lookupNLVar s a
             case mbNL2 of

               -- ordinary var = ordinary var
               Nothing | SysName _ <- a ->
                         debugBlock s "sys-var with no def" $
                           do vi <- readIORef (declared s)
                              debugLog s (show vi)
                              setNormalVar x e
                       | otherwise -> setNormalVar x e

               -- ordinary var = nl var
               Just nlE -> setNLVar a nlE x

       -- ordinary var = lin rel; XXX: TODO

       _ -> return (False, [])

  where
  setNormalVar var def =
    do debugBlock s "setting-normal" (debugLog s (Var var :== def))
       let su = Map.singleton var def
       mbLins <- substNL s su
       let newLins = Map.toList (fromMaybe Map.empty mbLins)
       markDefined s var
       return (not (null newLins), (var,def) : newLins)

  -- Set a non-lin var, to another var.
  setNLVar var nlE a =
    do mbNL2 <- lookupNLVar s a
       case mbNL2 of

         -- non-lin `x = e1` equals non-lin `y = e2`
         --   * new constraint: `e1 = e2`
         --   * su: `x = y`; eliminates `x`
         Just nlE2 ->
           do assert s (simpProp (nlE :== nlE2))  -- probably useless
              markDefined s var
              return (True, [(var,Var a)])

         -- non-lin `x = e1` equals `?a`
         Nothing

           -- `?a` occurs in `e1`
           --   * do nothing; can this be useful in any way?
           | a `Set.member` cryExprFVS nlE ->
              return (False, [])

           -- `?a` does not occur in `e1`
           --   * su: `?a = e`; eliminates `?a`
           | otherwise -> setNormalVar a nlE




-- | Convert a bunch of improving equations into an idempotent substitution.
-- Assumes that the equations don't have loops.
toSubst :: ImpMap -> Subst
toSubst m =
  case normMap (apSubst m) m of
    Nothing -> m
    Just m1 -> toSubst m1


-- | Apply a function to all elements of a map.  Returns `Nothing` if nothing
-- changed, and @Just new_map@ otherwise.
normMap :: (a -> Maybe a) -> Map k a -> Maybe (Map k a)
normMap f m = mk $ runId $ runStateT False $ traverse upd m
  where
  mk (a,changes) = if changes then Just a else Nothing

  upd x = case f x of
            Just y  -> set True >> return y
            Nothing -> return x

--------------------------------------------------------------------------------

debugBlock :: Solver -> String -> IO a -> IO a
debugBlock s@Solver { .. } name m =
  do debugLog s name
     SMT.logTab logger
     a <- m
     SMT.logUntab logger
     return a

class DebugLog t where
  debugLog :: Solver -> t -> IO ()

  debugLogList :: Solver -> [t] -> IO ()
  debugLogList s ts = case ts of
                        [] -> debugLog s "(none)"
                        _  -> mapM_ (debugLog s) ts

instance DebugLog Char where
  debugLog s x     = SMT.logMessage (logger s) (show x)
  debugLogList s x = SMT.logMessage (logger s) x

instance DebugLog a => DebugLog [a] where
  debugLog = debugLogList

instance DebugLog a => DebugLog (Maybe a) where
  debugLog s x = case x of
                   Nothing -> debugLog s "(nothing)"
                   Just a  -> debugLog s a

instance DebugLog Doc where
  debugLog s x = debugLog s (show x)

instance DebugLog Cry.Type where
  debugLog s x = debugLog s (pp x)

instance DebugLog Goal where
  debugLog s x = debugLog s (goal x)

instance DebugLog Cry.Subst where
  debugLog s x = debugLog s (pp x)

instance DebugLog Prop where
  debugLog s x = debugLog s (ppProp x)



