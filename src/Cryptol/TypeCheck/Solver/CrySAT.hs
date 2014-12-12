{-# LANGUAGE Safe #-}
{-# LANGUAGE RecordWildCards #-}
module Cryptol.TypeCheck.Solver.CrySAT
  ( withScope, withSolver
  , assumeProps, checkDefined, simplifyProps
  , check
  , Solver
  ) where

import qualified Cryptol.TypeCheck.AST as Cry

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
import           Data.IORef ( IORef, newIORef, readIORef, modifyIORef' )

import           SimpleSMT ( SExpr )
import qualified SimpleSMT as SMT

type ImpMap = Map Name Expr

{- | Check if a collection of things are defined.
It does not modify the solver's state.

The result is like this:
  * 'Nothing': The properties are inconsistent
  * 'Just' info:  The properties may be consistent, and here is some info:
      * [a]:           We could not prove that these are well defineed.
      * [(a,SMTProp)]: We proved that these are well defined.
      * ImpMap:        We computed some improvements. -}
checkDefined :: Solver -> [(a,Prop)] -> IO (Maybe ([a], [(a,SMTProp)], ImpMap))
checkDefined s props0 = withScope s (go Map.empty [] props0)
  where
  go knownImps done notDone =
    do (newNotDone, novelDone) <- checkDefined' s notDone
       (possible,  imps)       <- check s
       if not possible
         then return Nothing
         else
           do let novelImps = Map.difference imps knownImps
                  newDone   = novelDone ++ done

              if Map.null novelImps
                then return $ Just ( map fst newNotDone
                                   , [ (x,p) | (x,_,p) <- newDone ]
                                   , knownImps)
                else
                  do mapM_ addImpProp (Map.toList novelImps)
                     let newImps    = Map.union newImps knownImps
                         impDone    = map (updProp novelImps) newDone
                         impNotDone = [ (a, fromMaybe p (apSubst novelImps p)) |
                                                        (a,p) <- newNotDone ]
                     go newImps impDone impNotDone

  addImpProp (x,e) = assert s (prepareProp (Var x :== e))
  updProp su (a,origProp,smtProp) =
    case apSubst su origProp of
      Nothing -> (a,origProp,smtProp)
      Just p1 -> (a,p1,prepareProp p1)


-- | Check that a bunch of constraints are all defined.
-- We return constraints that are not necessarily defined in the first
-- component, and the ones that are defined in the second component.
-- Well defined constraints are asserted at this point.
checkDefined' :: Solver -> [(a,Prop)] -> IO ([(a,Prop)], [(a,Prop,SMTProp)])
checkDefined' s props0 =
  go False [] [] [ (a, p, prepareProp (cryDefinedProp p)) | (a,p) <- props0 ]

  where
  -- Everything is defined: keep going.
  go _    isDef []       [] = return ([], isDef)

  -- We have possibly non-defined, but we also added a new fact: go again.
  go True isDef isNotDef [] = go False isDef [] isNotDef

  -- We have possibly non-defined predicates and nothing changed.
  go False isDef isNotDef [] = return ([ (a,p) | (a,p,_) <- isNotDef ], isDef)

  -- Process one constraint.
  go ch isDef isNotDef ((ct,p,q) : more) =
    do proved <- prove s q
       if proved then do let r = prepareProp p
                         assert s r -- add defined prop as an assumption
                         go True ((ct,p,r) : isDef) isNotDef  more
                 else go ch isDef ((ct,p,q) : isNotDef) more








-- | Simplify a bunch of well-defined properties.
-- Eliminates properties that are implied by the rest.
-- Does not modify the set of assumptions.
simplifyProps :: Solver -> [(a,SMTProp)] -> IO [a]
simplifyProps s props = withScope s (go [] props)
  where
  go survived [] = return survived
  go survived ((ct,p) : more) =
    do proved <- withScope s $ do mapM_ (assert s . snd) more
                                  prove s p
       if proved
         then go survived more
         else do assert s p
                 go (ct : survived) more


-- | Add the given constraints as assumptions.
-- We also assume that the constraints are well-defined.
-- Modifies the set of assumptions.
assumeProps :: Solver -> [Cry.Prop] -> IO VarMap
assumeProps s props =
  do mapM_ (assert s . prepareProp) (map cryDefinedProp ps ++ ps)
     return (Map.unions varMaps)
  where (ps,varMaps) = unzip (mapMaybe exportProp props)
  -- XXX: Instead of asserting one at a time, perhaps we should
  -- assert a conjunction.  That way, we could simplify the whole thing
  -- in one go, and would avoid having to assert 'true' many times.





--------------------------------------------------------------------------------

data SMTProp = SMTProp
  { smtpVars        :: Set Name
    -- ^ Theses vars include vars in the linear part,
    -- as well as variables in the 'fst' of the non-linear part.
  , smtpLinPart     :: SExpr
  , smtpNonLinPart  :: [(Name,Expr)]
    -- ^ The names are all distinct, and don't appear in the the defs.
  }

-- | Prepare a property for export to an SMT solver.
prepareProp :: Prop -> SMTProp
prepareProp prop0 = SMTProp
  { smtpVars       = cryPropFVS linProp
  , smtpLinPart    = ifPropToSmtLib (desugarProp linProp)
  , smtpNonLinPart = nonLinEs
  }
  where
  prop1               = crySimplify prop0
  (nonLinEs, linProp) = nonLinProp prop1



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
  }

data Scope = Scope
  { scopeNames    :: [Name]         -- ^ Variables declared in this scope
  , scopeAsmps    :: [(Name,Expr)]  -- ^ Non-linear assumptions.
  }

scopeEmpty :: Scope
scopeEmpty = Scope { scopeNames = [], scopeAsmps = [] }

scopeElem :: Name -> Scope -> Bool
scopeElem x Scope { .. } = x `elem` scopeNames

scopeInsert :: Name -> Scope -> Scope
scopeInsert x Scope { .. } = Scope { scopeNames = x : scopeNames, .. }

scopeAssert :: [(Name,Expr)] -> Scope -> Scope
scopeAssert as Scope { .. } = Scope { scopeAsmps = as ++ scopeAsmps, .. }


-- | No scopes.
viEmpty :: VarInfo
viEmpty = VarInfo { curScope = scopeEmpty, otherScopes = [] }

-- | Check if a name is any of the scopes.
viElem :: Name -> VarInfo -> Bool
viElem x VarInfo { .. } = any (x `scopeElem`) (curScope : otherScopes)

-- | Add a name to a scope.
viInsert :: Name -> VarInfo -> VarInfo
viInsert x VarInfo { .. } = VarInfo { curScope = scopeInsert x curScope, .. }

-- | Add some non-linear assertions to the current scope.
viAssert :: [(Name,Expr)] -> VarInfo -> VarInfo
viAssert as VarInfo { .. } = VarInfo { curScope = scopeAssert as curScope, .. }

-- | Enter a scope.
viPush :: VarInfo -> VarInfo
viPush VarInfo { .. } = VarInfo { curScope = scopeEmpty
                                , otherScopes = curScope : otherScopes }

-- | Exit a scope.
viPop :: VarInfo -> VarInfo
viPop VarInfo { .. } = case otherScopes of
                         c : cs -> VarInfo { curScope = c, otherScopes = cs }
                         _ -> panic "viPop" ["no more scopes"]

-- | All declared names
viNames :: VarInfo -> [ Name ]
viNames VarInfo { .. } = concatMap scopeNames (curScope : otherScopes)

-- | Execute a computation with a fresh solver instance.
withSolver :: (Solver -> IO a) -> IO a
withSolver k =
  do logger <- SMT.newLogger
     solver <- SMT.newSolver "cvc4" ["--lang=smt2", "--incremental"]
                                                   Nothing {-(Just logger)-}
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
          _  <- SMT.declare solver (smtFinName a) SMT.tBool
          SMT.assert solver(SMT.geq e (SMT.int 0))
          modifyIORef' declared (viInsert a)

-- | Add an assertion to the current context.
assert :: Solver -> SMTProp -> IO ()
assert s@Solver { .. } SMTProp { .. } =
  do mapM_ (declareVar s) (Set.toList smtpVars)
     SMT.assert solver smtpLinPart
     modifyIORef' declared (viAssert smtpNonLinPart)


-- | Try to prove a property.  The result is 'True' when we are sure that
-- the property holds, and 'False' otherwise.  In other words, getting `False`
-- *does not* mean that the proposition does not hold.
prove :: Solver -> SMTProp -> IO Bool
prove s@(Solver { .. }) SMTProp { .. } =
  withScope s $
  do mapM_ (declareVar s) (Set.toList smtpVars)
     SMT.assert solver (SMT.not smtpLinPart)
     res <- SMT.check solver
     case res of
       SMT.Unsat   -> return True
       SMT.Unknown -> return False  -- We are not sure
       SMT.Sat     -> return False
        -- XXX: If the answer is Sat, it is possible that this is a
        -- a fake example, as we need to evaluate the nonLinear constraints.
        -- If they are all satisfied, then we have a genuine counter example.
        -- Otherwise, we could look for another one...


-- | Check if the current set of assumptions is satisifiable, and find
-- some facts that must hold in any models of the current assumptions.
-- The 'Bool' is 'True' if the current asumptions *may be* satisifiable.
-- The 'Bool' is 'False' if the current assumptions are *definately*
-- not satisfiable.
check :: Solver -> IO (Bool, ImpMap)
check Solver { .. } =
  do res <- SMT.check solver
     case res of
       SMT.Unsat   -> return (False, Map.empty)
       SMT.Unknown -> return (True, Map.empty)
       SMT.Sat     ->
         do names <- viNames `fmap` readIORef declared
            m     <- fmap Map.fromList (mapM getVal names)
            imps  <- toSubst `fmap` cryImproveModel solver m

            -- XXX: Here we should apply the imps to the non-linear things
            -- and evalute. If this results in a contradiction, than we
            -- know that current assumptions are definately not satisfiable
            -- because the `imps` must hold in any model of the linear part.
            -- Also, some of the non-linear things may become linear,
            -- so we could get further improvements.

            -- For now, we just return the improvements, with the idea
            -- that they are sent outside of CrySat (e.g., they might enable
            -- some class constraints to be solved), the idea being that
            -- we'd apply the substitution and start over.

            return (True, imps)


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


-- | Convert a bunch of improving equations into an idempotent substitution.
-- Assumes that the equations don't have loops.
toSubst :: ImpMap -> ImpMap
toSubst m =
  case normMap (apSubst m) m of
    Nothing -> m
    Just m1 -> toSubst m1


-- | Apply a function to all elements of a map.  Returns `Nothing` if nothing
-- changed, and @Just newmap@ otherwise.
normMap :: (a -> Maybe a) -> Map k a -> Maybe (Map k a)
normMap f m = mk $ runId $ runStateT False $ traverse upd m
  where
  mk (a,changes) = if changes then Just a else Nothing

  upd x = case f x of
            Just y  -> set True >> return y
            Nothing -> return x




