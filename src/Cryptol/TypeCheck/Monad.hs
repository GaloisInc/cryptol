-- |
-- Module      :  Cryptol.TypeCheck.Monad
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BlockArguments #-}
module Cryptol.TypeCheck.Monad
  ( module Cryptol.TypeCheck.Monad
  , module Cryptol.TypeCheck.InferTypes
  ) where

import qualified Control.Applicative as A
import qualified Control.Monad.Fail as Fail
import           Control.Monad.Fix(MonadFix(..))
import           Data.Text(Text)
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Data.Map (Map)
import           Data.Set (Set)
import           Data.List(find, foldl')
import           Data.List.NonEmpty(NonEmpty((:|)))
import           Data.Semigroup(sconcat)
import           Data.Maybe(mapMaybe,fromMaybe)
import           Data.IORef

import           GHC.Generics (Generic)
import           Control.DeepSeq

import           MonadLib hiding (mapM)

import           Cryptol.ModuleSystem.Name
                    (FreshM(..),Supply,mkLocal,asLocal
                    , nameInfo, NameInfo(..),nameTopModule)
import           Cryptol.ModuleSystem.NamingEnv.Types
import qualified Cryptol.ModuleSystem.Interface as If
import           Cryptol.Parser.Position
import qualified Cryptol.Parser.AST as P
import           Cryptol.TypeCheck.AST
import           Cryptol.TypeCheck.Subst
import           Cryptol.TypeCheck.Interface(genIfaceWithNames,genIfaceNames)
import           Cryptol.TypeCheck.Unify(doMGU, runResult, UnificationError(..)
                                        , Path, rootPath)
import           Cryptol.TypeCheck.InferTypes
import           Cryptol.TypeCheck.Error( Warning(..),Error(..)
                                        , cleanupErrors, computeFreeVarNames, cleanupWarnings
                                        )
import qualified Cryptol.TypeCheck.SimpleSolver as Simple
import qualified Cryptol.TypeCheck.Solver.SMT as SMT
import           Cryptol.TypeCheck.PP(NameMap, defaultPPCfg)
import           Cryptol.Utils.PP(pp, (<+>), text,commaSep,brackets,debugShowUniques)
import           Cryptol.Utils.Ident(Ident,Namespace(..),ModName)
import           Cryptol.Utils.Panic(panic)
import Cryptol.Parser.Name (NameSource(SystemName))

-- | Information needed for type inference.
data InferInput = InferInput
  { inpRange     :: Range             -- ^ Location of program source
  , inpVars      :: Map Name Schema   -- ^ Variables that are in scope
  , inpTSyns     :: Map Name TySyn    -- ^ Type synonyms that are in scope
  , inpNominalTypes :: Map Name NominalType -- ^ Nominal types in scope
  , inpSignatures :: !(Map Name ModParamNames)  -- ^ Signatures in scope

  , inpTopModules    :: ModName -> Maybe (ModuleG (), If.IfaceG ())
  , inpTopSignatures :: ModName -> Maybe ModParamNames

    -- When typechecking a module these start off empty.
    -- We need them when type-checking an expression at the command
    -- line, for example.
  , inpParams :: !ModParamNames

  , inpNameSeeds :: NameSeeds         -- ^ Private state of type-checker
  , inpMonoBinds :: Bool              -- ^ Should local bindings without
                                      --   signatures be monomorphized?

  , inpCallStacks :: Bool             -- ^ Are we tracking call stacks?

  , inpSearchPath :: [FilePath]
    -- ^ Where to look for Cryptol theory file.

  , inpPrimNames :: !PrimMap
    -- ^ This is used when the type-checker needs to refer to a predefined
    -- identifier (e.g., @number@).

  , inpSupply :: !Supply              -- ^ The supply for fresh name generation

  , inpSolver :: SMT.Solver           -- ^ Solver connection for typechecking
  }

-- | This is used for generating various names.
data NameSeeds = NameSeeds
  { seedTVar    :: !Int
  , seedGoal    :: !Int
  } deriving (Show, Generic, NFData)

-- | The initial seeds, used when checking a fresh program.
-- XXX: why does this start at 10?
nameSeeds :: NameSeeds
nameSeeds = NameSeeds { seedTVar = 10, seedGoal = 0 }


-- | The results of type inference.
data InferOutput a
  = InferFailed NameMap [(Range,Warning)] [(Range,Error)]
    -- ^ We found some errors

  | InferOK NameMap [(Range,Warning)] NameSeeds Supply a
    -- ^ Type inference was successful.


    deriving Show

bumpCounter :: InferM ()
bumpCounter = do RO { .. } <- IM ask
                 io $ modifyIORef' iSolveCounter (+1)

runInferM :: TVars a => InferInput -> InferM a -> IO (InferOutput a)
runInferM info m0 =
  do let IM m = selectorScope m0
     counter <- newIORef 0
     let allPs = inpParams info

     let env = Map.map ExtVar (inpVars info)
            <> Map.fromList
              [ (c, ExtVar t)
              | nt <- Map.elems (inpNominalTypes info)
              , (c,t) <- nominalTypeConTypes nt
              ]
            <> Map.map (ExtVar . mvpType) (mpnFuns allPs)

     let ro =         RO { iRange     = inpRange info
                         , iVars      = env
                         , iExtModules = inpTopModules info
                         , iExtSignatures = inpTopSignatures info
                         , iExtScope = (emptyModule ExternalScope)
                             { mTySyns           = inpTSyns info <>
                                                   mpnTySyn allPs
                             , mNominalTypes     = inpNominalTypes info
                             , mParamTypes       = mpnTypes allPs
                             , mParamFuns        = mpnFuns  allPs
                             , mParamConstraints = mpnConstraints allPs
                             , mSignatures       = inpSignatures info
                             }

                         , iTVars         = []
                         , iSolvedHasLazy = Map.empty
                         , iMonoBinds     = inpMonoBinds info
                         , iCallStacks    = inpCallStacks info
                         , iSolver        = inpSolver info
                         , iPrimNames     = inpPrimNames info
                         , iSolveCounter  = counter
                         }

     mb <- runExceptionT (runStateT rw (runReaderT ro m))
     case mb of
       Left errs -> inferFailed [] errs
       Right (result, finalRW) ->
         do let theSu    = iSubst finalRW
                defSu    = defaultingSubst theSu
                warns    = fmap' (fmap' (apSubst theSu)) (iWarnings finalRW)

            case iErrors finalRW of
              [] ->
                case iCts finalRW of
                  cts
                    | nullGoals cts -> inferOk warns
                                         (iNameSeeds finalRW)
                                         (iSupply finalRW)
                                         (apSubst defSu result)
                  cts ->
                     inferFailed warns
                       [ ( goalRange g
                         , UnsolvedGoals [apSubst theSu g]
                         ) | g <- fromGoals cts
                       ]

              errs -> inferFailed warns [(r,apSubst theSu e) | (r,e) <- errs]

  where
  ppcfg = defaultPPCfg
  -- XXX: perhaps this should be a part of the input?
  -- We use it when picking how to display names; we need to pick names
  -- for things that don't have their own, and we need to pick names that
  -- don't clash with existing ones.   This is affected by how things are
  -- pretty printed.

  inferOk ws a b c  = 
    let ws1 = cleanupWarnings ws
    in pure (InferOK (computeFreeVarNames ppcfg ws1 []) ws1 a b c)
  inferFailed ws es =
    let es1 = cleanupErrors es
        ws1 = cleanupWarnings ws
    in pure (InferFailed (computeFreeVarNames ppcfg ws1 es1) ws1 es1)


  rw = RW { iErrors     = []
          , iWarnings   = []
          , iSubst      = emptySubst
          , iExistTVars = []

          , iNameSeeds  = inpNameSeeds info

          , iCts        = emptyGoals
          , iHasCts     = []
          , iSolvedHas  = Map.empty

          , iSupply     = inpSupply info

          , iScope      = []
          , iBindTypes  = mempty
          }

{- | This introduces a new "selector scope" which is currently a module.
I think that it might be possible to have selectors scopes be groups
of recursive declarations instead, as we are not going to learn anything
additional once we are done with the recursive group that generated
the selectors constraints.   We do it at the module level because this
allows us to report more errors at once.

A selector scope does the following:
  * Keep track of the Has constraints generated in this scope
  * Keep track of the solutions for discharged selector constraints:
    - this uses a laziness trick where we build up a map containing the
      solutions for the Has constraints in the state
    - the *final* value for this map (i.e., at the value the end of the scope)
      is passed in as thunk in the reader component of the moment
    - as we type check expressions when we need the solution for a Has
      constraint we look it up from the reader environment; note that
      since the map is not yet built up we just get back a thunk, so we have
      to be carefule to not force it until *after* we've solved the goals
    - all of this happens in the `rec` block below
  * At the end of a selector scope we make sure that all Has constraints were
    discharged.  If not, we *abort* further type checking.  The reason for
    aborting rather than just recording an error is that the expression
    which produce contains thunks that will lead to non-termination if forced,
    and some type-checking operations (e.g., instantiation a functor)
    require us to traverse the expressions.
-}
selectorScope :: InferM a -> InferM a
selectorScope (IM m1) = IM
  do ro <- ask
     rw <- get
     mb <- inBase
           do rec let ro1 = ro { iSolvedHasLazy = solved }
                      rw1 = rw { iHasCts = [] : iHasCts rw }
                  mb <- runExceptionT (runStateT rw1 (runReaderT ro1 m1))
                  let solved = case mb of
                                 Left {} -> Map.empty
                                 Right (_,rw2) -> iSolvedHas rw2
              pure mb
     case mb of
       Left err      -> raise err
       Right (a,rw1) ->
         case iHasCts rw1 of
           us : cs ->
             do let errs = [ (goalRange g, UnsolvedGoals [g])
                           | g <- map hasGoal us ]
                set rw1 { iErrors = errs ++ iErrors rw1, iHasCts = cs }
                unIM (abortIfErrors)
                pure a
           [] -> panic "selectorScope" ["No selector scope"]



newtype InferM a = IM { unIM :: ReaderT RO
                              ( StateT  RW
                              ( ExceptionT [(Range,Error)]
                                IO
                              )) a }


data ScopeName = ExternalScope
               | LocalScope
               | SubModule Name
               | SignatureScope Name (Maybe Text) -- ^ The Text is docs
               | TopSignatureScope P.ModName
               | MTopModule P.ModName

-- | Read-only component of the monad.
data RO = RO
  { iRange    :: Range       -- ^ Source code being analysed
  , iVars     :: Map Name VarType
    -- ^ Type of variable that are in scope
    -- These are only parameters vars that are in recursive component we
    -- are checking at the moment.  If a var is not there, keep looking in
    -- the 'iScope'


  , iTVars    :: [TParam]    -- ^ Type variable that are in scope

  , iExtModules :: ModName -> Maybe (ModuleG (), If.IfaceG ())
    -- ^ An exteral top-level module.
    -- We need the actual module when we instantiate functors,
    -- because currently the type-checker desugars such modules.

  , iExtSignatures :: ModName -> Maybe ModParamNames
    -- ^ External top-level signatures.

  , iExtScope :: ModuleG ScopeName
    -- ^ These are things we know about, but are not part of the
    -- modules we are currently constructing.
    -- XXX: this sould probably be an interface
    -- NOTE: External functors should be looked up in `iExtModules`
    -- and not here, as they may be top-level modules.

  , iSolvedHasLazy :: Map Int HasGoalSln
    -- ^ NOTE: This field is lazy in an important way!  It is the
    -- final version of 'iSolvedHas' in 'RW', and the two are tied
    -- together through recursion.  The field is here so that we can
    -- look thing up before they are defined, which is OK because we
    -- don't need to know the results until everything is done.

  , iMonoBinds :: Bool
    -- ^ When this flag is set to true, bindings that lack signatures
    -- in where-blocks will never be generalized. Bindings with type
    -- signatures, and all bindings at top level are unaffected.

  , iCallStacks :: Bool
    -- ^ When this flag is true, retain source location information
    --   in typechecked terms

  , iSolver :: SMT.Solver

  , iPrimNames :: !PrimMap

  , iSolveCounter :: !(IORef Int)
  }

-- | Read-write component of the monad.
data RW = RW
  { iErrors   :: ![(Range,Error)]       -- ^ Collected errors
  , iWarnings :: ![(Range,Warning)]     -- ^ Collected warnings
  , iSubst    :: !Subst                 -- ^ Accumulated substitution

  , iExistTVars  :: [Map Name Type]
    -- ^ These keeps track of what existential type variables are available.
    -- When we start checking a function, we push a new scope for
    -- its arguments, and we pop it when we are done checking the function
    -- body. The front element of the list is the current scope, which is
    -- the only thing that will be modified, as follows.  When we encounter
    -- a existential type variable:
    --     1. we look in all scopes to see if it is already defined.
    --     2. if it was not defined, we create a fresh type variable,
    --        and we add it to the current scope.
    --     3. it is an error if we encounter an existential variable but we
    --        have no current scope.

  , iSolvedHas :: Map Int HasGoalSln
    -- ^ Selector constraints that have been solved (ref. iSolvedSelectorsLazy)

  -- Generating names
  , iNameSeeds :: !NameSeeds

  -- Constraints that need solving
  , iCts      :: !Goals                -- ^ Ordinary constraints
  , iHasCts   :: ![[HasGoal]]
    {- ^ Tuple/record projection constraints.  These are separate from
       the other constraints because solving them results in actual elaboration
       of the term, indicating how to do the projection.  The modification
       of the term is done using lazyness, by looking up a thunk ahead of time
       (@iSolvedHasLazy@ in RO), which is filled in when the constrait is
       solved (@iSolvedHas@).  See also `selectorScope`.
    -}

  , iScope :: ![ModuleG ScopeName]
    -- ^ Nested scopes we are currently checking, most nested first.
    -- These are basically partially built modules.

  , iBindTypes :: !(Map Name Schema)
    -- ^ Types of variables that we know about.  We don't worry about scoping
    -- here because we assume the bindings all have different names.

  , iSupply :: !Supply
  }


instance Functor InferM where
  fmap f (IM m) = IM (fmap f m)

instance A.Applicative InferM where
  pure x = IM (pure x)
  (<*>) = ap

instance Monad InferM where
  return        = pure
  IM m >>= f    = IM (m >>= unIM . f)

instance Fail.MonadFail InferM where
  fail x        = IM (fail x)

instance MonadFix InferM where
  mfix f        = IM (mfix (unIM . f))

instance FreshM InferM where
  liftSupply f = IM $
    do rw <- get
       let (a,s') = f (iSupply rw)
       set rw { iSupply = s' }
       return a


io :: IO a -> InferM a
io m = IM $ inBase m


-- | The monadic computation is about the given range of source code.
-- This is useful for error reporting.
inRange :: Range -> InferM a -> InferM a
inRange r (IM m) = IM $ mapReader (\ro -> ro { iRange = r }) m

inRangeMb :: Maybe Range -> InferM a -> InferM a
inRangeMb Nothing m  = m
inRangeMb (Just r) m = inRange r m

-- | This is the current range that we are working on.
curRange :: InferM Range
curRange = IM $ asks iRange

-- | Report an error.
recordError :: Error -> InferM ()
recordError = recordErrorLoc Nothing

-- | Report an error.
recordErrorLoc :: Maybe Range -> Error -> InferM ()
recordErrorLoc rng e =
  do r' <- curRange
     r <- case rng of
            Just r | rangeWithin r' r -> pure r'
            Just r  -> pure r
            Nothing -> case e of
                         AmbiguousSize d _ -> return (tvarSource d)
                         _                 -> curRange
     IM $ sets_ $ \s -> s { iErrors = (r,e) : iErrors s }


-- | If there are any recoded errors than abort firther type-checking.
abortIfErrors :: InferM ()
abortIfErrors =
  do rw <- IM get
     case iErrors rw of
       [] -> pure ()
       es ->
         do es1 <- forM es \(l,e) ->
                      do e1 <- applySubst e
                         pure (l,e1)
            IM (raise es1)

recordWarning :: Warning -> InferM ()
recordWarning w =
  unless ignore $
  do r <- case w of
            DefaultingTo d _ -> return (tvarSource d)
            _ -> curRange
     IM $ sets_ $ \s -> s { iWarnings = (r,w) : iWarnings s }
  where
  ignore
    | DefaultingTo d _ <- w
    , Just n <- tvSourceName (tvarDesc d)
    , GlobalName SystemName _ <- nameInfo n
      = True
    | otherwise = False

getSolver :: InferM SMT.Solver
getSolver =
  do RO { .. } <- IM ask
     return iSolver

-- | Retrieve the mapping between identifiers and declarations in the prelude.
getPrimMap :: InferM PrimMap
getPrimMap  =
  do RO { .. } <- IM ask
     return iPrimNames


--------------------------------------------------------------------------------
newGoal :: ConstraintSource -> Prop -> InferM Goal
newGoal goalSource goal =
  do goalRange <- curRange
     return Goal { .. }

-- | Record some constraints that need to be solved.
-- The string explains where the constraints came from.
newGoals :: ConstraintSource -> [Prop] -> InferM ()
newGoals src ps = addGoals =<< mapM (newGoal src) ps

{- | The constraints are removed, and returned to the caller.
The substitution IS applied to them. -}
getGoals :: InferM [Goal]
getGoals =
  do goals <- applySubst =<<
                  IM (sets $ \s -> (iCts s, s { iCts = emptyGoals }))
     return (fromGoals goals)

-- | Add a bunch of goals that need solving.
addGoals :: [Goal] -> InferM ()
addGoals gs0 = doAdd =<< simpGoals gs0
  where
  doAdd [] = return ()
  doAdd gs = IM $ sets_ $ \s -> s { iCts = foldl' (flip insertGoal) (iCts s) gs }


-- | Collect the goals emitted by the given sub-computation.
-- Does not emit any new goals.
collectGoals :: InferM a -> InferM (a, [Goal])
collectGoals m =
  do origGs <- applySubst =<< getGoals'
     a      <- m
     newGs  <- getGoals
     setGoals' origGs
     return (a, newGs)

  where

  -- retrieve the type map only
  getGoals'    = IM $ sets $ \ RW { .. } -> (iCts, RW { iCts = emptyGoals, .. })

  -- set the type map directly
  setGoals' gs = IM $ sets $ \ RW { .. } -> ((),   RW { iCts = gs, .. })

simpGoal :: Goal -> InferM [Goal]
simpGoal g =
  case Simple.simplify mempty (goal g) of
    p | Just t <- tIsError p ->
        do recordError $ UnsolvableGoals [g { goal = t }]
           return []
      | ps <- pSplitAnd p -> return [ g { goal = pr } | pr <- ps ]

simpGoals :: [Goal] -> InferM [Goal]
simpGoals gs = concat <$> mapM simpGoal gs



{- | Record a constraint that when we select from the first type,
we should get a value of the second type.
The returned function should be used to wrap the expression from
which we are selecting (i.e., the record or tuple).  Plese note
that the resulting expression should not be forced before the
constraint is solved.
-}
newHasGoal :: P.Selector -> Type -> Type -> InferM HasGoalSln
newHasGoal l ty f =
  do goalName <- newGoalName
     g        <- newGoal CtSelector (pHas l ty f)
     IM $ sets_ \s -> case iHasCts s of
                        cs : more ->
                          s { iHasCts = (HasGoal goalName g : cs) : more }
                        [] -> panic "newHasGoal" ["no selector scope"]
     solns    <- IM $ fmap iSolvedHasLazy ask
     return $ case Map.lookup goalName solns of
                Just e1 -> e1
                Nothing -> panic "newHasGoal" ["Unsolved has goal in result"]


-- | Add a previously generated @Has@ constraint
addHasGoal :: HasGoal -> InferM ()
addHasGoal g = IM $ sets_ \s -> case iHasCts s of
                                  cs : more -> s { iHasCts = (g : cs) : more }
                                  [] -> panic "addHasGoal" ["No selector scope"]

-- | Get the @Has@ constraints.  Each of this should either be solved,
-- or added back using 'addHasGoal'.
getHasGoals :: InferM [HasGoal]
getHasGoals =
  do gs <- IM $ sets \s -> case iHasCts s of
                             cs : more -> (cs, s { iHasCts = [] : more })
                             [] -> panic "getHasGoals" ["No selector scope"]
     applySubst gs

-- | Specify the solution (@Expr -> Expr@) for the given constraint ('Int').
solveHasGoal :: Int -> HasGoalSln -> InferM ()
solveHasGoal n e =
  IM $ sets_ $ \s -> s { iSolvedHas = Map.insert n e (iSolvedHas s) }


--------------------------------------------------------------------------------

-- | Generate a fresh variable name to be used in a local binding.
newLocalName :: Namespace -> Ident -> InferM Name
newLocalName ns x =
  do r <- curRange
     liftSupply (mkLocal SystemName ns x r)

newName :: (NameSeeds -> (a , NameSeeds)) -> InferM a
newName upd = IM $ sets $ \s -> let (x,seeds) = upd (iNameSeeds s)
                                in (x, s { iNameSeeds = seeds })


-- | Generate a new name for a goal.
newGoalName :: InferM Int
newGoalName = newName $ \s -> let x = seedGoal s
                              in (x, s { seedGoal = x + 1})

-- | Generate a new free type variable.
newTVar :: TypeSource -> Kind -> InferM TVar
newTVar src k = newTVar' src Set.empty k

-- | Generate a new free type variable that depends on these additional
-- type parameters.
newTVar' :: TypeSource -> Set TParam -> Kind -> InferM TVar
newTVar' src extraBound k =
  do r <- curRange
     bound <- getBoundInScope
     let vs = Set.union extraBound bound
         msg = TVarInfo { tvarDesc = src, tvarSource = r }
     newName $ \s -> let x = seedTVar s
                     in (TVFree x k vs msg, s { seedTVar = x + 1 })


-- | Check that the given "flavor" of parameter is allowed to
--   have the given type, and raise an error if not
checkParamKind :: TParam -> TPFlavor -> Kind -> InferM ()

checkParamKind tp flav k =
    case flav of
      TPModParam _     -> starOrHash
      TPPropSynParam _ -> starOrHashOrProp
      TPTySynParam _   -> starOrHash
      TPSchemaParam _  -> starOrHash
      TPNominalParam _ -> starOrHash
      TPPrimParam _    -> starOrHash
      TPUnifyVar       -> starOrHash

  where
    starOrHashOrProp =
      case k of
        KNum  -> return ()
        KType -> return ()
        KProp -> return ()
        _ -> recordError (BadParameterKind tp k [KNum, KType, KProp])

    starOrHash =
      case k of
        KNum  -> return ()
        KType -> return ()
        _ -> recordError (BadParameterKind tp k [KNum,KType])

-- | Generate a new free type variable.
newTParam :: P.TParam Name -> TPFlavor -> Kind -> InferM TParam
newTParam nm flav k =
  do let desc = TVarInfo { tvarDesc = TVFromSignature (P.tpName nm)
                         , tvarSource = fromMaybe emptyRange (P.tpRange nm)
                         }
     tp <- newName $ \s ->
             let x = seedTVar s
             in (TParam { tpUnique = x
                        , tpKind   = k
                        , tpFlav   = flav
                        , tpInfo   = desc
                        }
                , s { seedTVar = x + 1 })

     checkParamKind tp flav k
     return tp

-- | Generate a new version of a type parameter.  We use this when
-- instantiating module parameters (the "backtick" imports)
freshTParam :: (Name -> TPFlavor) -> TParam -> InferM TParam
freshTParam mkF tp = newName \s ->
  let u = seedTVar s
  in ( tp { tpUnique = u
          , tpFlav   = case tpName tp of
                         Just n -> mkF (asLocal NSType n)
                         Nothing -> tpFlav tp -- shouldn't happen?
          }
     , s  { seedTVar = u + 1 }
     )


-- | Generate an unknown type.  The doc is a note about what is this type about.
newType :: TypeSource -> Kind -> InferM Type
newType src k = TVar `fmap` newTVar src k



--------------------------------------------------------------------------------


-- | Record that the two types should be syntactically equal.
unify :: TypeWithSource -> Type -> InferM [Prop]
unify (WithSource t1 src rng) t2 =
  do t1' <- applySubst t1
     t2' <- applySubst t2
     let ((su1, ps), errs) = runResult (doMGU t1' t2')
     extendSubst su1
     let toError :: (Path,UnificationError) -> Error
         toError (pa,err) =
           case err of
             UniTypeLenMismatch _ _ -> TypeMismatch src rootPath t1' t2'
             UniTypeMismatch s1 s2  -> TypeMismatch src pa s1 s2
             UniKindMismatch k1 k2  -> KindMismatch (Just src) k1 k2
             UniRecursive x t       -> RecursiveType src pa (TVar x) t
             UniNonPolyDepends x vs -> TypeVariableEscaped src pa (TVar x) vs
             UniNonPoly x t         -> NotForAll src pa x t
     case errs of
       [] -> return ps
       _  -> do mapM_ (recordErrorLoc rng . toError) errs
                return []

-- | Apply the accumulated substitution to something with free type variables.
applySubst :: TVars t => t -> InferM t
applySubst t =
  do su <- getSubst
     return (apSubst su t)

applySubstPreds :: [Prop] -> InferM [Prop]
applySubstPreds ps =
  do ps1 <- applySubst ps
     return (concatMap pSplitAnd ps1)


applySubstGoals :: [Goal] -> InferM [Goal]
applySubstGoals gs =
  do gs1 <- applySubst gs
     return [ g { goal = p } | g <- gs1, p <- pSplitAnd (goal g) ]

-- | Get the substitution that we have accumulated so far.
getSubst :: InferM Subst
getSubst = IM $ fmap iSubst get

-- | Add to the accumulated substitution, checking that the datatype
-- invariant for 'Subst' is maintained.
extendSubst :: Subst -> InferM ()
extendSubst su =
  do mapM_ check (substToList su)
     IM $ sets_ $ \s -> s { iSubst = su @@ iSubst s }
  where
    check :: (TVar, Type) -> InferM ()
    check (v, ty) =
      case v of
        TVBound _ ->
          panic "Cryptol.TypeCheck.Monad.extendSubst"
            [ "Substitution instantiates bound variable:"
            , "Variable: " ++ show (pp v)
            , "Type:     " ++ show (pp ty)
            ]
        TVFree _ _ tvs _ ->
          do let escaped = Set.difference (freeParams ty) tvs
             if Set.null escaped then return () else
               panic "Cryptol.TypeCheck.Monad.extendSubst"
                 [ "Escaped quantified variables:"
                 , "Substitution:  " ++ show (pp v <+> text ":=" <+> pp ty)
                 , "Vars in scope: " ++ show (brackets (commaSep (map pp (Set.toList tvs))))
                 , "Escaped:       " ++ show (brackets (commaSep (map pp (Set.toList escaped))))
                 ]


-- | Variables that are either mentioned in the environment or in
-- a selector constraint.
varsWithAsmps :: InferM (Set TVar)
varsWithAsmps =
  do env     <- IM $ fmap (Map.elems . iVars) ask
     fromEnv <- forM env $ \v ->
                  case v of
                    ExtVar sch  -> getVars sch
                    CurSCC _ t  -> getVars t
     hasCts <- IM (iHasCts <$> get)
     let sels = map (goal . hasGoal) (concat hasCts)
     fromSels <- mapM getVars sels
     fromEx   <- (getVars . concatMap Map.elems) =<< IM (fmap iExistTVars get)
     return (Set.unions fromEnv `Set.union` Set.unions fromSels
                                `Set.union` fromEx)
  where
  getVars x = fvs `fmap` applySubst x

--------------------------------------------------------------------------------


-- | Lookup the type of a variable.
lookupVar :: Name -> InferM VarType
lookupVar x =
  do mb <- IM $ asks $ Map.lookup x . iVars
     case mb of
       Just a  -> pure a
       Nothing ->
         do mb1 <- Map.lookup x . iBindTypes <$> IM get
            case mb1 of
              Just a -> pure (ExtVar a)
              Nothing ->
                do mp <- IM $ asks iVars
                   panic "lookupVar" $ [ "Undefined variable"
                                     , show x
                                     , "IVARS"
                                     ] ++ map (show . debugShowUniques . pp) (Map.keys mp)

-- | Lookup a type variable.  Return `Nothing` if there is no such variable
-- in scope, in which case we must be dealing with a type constant.
lookupTParam :: Name -> InferM (Maybe TParam)
lookupTParam x = IM $ asks $ find this . iTVars
  where this tp = tpName tp == Just x

-- | Lookup the definition of a type synonym.
lookupTSyn :: Name -> InferM (Maybe TySyn)
lookupTSyn x = Map.lookup x <$> getTSyns

-- | Lookup the definition of a nominal type
lookupNominal :: Name -> InferM (Maybe NominalType)
lookupNominal x = Map.lookup x <$> getNominalTypes

-- | Lookup the kind of a parameter type
lookupParamType :: Name -> InferM (Maybe ModTParam)
lookupParamType x = Map.lookup x <$> getParamTypes

lookupSignature :: P.ImpName Name -> InferM ModParamNames
lookupSignature nx =
  case nx of
    -- XXX: top
    P.ImpNested x ->
      do sigs <- getSignatures
         case Map.lookup x sigs of
           Just ips -> pure ips
           Nothing  -> panic "lookupSignature"
                        [ "Missing signature", show x ]

    P.ImpTop t ->
      do loaded <- iExtSignatures <$> IM ask
         case loaded t of
           Just ps -> pure ps
           Nothing -> panic "lookupSignature"
                        [ "Top level signature is not loaded", show (pp nx) ]

-- | Lookup an external (i.e., previously loaded) top module.
lookupTopModule :: ModName -> InferM (Maybe (ModuleG (), If.IfaceG ()))
lookupTopModule m =
  do ms <- iExtModules <$> IM ask
     pure (ms m)

lookupFunctor :: P.ImpName Name -> InferM (ModuleG ())
lookupFunctor iname =
  case iname of
    P.ImpTop m -> fst . fromMb <$> lookupTopModule m
    P.ImpNested m ->
      do localFuns <- getScope mFunctors
         case Map.lookup m localFuns of
           Just a -> pure a { mName = () }
           Nothing ->
             do mbTop <- lookupTopModule (nameTopModule m)
                pure (fromMb do a <- fst <$> mbTop
                                b <- Map.lookup m (mFunctors a)
                                pure b { mName = () })
  where
  fromMb mb = case mb of
                Just a -> a
                Nothing -> panic "lookupFunctor"
                                  [ "Missing functor", show iname ]


{- | Get information about the things defined in the module.
Note that, in general, the interface may contain *more* than just the
definitions in the module, however the `ifNames` should indicate which
ones are part of the module.
-}
lookupModule :: P.ImpName Name -> InferM (If.IfaceG ())
lookupModule iname =
  case iname of
    P.ImpTop m -> snd . fromMb <$> lookupTopModule m
    P.ImpNested m ->
      do localMods <- getScope mSubmodules
         case Map.lookup m localMods of
           Just names ->
              do n <- genIfaceWithNames (smIface names) <$> getCurDecls
                 pure (If.ifaceForgetName n)

           Nothing ->
             do mb <- lookupTopModule (nameTopModule m)
                pure (fromMb
                         do iface <- snd <$> mb
                            names <- Map.lookup m
                                        (If.ifModules (If.ifDefines iface))
                            pure iface
                                   { If.ifNames = names { If.ifsName = () } })

  where
  fromMb mb = case mb of
                Just a -> a
                Nothing -> panic "lookupModule"
                                  [ "Missing module", show iname ]



lookupModParam :: P.Ident -> InferM (Maybe ModParam)
lookupModParam p =
  do scope <- getScope mParams
     pure (Map.lookup p scope)


-- | Check if we already have a name for this existential type variable and,
-- if so, return the definition.  If not, try to create a new definition,
-- if this is allowed.  If not, returns nothing.

existVar :: Name -> Kind -> InferM Type
existVar x k =
  do scopes <- iExistTVars <$> IM get
     case msum (map (Map.lookup x) scopes) of
       Just ty -> return ty
       Nothing ->
         case scopes of
           [] ->
              do recordError (UndefinedExistVar x)
                 newType TypeErrorPlaceHolder k

           sc : more ->
             do ty <- newType TypeErrorPlaceHolder k
                IM $ sets_ $ \s -> s{ iExistTVars = Map.insert x ty sc : more }
                return ty


-- | Returns the type synonyms that are currently in scope.
getTSyns :: InferM (Map Name TySyn)
getTSyns = getScope mTySyns

-- | Returns the nominal type declarations that are in scope.
getNominalTypes :: InferM (Map Name NominalType)
getNominalTypes = getScope mNominalTypes

-- | Returns the abstract function declarations
getParamTypes :: InferM (Map Name ModTParam)
getParamTypes = getScope mParamTypes

-- | Constraints on the module's parameters.
getParamConstraints :: InferM [Located Prop]
getParamConstraints = getScope mParamConstraints

-- | Get the set of bound type variables that are in scope.
getTVars :: InferM (Set Name)
getTVars = IM $ asks $ Set.fromList . mapMaybe tpName . iTVars

-- | Return the keys of the bound variables that are in scope.
getBoundInScope :: InferM (Set TParam)
getBoundInScope =
  do ro <- IM ask
     params <- Set.fromList . map mtpParam . Map.elems <$> getParamTypes
     let bound  = Set.fromList (iTVars ro)
     return $! Set.union params bound

-- | Retrieve the value of the `mono-binds` option.
getMonoBinds :: InferM Bool
getMonoBinds  = IM (asks iMonoBinds)

getCallStacks :: InferM Bool
getCallStacks = IM (asks iCallStacks)

getSignatures :: InferM (Map Name ModParamNames)
getSignatures = getScope mSignatures



{- | We disallow shadowing between type synonyms and type variables
because it is confusing.  As a bonus, in the implementation we don't
need to worry about where we lookup things (i.e., in the variable or
type synonym environment. -}

-- XXX: this should be done in renamer
checkTShadowing :: String -> Name -> InferM ()
checkTShadowing this new =
  do tsyns <- getTSyns
     ro <- IM ask
     rw <- IM get
     let shadowed =
           do _ <- Map.lookup new tsyns
              return "type synonym"
           `mplus`
           do guard (new `elem` mapMaybe tpName (iTVars ro))
              return "type variable"
           `mplus`
           do _ <- msum (map (Map.lookup new) (iExistTVars rw))
              return "type"

     case shadowed of
       Nothing -> return ()
       Just that ->
          recordError (TypeShadowing this new that)


-- | The sub-computation is performed with the given type parameter in scope.
withTParam :: TParam -> InferM a -> InferM a
withTParam p (IM m) =
  do case tpName p of
       Just x  -> checkTShadowing "variable" x
       Nothing -> return ()
     IM $ mapReader (\r -> r { iTVars = p : iTVars r }) m

withTParams :: [TParam] -> InferM a -> InferM a
withTParams ps m = foldr withTParam m ps


-- | Execute the given computation in a new top scope.
-- The sub-computation would typically be validating a module.
newScope :: ScopeName -> InferM ()
newScope nm = IM $ sets_ \rw -> rw { iScope = emptyModule nm : iScope rw }

newLocalScope :: InferM ()
newLocalScope = newScope LocalScope

newSignatureScope :: Name -> Maybe Text -> InferM ()
newSignatureScope x doc =
  do updScope \o -> o { mNested = Set.insert x (mNested o) }
     newScope (SignatureScope x doc)

newTopSignatureScope :: ModName -> InferM ()
newTopSignatureScope x = newScope (TopSignatureScope x)

{- | Start a new submodule scope.  The imports and exports are just used
to initialize an empty module.  As we type check declarations they are
added to this module's scope. -}
newSubmoduleScope ::
  Name -> [Text] -> ExportSpec Name -> NamingEnv -> InferM ()
newSubmoduleScope x docs e inScope =
  do updScope \o -> o { mNested = Set.insert x (mNested o) }
     newScope (SubModule x)
     updScope \m -> m { mDoc = docs, mExports = e, mInScope = inScope }

newModuleScope :: [Text] -> P.ModName -> ExportSpec Name -> NamingEnv -> InferM ()
newModuleScope docs x e inScope =
  do newScope (MTopModule x)
     updScope \m -> m { mDoc = docs, mExports = e, mInScope = inScope }

-- | Update the current scope (first in the list). Assumes there is one.
updScope :: (ModuleG ScopeName -> ModuleG ScopeName) -> InferM ()
updScope f = IM $ sets_ \rw -> rw { iScope = upd (iScope rw) }
  where
  upd r =
    case r of
      []       -> panic "updTopScope" [ "No top scope" ]
      s : more -> f s : more

endLocalScope :: InferM ([DeclGroup], Map Name TySyn)
endLocalScope =
  IM $ sets \rw ->
       case iScope rw of
         x : xs | LocalScope <- mName x ->
                    ( (reverse (mDecls x), mTySyns x), rw { iScope = xs })

         _ -> panic "endLocalScope" ["Missing local scope"]

endSubmodule :: InferM ()
endSubmodule =
  IM $ sets_ \rw ->
       case iScope rw of
         x@Module { mName = SubModule m } : y : more -> rw { iScope = z : more }
           where
           x1    = x { mName = m, mDecls = reverse (mDecls x) }

           isFun = isParametrizedModule x1

           add :: Monoid a => (ModuleG ScopeName -> a) -> a
           add f = if isFun then f y else f x <> f y

           z = Module
                 { mName             = mName y
                 , mDoc              = mDoc y
                 , mExports          = mExports y
                 , mParamTypes       = mParamTypes y
                 , mParamFuns        = mParamFuns  y
                 , mParamConstraints = mParamConstraints y
                 , mParams           = mParams y
                 , mNested           = mNested y
                 , mInScope          = mInScope y

                 , mTySyns      = add mTySyns
                 , mNominalTypes = add mNominalTypes
                 , mDecls       = add mDecls
                 , mSignatures  = add mSignatures
                 , mSubmodules  = if isFun
                                    then mSubmodules y
                                    else let sm = Submodule
                                                    { smIface = genIfaceNames x1
                                                    , smInScope = mInScope x }
                                         in Map.insert m sm
                                               (mSubmodules x <> mSubmodules y)
                 , mFunctors    = if isFun
                                    then Map.insert m x1 (mFunctors y)
                                    else mFunctors x <> mFunctors y
                 }

         _ -> panic "endSubmodule" [ "Not a submodule" ]


endModule :: InferM TCTopEntity
endModule =
  IM $ sets \rw ->
    case iScope rw of
      [ x ] | MTopModule m <- mName x ->
        ( TCTopModule x { mName = m, mDecls = reverse (mDecls x) }
        , rw { iScope = [] }
        )
      _ -> panic "endModule" [ "Not a single top module" ]

endSignature :: InferM ()
endSignature =
  IM $ sets_ \rw ->
    case iScope rw of
      x@Module { mName = SignatureScope m doc } : y : more ->
        rw { iScope = z : more }
        where
        z   = y { mSignatures = Map.insert m sig (mSignatures y) }
        sig = ModParamNames
                { mpnTypes       = mParamTypes x
                , mpnConstraints = mParamConstraints x
                , mpnFuns        = mParamFuns x
                , mpnTySyn       = mTySyns x
                , mpnDoc         = doc
                }
      _ -> panic "endSignature" [ "Not a signature scope" ]

endTopSignature :: InferM TCTopEntity
endTopSignature =
  IM $ sets \rw ->
    case iScope rw of
      [ x ] | TopSignatureScope m <- mName x ->
        ( TCTopSignature m ModParamNames
                             { mpnTypes       = mParamTypes x
                             , mpnConstraints = mParamConstraints x
                             , mpnFuns        = mParamFuns x
                             , mpnTySyn       = mTySyns x
                             , mpnDoc         = Nothing
                             }
        , rw { iScope = [] }
        )
      _ -> panic "endTopSignature" [ "Not a top-level signature" ]



-- | Get an environment combining all nested scopes.
getScope :: Semigroup a => (ModuleG ScopeName -> a) -> InferM a
getScope f =
  do ro <- IM ask
     rw <- IM get
     pure (sconcat (f (iExtScope ro) :| map f (iScope rw)))

getCurDecls :: InferM (ModuleG ())
getCurDecls =
  do ro <- IM ask
     rw <- IM get
     pure (foldr (\m1 m2 -> mergeDecls (forget m1) m2)
                (forget (iExtScope ro)) (iScope rw))

  where
  forget m = m { mName = () }

  mergeDecls m1 m2 =
    Module
      { mName             = ()
      , mDoc              = mempty
      , mExports          = mempty
      , mParams           = mempty
      , mParamTypes       = mempty
      , mParamConstraints = mempty
      , mParamFuns        = mempty
      , mNested           = mempty

      , mTySyns           = uni mTySyns
      , mNominalTypes     = uni mNominalTypes
      , mDecls            = uni mDecls
      , mSubmodules       = uni mSubmodules
      , mFunctors         = uni mFunctors
      , mSignatures       = uni mSignatures

      , mInScope          = uni mInScope
      }
    where
    uni f = f m1 <> f m2


addDecls :: DeclGroup -> InferM ()
addDecls ds =
  do updScope \r -> r { mDecls = ds : mDecls r }
     IM $ sets_ \rw -> rw { iBindTypes = new rw }
  where
  add d   = Map.insert (dName d) (dSignature d)
  new rw  = foldr add (iBindTypes rw) (groupDecls ds)

-- | The sub-computation is performed with the given type-synonym in scope.
addTySyn :: TySyn -> InferM ()
addTySyn t =
  do let x = tsName t
     checkTShadowing "synonym" x
     updScope \r -> r { mTySyns = Map.insert x t (mTySyns r) }

addNominal :: NominalType -> InferM ()
addNominal t =
  do updScope \r -> r { mNominalTypes = Map.insert (ntName t) t (mNominalTypes r) }
     let cons = nominalTypeConTypes t
         ins  = uncurry Map.insert
     IM $ sets_ \rw -> rw { iBindTypes = foldr ins (iBindTypes rw) cons }

addParamType :: ModTParam -> InferM ()
addParamType a =
  updScope \r -> r { mParamTypes = Map.insert (mtpName a) a (mParamTypes r) }

addSignatures :: Map Name ModParamNames -> InferM ()
addSignatures mp =
  updScope \r -> r { mSignatures = Map.union mp (mSignatures r) }

addSubmodules :: Map Name Submodule -> InferM ()
addSubmodules mp =
  updScope \r -> r { mSubmodules = Map.union mp (mSubmodules r) }

addFunctors :: Map Name (ModuleG Name) -> InferM ()
addFunctors mp =
  updScope \r -> r { mFunctors = Map.union mp (mFunctors r) }

setNested :: Set Name -> InferM ()
setNested names =
  updScope \r -> r { mNested = names }


-- | The sub-computation is performed with the given abstract function in scope.
addParamFun :: ModVParam -> InferM ()
addParamFun x =
  do updScope \r -> r { mParamFuns = Map.insert (mvpName x) x (mParamFuns r) }
     IM $ sets_ \rw -> rw { iBindTypes = Map.insert (mvpName x) (mvpType x)
                                                    (iBindTypes rw) }

-- | Add some assumptions for an entire module
addParameterConstraints :: [Located Prop] -> InferM ()
addParameterConstraints ps =
  updScope \r -> r { mParamConstraints = ps ++ mParamConstraints r }

addModParam :: ModParam -> InferM ()
addModParam p =
  updScope \r -> r { mParams = Map.insert (mpName p) p (mParams r) }




-- | Perform the given computation in a new scope (i.e., the subcomputation
-- may use existential type variables).  This is a different kind of scope
-- from the nested modules one.
inNewScope :: InferM a -> InferM a
inNewScope m =
  do curScopes <- iExistTVars <$> IM get
     IM $ sets_ $ \s -> s { iExistTVars = Map.empty : curScopes }
     a <- m
     IM $ sets_ $ \s -> s { iExistTVars = curScopes }
     return a


-- | The sub-computation is performed with the given variable in scope.
withVarType :: Name -> VarType -> InferM a -> InferM a
withVarType x s (IM m) =
  IM $ mapReader (\r -> r { iVars = Map.insert x s (iVars r) }) m

withVarTypes :: [(Name,VarType)] -> InferM a -> InferM a
withVarTypes xs m = foldr (uncurry withVarType) m xs

withVar :: Name -> Schema -> InferM a -> InferM a
withVar x s = withVarType x (ExtVar s)

-- | The sub-computation is performed with the given variables in scope.
withMonoType :: (Name,Located Type) -> InferM a -> InferM a
withMonoType (x,lt) = withVar x (Forall [] [] (thing lt))

-- | The sub-computation is performed with the given variables in scope.
withMonoTypes :: Map Name (Located Type) -> InferM a -> InferM a
withMonoTypes xs m = foldr withMonoType m (Map.toList xs)

--------------------------------------------------------------------------------
-- Kind checking


newtype KindM a = KM { unKM :: ReaderT KRO (StateT KRW InferM)  a }

data KRO = KRO { lazyTParams :: Map Name TParam -- ^ lazy map, with tparams.
               , allowWild   :: AllowWildCards  -- ^ are type-wild cards allowed?
               }

-- | Do we allow wild cards in the given context.
data AllowWildCards = AllowWildCards | NoWildCards

data KRW = KRW { typeParams :: Map Name Kind -- ^ kinds of (known) vars.
               , kCtrs      :: [(ConstraintSource,[Prop])]
               }

instance Functor KindM where
  fmap f (KM m) = KM (fmap f m)

instance A.Applicative KindM where
  pure x = KM (pure x)
  (<*>) = ap

instance Monad KindM where
  return        = pure
  KM m >>= k    = KM (m >>= unKM . k)

instance Fail.MonadFail KindM where
  fail x        = KM (fail x)


{- | The arguments to this function are as follows:

(type param. name, kind signature (opt.), type parameter)

The type parameter is just a thunk that we should not force.
The reason is that the parameter depends on the kind that we are
in the process of computing.

As a result we return the value of the sub-computation and the computed
kinds of the type parameters. -}
runKindM :: AllowWildCards               -- Are type-wild cards allowed?
         -> [(Name, Maybe Kind, TParam)] -- ^ See comment
         -> KindM a -> InferM (a, Map Name Kind, [(ConstraintSource,[Prop])])
runKindM wildOK vs (KM m) =
  do (a,kw) <- runStateT krw (runReaderT kro m)
     return (a, typeParams kw, kCtrs kw)
  where
  tps  = Map.fromList [ (x,t) | (x,_,t)      <- vs ]
  kro  = KRO { allowWild = wildOK, lazyTParams = tps }
  krw  = KRW { typeParams = Map.fromList [ (x,k) | (x,Just k,_) <- vs ]
             , kCtrs = []
             }

-- | This is what's returned when we lookup variables during kind checking.
data LkpTyVar = TLocalVar TParam (Maybe Kind) -- ^ Locally bound variable.
              | TOuterVar TParam              -- ^ An outer binding.

-- | Check if a name refers to a type variable.
kLookupTyVar :: Name -> KindM (Maybe LkpTyVar)
kLookupTyVar x = KM $
  do vs <- lazyTParams `fmap` ask
     ss <- get
     case Map.lookup x vs of
       Just t  -> return $ Just $ TLocalVar t $ Map.lookup x $ typeParams ss
       Nothing -> lift $ lift $ do t <- lookupTParam x
                                   return (fmap TOuterVar t)

-- | Are type wild-cards OK in this context?
kWildOK :: KindM AllowWildCards
kWildOK = KM $ fmap allowWild ask

-- | Reports an error.
kRecordError :: Error -> KindM ()
kRecordError e = kInInferM $ recordError e

kRecordWarning :: Warning -> KindM ()
kRecordWarning w = kInInferM $ recordWarning w

kIO :: IO a -> KindM a
kIO m = KM $ lift $ lift $ io m

-- | Generate a fresh unification variable of the given kind.
-- NOTE:  We do not simplify these, because we end up with bottom.
-- See `Kind.hs`
-- XXX: Perhaps we can avoid the recursion?
kNewType :: TypeSource -> Kind -> KindM Type
kNewType src k =
  do tps <- KM $ do vs <- asks lazyTParams
                    return $ Set.fromList (Map.elems vs)
     kInInferM $ TVar `fmap` newTVar' src tps k

-- | Lookup the definition of a type synonym.
kLookupTSyn :: Name -> KindM (Maybe TySyn)
kLookupTSyn x = kInInferM $ lookupTSyn x

-- | Lookup the definition of a nominal type.
kLookupNominal :: Name -> KindM (Maybe NominalType)
kLookupNominal = kInInferM . lookupNominal

kLookupParamType :: Name -> KindM (Maybe ModTParam)
kLookupParamType x = kInInferM (lookupParamType x)

kExistTVar :: Name -> Kind -> KindM Type
kExistTVar x k = kInInferM $ existVar x k

-- | Replace the given bound variables with concrete types.
kInstantiateT :: Type -> [(TParam, Type)] -> KindM Type
kInstantiateT t as = return (apSubst su t)
  where su = listParamSubst as

{- | Record the kind for a local type variable.
This assumes that we already checked that there was no other valid
kind for the variable (if there was one, it gets over-written). -}
kSetKind :: Name -> Kind -> KindM ()
kSetKind v k = KM $ sets_ $ \s -> s{ typeParams = Map.insert v k (typeParams s)}

-- | The sub-computation is about the given range of the source code.
kInRange :: Range -> KindM a -> KindM a
kInRange r (KM m) = KM $
  do e <- ask
     s <- get
     (a,s1) <- lift $ lift $ inRange r $ runStateT s $ runReaderT e m
     set s1
     return a

kNewGoals :: ConstraintSource -> [Prop] -> KindM ()
kNewGoals _ [] = return ()
kNewGoals c ps = KM $ sets_ $ \s -> s { kCtrs = (c,ps) : kCtrs s }

kInInferM :: InferM a -> KindM a
kInInferM m = KM $ lift $ lift m
