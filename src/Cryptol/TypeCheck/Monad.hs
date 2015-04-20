-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE RecordWildCards, CPP, Safe #-}
#if __GLASGOW_HASKELL__ >= 706
{-# LANGUAGE RecursiveDo #-}
#else
{-# LANGUAGE DoRec #-}
#endif
module Cryptol.TypeCheck.Monad
  ( module Cryptol.TypeCheck.Monad
  , module Cryptol.TypeCheck.InferTypes
  ) where

import           Cryptol.Parser.Position
import qualified Cryptol.Parser.AST as P
import           Cryptol.TypeCheck.AST
import           Cryptol.TypeCheck.Subst
import           Cryptol.TypeCheck.Unify(mgu, Result(..), UnificationError(..))
import           Cryptol.TypeCheck.InferTypes
import           Cryptol.Utils.PP(pp, (<+>), Doc, text, quotes)
import           Cryptol.Utils.Panic(panic)

import qualified Data.Map as Map
import qualified Data.Set as Set
import           Data.Map (Map)
import           Data.Set (Set)
import           Data.List(find, minimumBy, groupBy, sortBy)
import           Data.Maybe(mapMaybe)
import           Data.Function(on)
import           MonadLib
import qualified Control.Applicative as A
import           Control.Monad.Fix(MonadFix(..))

#if __GLASGOW_HASKELL__ < 710
import           Data.Functor
#endif

-- | Information needed for type inference.
data InferInput = InferInput
  { inpRange     :: Range             -- ^ Location of program source
  , inpVars      :: Map QName Schema  -- ^ Variables that are in scope
  , inpTSyns     :: Map QName TySyn   -- ^ Type synonyms that are in scope
  , inpNewtypes  :: Map QName Newtype -- ^ Newtypes in scope
  , inpNameSeeds :: NameSeeds         -- ^ Private state of type-checker
  , inpMonoBinds :: Bool              -- ^ Should local bindings without
                                      --   signatures be monomorphized?

  , inpSolverConfig :: SolverConfig   -- ^ Options for the constraint solver
  } deriving Show


-- | This is used for generating various names.
data NameSeeds = NameSeeds
  { seedTVar    :: !Int
  , seedGoal    :: !Int
  } deriving Show

-- | The initial seeds, used when checking a fresh program.
nameSeeds :: NameSeeds
nameSeeds = NameSeeds { seedTVar = 10, seedGoal = 0 }


-- | The results of type inference.
data InferOutput a
  = InferFailed [(Range,Warning)] [(Range,Error)]
    -- ^ We found some errors

  | InferOK [(Range,Warning)] NameSeeds a
    -- ^ Type inference was successful.


    deriving Show

runInferM :: TVars a => InferInput -> InferM a -> IO (InferOutput a)
runInferM info (IM m) =
  do rec ro <- return RO { iRange     = inpRange info
                     , iVars          = Map.map ExtVar (inpVars info)
                     , iTVars         = []
                     , iTSyns         = fmap mkExternal (inpTSyns info)
                     , iNewtypes      = fmap mkExternal (inpNewtypes info)
                     , iSolvedHasLazy = iSolvedHas finalRW     -- RECURSION
                     , iMonoBinds     = inpMonoBinds info
                     , iSolverConfig  = inpSolverConfig info
                     }

         (result, finalRW) <- runStateT rw $ runReaderT ro m  -- RECURSION

     let theSu    = iSubst finalRW
         defSu    = defaultingSubst theSu
         warns    = [(r,apSubst theSu w) | (r,w) <- iWarnings finalRW ]

     case iErrors finalRW of
       [] ->
         case (iCts finalRW, iHasCts finalRW) of
           (cts,[])
             | nullGoals cts
                   -> return $ InferOK warns
                                  (iNameSeeds finalRW)
                                  (apSubst defSu result)
           (cts,has) -> return $ InferFailed warns
                $ dropErrorsFromSameLoc
                [ ( goalRange g
                  , UnsolvedGoal (apSubst theSu g)
                  ) | g <- fromGoals cts ++ map hasGoal has
                ]
       errs -> return $ InferFailed warns
                      $ dropErrorsFromSameLoc
                                  [(r,apSubst theSu e) | (r,e) <- errs]

  where
  mkExternal x = (IsExternal, x)
  rw = RW { iErrors     = []
          , iWarnings   = []
          , iSubst      = emptySubst
          , iExistTVars = []

          , iNameSeeds  = inpNameSeeds info

          , iCts        = emptyGoals
          , iHasCts     = []
          , iSolvedHas  = Map.empty
          }

  dropErrorsFromSameLoc = map chooseBestError . groupBy ((==)    `on` fst)
                                              . sortBy  (cmpRange `on` fst)

  addErrorSize (r,e) = (length (show (pp e)), (r,e))
  chooseBestError    = snd . minimumBy (compare `on` fst) . map addErrorSize

  -- The actual order does not matter
  cmpRange (Range x y z) (Range a b c) = compare (x,y,z) (a,b,c)




newtype InferM a = IM { unIM :: ReaderT RO (StateT RW IO) a }

data DefLoc = IsLocal | IsExternal

-- | Read-only component of the monad.
data RO = RO
  { iRange    :: Range                  -- ^ Source code being analysed
  , iVars     :: Map QName VarType      -- ^ Type of variable that are in scope

  {- NOTE: We assume no shadowing between these two, so it does not matter
  where we look first. Similarly, we assume no shadowing with
  the existential type variable (in RW).  See `checkTShadowing`. -}

  , iTVars    :: [TParam]                  -- ^ Type variable that are in scope
  , iTSyns    :: Map QName (DefLoc, TySyn) -- ^ Type synonyms that are in scope
  , iNewtypes :: Map QName (DefLoc, Newtype)
   -- ^ Newtype declarations in scope
   --
   -- NOTE: type synonyms take precedence over newtype.  The reason is
   -- that we can define local type synonyms, but not local newtypes.
   -- So, either a type-synonym shadows a newtype, or it was declared
   -- at the top-level, but then there can't be a newtype with the
   -- same name (this should be caught by the renamer).

  , iSolvedHasLazy :: Map Int (Expr -> Expr)
    -- ^ NOTE: This field is lazy in an important way!  It is the
    -- final version of `iSolvedHas` in `RW`, and the two are tied
    -- together through recursion.  The field is here so that we can
    -- look thing up before they are defined, which is OK because we
    -- don't need to know the results until everything is done.

  , iMonoBinds :: Bool
    -- ^ When this flag is set to true, bindings that lack signatures
    -- in where-blocks will never be generalized. Bindings with type
    -- signatures, and all bindings at top level are unaffected.

  , iSolverConfig :: SolverConfig
  }

-- | Read-write component of the monad.
data RW = RW
  { iErrors   :: ![(Range,Error)]       -- ^ Collected errors
  , iWarnings :: ![(Range,Warning)]     -- ^ Collected warnings
  , iSubst    :: !Subst                 -- ^ Accumulated substitution

  , iExistTVars  :: [Map QName Type]
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

  , iSolvedHas :: Map Int (Expr -> Expr)
    -- ^ Selector constraints that have been solved (ref. iSolvedSelectorsLazy)

  -- Generating names
  , iNameSeeds :: !NameSeeds

  -- Constraints that need solving
  , iCts      :: !Goals                -- ^ Ordinary constraints
  , iHasCts   :: ![HasGoal]
    {- ^ Tuple/record projection constraints.  The `Int` is the "name"
         of the constraint, used so that we can name it solution properly. -}
  }

instance Functor InferM where
  fmap f (IM m) = IM (fmap f m)

instance A.Applicative InferM where
  pure  = return
  (<*>) = ap

instance Monad InferM where
  return x      = IM (return x)
  fail x        = IM (fail x)
  IM m >>= f    = IM (m >>= unIM . f)

instance MonadFix InferM where
  mfix f        = IM (mfix (unIM . f))


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
recordError e =
  do r <- curRange
     IM $ sets_ $ \s -> s { iErrors = (r,e) : iErrors s }

recordWarning :: Warning -> InferM ()
recordWarning w =
  do r <- curRange
     IM $ sets_ $ \s -> s { iWarnings = (r,w) : iWarnings s }

getSolverConfig :: InferM SolverConfig
getSolverConfig =
  do RO { .. } <- IM ask
     return iSolverConfig




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
  do goals <- applySubst =<< IM (sets $ \s -> (iCts s, s { iCts = emptyGoals }))
     return (fromGoals goals)

-- | Add a bunch of goals that need solving.
addGoals :: [Goal] -> InferM ()
addGoals gs = IM $ sets_ $ \s -> s { iCts = foldl (flip insertGoal) (iCts s) gs }

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



{- | Record a constraint that when we select from the first type,
we should get a value of the second type.
The returned function should be used to wrap the expression from
which we are selecting (i.e., the record or tuple).  Plese note
that the resulting expression should not be forced before the
constraint is solved.
-}
newHasGoal :: P.Selector -> Type -> Type -> InferM (Expr -> Expr)
newHasGoal l ty f =
  do goalName <- newGoalName
     g        <- newGoal CtSelector (pHas l ty f)
     IM $ sets_ $ \s -> s { iHasCts = HasGoal goalName g : iHasCts s }
     solns    <- IM $ fmap iSolvedHasLazy ask
     return $ case Map.lookup goalName solns of
                Just e1 -> e1
                Nothing -> panic "newHasGoal" ["Unsolved has goal in result"]

-- | Add a previously generate has constrained
addHasGoal :: HasGoal -> InferM ()
addHasGoal g = IM $ sets_ $ \s -> s { iHasCts = g : iHasCts s }

-- | Get the `Has` constraints.  Each of this should either be solved,
-- or added back using `addHasGoal`.
getHasGoals :: InferM [HasGoal]
getHasGoals = do gs <- IM $ sets $ \s -> (iHasCts s, s { iHasCts = [] })
                 applySubst gs

-- | Specify the solution (`Expr -> Expr`) for the given constraint (`Int`).
solveHasGoal :: Int -> (Expr -> Expr) -> InferM ()
solveHasGoal n e =
  IM $ sets_ $ \s -> s { iSolvedHas = Map.insert n e (iSolvedHas s) }


--------------------------------------------------------------------------------


newName :: (NameSeeds -> (a , NameSeeds)) -> InferM a
newName upd = IM $ sets $ \s -> let (x,seeds) = upd (iNameSeeds s)
                                in (x, s { iNameSeeds = seeds })


-- | Generate a new name for a goal.
newGoalName :: InferM Int
newGoalName = newName $ \s -> let x = seedGoal s
                              in (x, s { seedGoal = x + 1})

-- | Generate a new free type variable.
newTVar :: Doc -> Kind -> InferM TVar
newTVar src k = newTVar' src Set.empty k

-- | Generate a new free type variable that depends on these additional
-- type parameters.
newTVar' :: Doc -> Set TVar -> Kind -> InferM TVar
newTVar' src extraBound k =
  do bound <- getBoundInScope
     let vs = Set.union extraBound bound
     newName $ \s -> let x = seedTVar s
                     in (TVFree x k vs src, s { seedTVar = x + 1 })



-- | Generate a new free type variable.
newTParam :: Maybe QName -> Kind -> InferM TParam
newTParam nm k = newName $ \s -> let x = seedTVar s
                                 in (TParam { tpUnique = x
                                            , tpKind   = k
                                            , tpName   = nm
                                            }
                                 , s { seedTVar = x + 1 })


-- | Generate an unknown type.  The doc is a note about what is this type about.
newType :: Doc -> Kind -> InferM Type
newType src k = TVar `fmap` newTVar src k



--------------------------------------------------------------------------------


-- | Record that the two types should be syntactically equal.
unify :: Type -> Type -> InferM [Prop]
unify t1 t2 =
  do t1' <- applySubst t1
     t2' <- applySubst t2
     case mgu t1' t2' of
       OK (su1,ps) -> extendSubst su1 >> return ps
       Error err   ->
         do case err of
              UniTypeLenMismatch _ _ -> recordError (TypeMismatch t1' t2')
              UniTypeMismatch s1 s2 -> recordError (TypeMismatch s1 s2)
              UniKindMismatch k1 k2 -> recordError (KindMismatch k1 k2)
              UniRecursive x t -> recordError (RecursiveType (TVar x) t)
              UniNonPolyDepends x vs -> recordError
                                          (TypeVariableEscaped (TVar x) vs)
              UniNonPoly x t -> recordError (NotForAll x t)
            return []




-- | Apply the accumulated substitution to something with free type variables.
applySubst :: TVars t => t -> InferM t
applySubst t =
  do su <- getSubst
     return (apSubst su t)

-- | Get the substitution that we have accumulated so far.
getSubst :: InferM Subst
getSubst = IM $ fmap iSubst get

-- | Add to the accumulated substitution.
extendSubst :: Subst -> InferM ()
extendSubst su = IM $ sets_ $ \s -> s { iSubst = su @@ iSubst s }


-- | Variables that are either mentioned in the environment or in
-- a selector constraint.
varsWithAsmps :: InferM (Set TVar)
varsWithAsmps =
  do env     <- IM $ fmap (Map.elems . iVars) ask
     fromEnv <- forM env $ \v ->
                  case v of
                    ExtVar sch  -> getVars sch
                    CurSCC _ t  -> getVars t
     sels <- IM $ fmap (map (goal . hasGoal) . iHasCts) get
     fromSels <- mapM getVars sels
     fromEx   <- (getVars . concatMap Map.elems) =<< IM (fmap iExistTVars get)
     return (Set.unions fromEnv `Set.union` Set.unions fromSels
                                `Set.union` fromEx)
  where
  getVars x = fvs `fmap` applySubst x

--------------------------------------------------------------------------------


-- | Lookup the type of a variable.
lookupVar :: QName -> InferM VarType
lookupVar x =
  do mb <- IM $ asks $ Map.lookup x . iVars
     case mb of
       Just t  -> return t
       Nothing ->
         do mbNT <- lookupNewtype x
            case mbNT of
              Just nt -> return (ExtVar (newtypeConType nt))
              Nothing -> do recordError $ UndefinedVariable x
                            a <- newType (text "type of" <+> pp x) KType
                            return $ ExtVar $ Forall [] [] a

-- | Lookup a type variable.  Return `Nothing` if there is no such variable
-- in scope, in which case we must be dealing with a type constant.
lookupTVar :: QName -> InferM (Maybe Type)
lookupTVar x = IM $ asks $ fmap (TVar . tpVar) . find this . iTVars
  where this tp = tpName tp == Just x

-- | Lookup the definition of a type synonym.
lookupTSyn :: QName -> InferM (Maybe TySyn)
lookupTSyn x = fmap (fmap snd . Map.lookup x) getTSyns

-- | Lookup the definition of a newtype
lookupNewtype :: QName -> InferM (Maybe Newtype)
lookupNewtype x = fmap (fmap snd . Map.lookup x) getNewtypes

-- | Check if we already have a name for this existential type variable and,
-- if so, return the definition.  If not, try to create a new definition,
-- if this is allowed.  If not, returns nothing.

existVar :: QName -> Kind -> InferM Type
existVar x k =
  do scopes <- iExistTVars <$> IM get
     case msum (map (Map.lookup x) scopes) of
       Just ty -> return ty
       Nothing ->
         case scopes of
           [] ->
              do recordError $ ErrorMsg $
                    text "Undefined type" <+> quotes (pp x)
                 newType (text "undefined existential type varible" <+>
                                                            quotes (pp x)) k

           sc : more ->
             do ty <- newType (text "existential type variable"
                                                        <+> quotes (pp x)) k
                IM $ sets_ $ \s -> s{ iExistTVars = Map.insert x ty sc : more }
                return ty


-- | Returns the type synonyms that are currently in scope.
getTSyns :: InferM (Map QName (DefLoc,TySyn))
getTSyns = IM $ asks iTSyns

-- | Returns the newtype declarations that are in scope.
getNewtypes :: InferM (Map QName (DefLoc,Newtype))
getNewtypes = IM $ asks iNewtypes

-- | Get the set of bound type variables that are in scope.
getTVars :: InferM (Set QName)
getTVars = IM $ asks $ Set.fromList . mapMaybe tpName . iTVars

-- | Return the keys of the bound variables that are in scope.
getBoundInScope :: InferM (Set TVar)
getBoundInScope = IM $ asks $ Set.fromList . map tpVar . iTVars

-- | Retrieve the value of the `mono-binds` option.
getMonoBinds :: InferM Bool
getMonoBinds  = IM (asks iMonoBinds)

{- | We disallow shadowing between type synonyms and type variables
because it is confusing.  As a bonus, in the implementation we don't
need to worry about where we lookup things (i.e., in the variable or
type synonym environment. -}

checkTShadowing :: String -> QName -> InferM ()
checkTShadowing this new =
  do ro <- IM ask
     rw <- IM get
     let shadowed =
           do _ <- Map.lookup new (iTSyns ro)
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
          recordError $ ErrorMsg $
             text "Type" <+> text this <+> quotes (pp new) <+>
             text "shadows an existing" <+>
             text that <+> text "with the same name."



-- | The sub-computation is performed with the given type parameter in scope.
withTParam :: TParam -> InferM a -> InferM a
withTParam p (IM m) =
  do case tpName p of
       Just x  -> checkTShadowing "variable" x
       Nothing -> return ()
     IM $ mapReader (\r -> r { iTVars = p : iTVars r }) m

withTParams :: [TParam] -> InferM a -> InferM a
withTParams ps m = foldr withTParam m ps

-- | The sub-computation is performed with the given type-synonym in scope.
withTySyn :: TySyn -> InferM a -> InferM a
withTySyn t (IM m) =
  do let x = tsName t
     checkTShadowing "synonym" x
     IM $ mapReader (\r -> r { iTSyns = Map.insert x (IsLocal,t) (iTSyns r) }) m

withNewtype :: Newtype -> InferM a -> InferM a
withNewtype t (IM m) =
  IM $ mapReader
        (\r -> r { iNewtypes = Map.insert (ntName t) (IsLocal,t)
                                                     (iNewtypes r) }) m

-- | The sub-computation is performed with the given variable in scope.
withVarType :: QName -> VarType -> InferM a -> InferM a
withVarType x s (IM m) =
  IM $ mapReader (\r -> r { iVars = Map.insert x s (iVars r) }) m

withVarTypes :: [(QName,VarType)] -> InferM a -> InferM a
withVarTypes xs m = foldr (uncurry withVarType) m xs

withVar :: QName -> Schema -> InferM a -> InferM a
withVar x s = withVarType x (ExtVar s)


-- | The sub-computation is performed with the given variables in scope.
withMonoType :: (QName,Located Type) -> InferM a -> InferM a
withMonoType (x,lt) = withVar x (Forall [] [] (thing lt))

-- | The sub-computation is performed with the given variables in scope.
withMonoTypes :: Map QName (Located Type) -> InferM a -> InferM a
withMonoTypes xs m = foldr withMonoType m (Map.toList xs)

-- | The sub-computation is performed with the given type synonyms
-- and variables in scope.
withDecls :: ([TySyn], Map QName Schema) -> InferM a -> InferM a
withDecls (ts,vs) m = foldr withTySyn (foldr add m (Map.toList vs)) ts
  where
  add (x,t) = withVar x t

-- | Perform the given computation in a new scope (i.e., the subcomputation
-- may use existential type variables).
inNewScope :: InferM a -> InferM a
inNewScope m =
  do curScopes <- iExistTVars <$> IM get
     IM $ sets_ $ \s -> s { iExistTVars = Map.empty : curScopes }
     a <- m
     IM $ sets_ $ \s -> s { iExistTVars = curScopes }
     return a



--------------------------------------------------------------------------------
-- Kind checking


newtype KindM a = KM { unKM :: ReaderT KRO (StateT KRW InferM)  a }

data KRO = KRO { lazyTVars  :: Map QName Type -- ^ lazy map, with tyvars.
               , allowWild  :: Bool           -- ^ are type-wild cards allowed?
               }

data KRW = KRW { typeParams :: Map QName Kind -- ^ kinds of (known) vars.
               }

instance Functor KindM where
  fmap f (KM m) = KM (fmap f m)

instance A.Applicative KindM where
  pure  = return
  (<*>) = ap

instance Monad KindM where
  return x      = KM (return x)
  fail x        = KM (fail x)
  KM m >>= k    = KM (m >>= unKM . k)

{- | The arguments to this function are as follows:

(type param. name, kind signature (opt.), a type representing the param)

The type representing the parameter is just a thunk that we should not force.
The reason is that the type depnds on the kind of parameter, that we are
in the process of computing.

As a result we return the value of the sub-computation and the computed
kinds of the type parameters. -}
runKindM :: Bool                          -- Are type-wild cards allowed?
         -> [(QName, Maybe Kind, Type)]   -- ^ See comment
         -> KindM a -> InferM (a, Map QName Kind)
runKindM wildOK vs (KM m) =
  do (a,kw) <- runStateT krw (runReaderT kro m)
     return (a, typeParams kw)
  where
  tys  = Map.fromList [ (x,t) | (x,_,t)      <- vs ]
  kro  = KRO { allowWild = wildOK, lazyTVars = tys }
  krw  = KRW { typeParams = Map.fromList [ (x,k) | (x,Just k,_) <- vs ] }

-- | This is what's returned when we lookup variables during kind checking.
data LkpTyVar = TLocalVar Type (Maybe Kind) -- ^ Locally bound variable.
              | TOuterVar Type              -- ^ An outer binding.

-- | Check if a name refers to a type variable.
kLookupTyVar :: QName -> KindM (Maybe LkpTyVar)
kLookupTyVar x = KM $
  do vs <- lazyTVars `fmap` ask
     ss <- get
     case Map.lookup x vs of
       Just t  -> return $ Just $ TLocalVar t $ Map.lookup x $ typeParams ss
       Nothing -> lift $ lift $ do t <- lookupTVar x
                                   return (fmap TOuterVar t)

-- | Are type wild-cards OK in this context?
kWildOK :: KindM Bool
kWildOK = KM $ fmap allowWild ask

-- | Reports an error.
kRecordError :: Error -> KindM ()
kRecordError e = kInInferM $ recordError e

kRecordWarning :: Warning -> KindM ()
kRecordWarning w = kInInferM $ recordWarning w

-- | Generate a fresh unification variable of the given kind.
kNewType :: Doc -> Kind -> KindM Type
kNewType src k =
  do tps <- KM $ do vs <- asks lazyTVars
                    return $ Set.fromList [ tv | TVar tv <- Map.elems vs ]
     kInInferM $ TVar `fmap` newTVar' src tps k

-- | Lookup the definition of a type synonym.
kLookupTSyn :: QName -> KindM (Maybe TySyn)
kLookupTSyn x = kInInferM $ lookupTSyn x

-- | Lookup the definition of a newtype.
kLookupNewtype :: QName -> KindM (Maybe Newtype)
kLookupNewtype x = kInInferM $ lookupNewtype x

kExistTVar :: QName -> Kind -> KindM Type
kExistTVar x k = kInInferM $ existVar x k

-- | Replace the given bound variables with concrete types.
kInstantiateT :: Type -> [(TParam,Type)] -> KindM Type
kInstantiateT t as = return (apSubst su t)
  where su = listSubst [ (tpVar x, t1) | (x,t1) <- as ]

{- | Record the kind for a local type variable.
This assumes that we already checked that there was no other valid
kind for the variable (if there was one, it gets over-written). -}
kSetKind :: QName -> Kind -> KindM ()
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
kNewGoals c ps = kInInferM $ newGoals c ps

kInInferM :: InferM a -> KindM a
kInInferM m = KM $ lift $ lift m


