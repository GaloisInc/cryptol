-- |
-- Module      :  Cryptol.ModuleSystem.Renamer
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# Language RecordWildCards #-}
{-# Language FlexibleInstances #-}
{-# Language FlexibleContexts #-}
{-# Language BlockArguments #-}
{-# Language OverloadedStrings #-}
module Cryptol.ModuleSystem.Renamer (
    NamingEnv(), shadowing
  , BindsNames, InModule(..)
  , shadowNames
  , Rename(..), runRenamer, RenameM()
  , RenamerError(..)
  , RenamerWarning(..)
  , renameVar
  , renameType
  , renameModule
  , renameTopDecls
  , RenamerInfo(..)
  , NameType(..)
  , RenamedModule(..)
  ) where

import Prelude ()
import Prelude.Compat

import Data.Either(partitionEithers)
import Data.Maybe(fromJust,mapMaybe)
import Data.List(find,groupBy,sortBy)
import Data.Function(on)
import Data.Foldable(toList)
import Data.Map(Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Graph(SCC(..))
import Data.Graph.SCC(stronglyConnComp)
import MonadLib hiding (mapM, mapM_)


import Cryptol.ModuleSystem.Name
import Cryptol.ModuleSystem.Names
import Cryptol.ModuleSystem.NamingEnv
import Cryptol.ModuleSystem.Exports
import Cryptol.Parser.Position(getLoc,Range)
import Cryptol.Parser.AST
import Cryptol.Parser.Selector(selName)
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.RecordMap
import Cryptol.Utils.Ident(allNamespaces,OrigName(..))
import Cryptol.Utils.PP

import Cryptol.ModuleSystem.Interface
import Cryptol.ModuleSystem.Renamer.Error
import Cryptol.ModuleSystem.Binds
import Cryptol.ModuleSystem.Renamer.Monad
import Cryptol.ModuleSystem.Renamer.Imports
import Cryptol.ModuleSystem.Renamer.ImplicitImports


{-
The Renamer Algorithm
=====================

1. Add implicit imports for visible nested modules

2. Compute what each module defines   (see "Cryptol.ModuleSystem.Binds")
  - This assigns unique names to names introduces by various declarations
  - Here we detect repeated top-level definitions in a module.
  - Module instantiations also get a name, but are not yet resolved, so
    we don't know what's defined by them.
  - We do not generate unique names for functor parameters---those will
    be matched textually to the arguments when applied.
  - We *do* generate unique names for declarations in "signatures"
    * those are only really needed when renaming the signature (step 4)
      (e.g., to determine if a name refers to something declared in the
      signature or something else).
    * when validating a module against a signature the names of the declarations
      are matched textually, *not* using the unique names
      (e.g., `x` in a signature is matched with the thing named `x` in a module,
       even though these two `x`s will have different unique `id`s)


3. Resolve imports and instantiations (see "Cryptol.ModuleSystem.Imports")
  - Resolves names in submodule imports
  - Resolves functor instantiations:
    * generate new nemaes for delcarations in the functions.
    * this includes any nested modules, and things nested withing them.
  - At this point we have enough information to know what's exported by 
    each module

4. Do the renaming (this module)
  - Using step 3 we compute the scoping environment for each module/signature
  - We traverse all declarations and replace the parser names with the
    corresponding names in scope:
    * Here we detect ambiguity and undefined errors
    * During this pass is also where we keep track of infromation of what
      names are used by declarations:
      - this is used to compute the dependencies between declarations
      - which are in turn used to order the declarations in dependency order
        * this is assumed by the TC
        * here we also report errors about invalid recursive dependencies
    * During this stage we also issue warning about unused type names
      (and we should probably do unused value names too one day)
  - During the rewriting we also do:
    - rebalance expression trees using the operator fixities
    - desugar record update notation
-}


-- | The result of renaming a module
data RenamedModule = RenamedModule
  { rmModule   :: Module Name     -- ^ The renamed module
  , rmDefines  :: NamingEnv       -- ^ What this module defines
  , rmInScope  :: NamingEnv       -- ^ What's in scope in this module
  , rmImported :: IfaceDecls
    -- ^ Imported declarations.  This provides the types for external
    -- names (used by the type-checker).
  }

-- | Entry point. This is used for renaming a top-level module.
renameModule :: Module PName -> RenameM RenamedModule
renameModule m0 =
  do -- Step 1: add implicit imports
     let m = case mDef m0 of
               NormalModule ds ->
                 m0 { mDef = NormalModule (addImplicitNestedImports ds) }
               _ -> m0 -- XXX: OldStyleFunctor instnatiantions should
                       -- be translated into normal instantiations and
                       -- an anonymous module.

     -- Step 2: compute what's defined
     (defs,errs) <- liftSupply (modBuilder (topModuleDefs m))
     mapM_ recordError errs

     -- Step 3: resolve imports
     extern       <- getLoadedMods
     resolvedMods <- liftSupply (resolveImports extern defs)

     let pathToName = Map.fromList [ (nameModPath x, x)
                                   | ImpNested x <- Map.keys resolvedMods ]


     let mname = ImpTop (thing (mName m))

     setResolvedLocals resolvedMods $
       setNestedModule pathToName
       do (ifs,(inScope,m1)) <- collectIfaceDeps (renameModule' mname m)
          env <- rmodDefines <$> lookupResolved mname
          pure RenamedModule
                 { rmModule = m1
                 , rmDefines = env
                 , rmInScope = inScope
                 , rmImported = ifs
                  -- XXX: maybe we should keep the nested defines too?
                 }





{- | Entry point. Rename a list of top-level declarations.
This is used for declaration that don't live in a module
(e.g., define on the command line.)

We assume that these declarations do not contain any nested modules.
-}
renameTopDecls ::
  ModName -> [TopDecl PName] -> RenameM (NamingEnv,[TopDecl Name])
renameTopDecls m ds0 =

  do -- Step 1: add implicit importgs
     let ds = addImplicitNestedImports ds0

     -- Step 2: compute what's defined
     (defs,errs) <- liftSupply (modBuilder (topDeclsDefs ds))
     mapM_ recordError errs

     -- Step 3: resolve imports
     extern       <- getLoadedMods
     resolvedMods <- liftSupply (resolveImports extern (TopMod m defs))

     let pathToName = Map.fromList [ (nameModPath x, x)
                                   | ImpNested x <- Map.keys resolvedMods ]


     setResolvedLocals resolvedMods $
      setNestedModule pathToName
      do env    <- rmodDefines <$> lookupResolved (ImpTop m)

         -- we already checked for duplicates in Step 2
         ds1 <- shadowNames' CheckNone env (renameTopDecls' ds)
         -- record a use of top-level names to avoid
         -- unused name warnings
         let exports = exportedDecls ds1
         mapM_ recordUse (exported NSType exports)

         pure (env,ds1)

--------------------------------------------------------------------------------
-- Stuff below is related to Step 4 of the algorighm.


class Rename f where
  rename :: f PName -> RenameM (f Name)


-- | This is used for both top-level and nested modules.
-- Returns:
--
--    * Things defined in the module
--    * Renamed module
renameModule' ::
  ImpName Name {- ^ Resolved name for this module -} ->
  ModuleG mname PName ->
  RenameM (NamingEnv, ModuleG mname Name)
renameModule' mname m =
  setCurMod
    case mname of
      ImpTop r    -> TopModule r
      ImpNested r -> nameModPath r

  do resolved <- lookupResolved mname
     let env = rmodDefines resolved


     (inScope,newDef) <-
        shadowNames' CheckNone (rmodImports resolved)
        do (paramEnv,params) <-
                      shadowNames' CheckNone env (doModParams (mModParams m))

           shadowNames' CheckOverlap (env <> paramEnv) $
            -- we check that defined names and ones that came from parameters
            -- do not clash, as this would be very confusing.

             setModParams params
             do inScope <- getNamingEnv
                newDef <- case mDef m of
                            NormalModule ds ->
                              do ds1 <- renameTopDecls' ds
                                 let exports = exportedDecls ds1
                                 mapM_ recordUse (exported NSType exports)
                                 pure (NormalModule ds1)

                            FunctorInstance f as _ ->
                              do f'  <- rnLocated rename f
                                 as' <- rename as
                                 checkFunctorArgs as'

                                 let l = Just (srcRange f')
                                 imap <- mkInstMap l mempty (thing f') mname
                                 pure (FunctorInstance f' as' imap)

                            FunctorInstanceOld f ds ->
                              FunctorInstanceOld f <$> renameTopDecls' ds

                pure (inScope, newDef)
     return (inScope, m { mDef = newDef })

checkFunctorArgs :: ModuleInstanceArgs Name -> RenameM ()
checkFunctorArgs args =
  case args of
    DefaultInstArg l -> checkIsModule (srcRange l) (thing l)
    NamedInstArgs as -> mapM_ checkArg as
  where
  checkArg (ModuleInstanceArg _ l) = checkIsModule (srcRange l) (thing l)

mkInstMap :: Maybe Range -> Map Name Name -> ImpName Name -> ImpName Name ->
  RenameM (Map Name Name)
mkInstMap checkFun acc0 ogname iname =
  do (onames,osubs) <- lookupDefinesAndSubs checkFun ogname
     inames         <- lookupDefines iname
     let mp   = zipByTextName onames inames
         subs = [ (ImpNested k, ImpNested v)
                | k <- Set.toList osubs, Just v <- [Map.lookup k mp]
                ]
     foldM doSub (Map.union mp acc0) subs

  where
  doSub acc (k,v) = mkInstMap Nothing acc k v




-- | This is used to rename local declarations (e.g. `where`)
renameDecls :: [Decl PName] -> RenameM [Decl Name]
renameDecls ds =
  do (ds1,deps) <- depGroup (traverse rename ds)
     let toNode d = let x = NamedThing (declName d)
                    in ((d,x), x, map NamedThing
                            $ Set.toList
                            $ Map.findWithDefault Set.empty x deps)
         ordered = toList (stronglyConnComp (map toNode ds1))
         fromSCC x =
           case x of
             AcyclicSCC (d,_) -> pure [d]
             CyclicSCC ds_xs ->
               let (rds,xs) = unzip ds_xs
               in case mapM validRecursiveD rds of
                    Nothing -> do recordError (InvalidDependency xs)
                                  pure rds
                    Just bs ->
                      do checkSameModule xs
                         pure [DRec bs]
     concat <$> mapM fromSCC ordered


validRecursiveD :: Decl name -> Maybe (Bind name)
validRecursiveD d =
  case d of
    DBind b       -> Just b
    DLocated d' _ -> validRecursiveD d'
    _             -> Nothing

checkSameModule :: [DepName] -> RenameM ()
checkSameModule xs =
  case ms of
    a : as | let bad = [ fst b | b <- as, snd a /= snd b ]
           , not (null bad) ->
              recordError (InvalidDependency $ map NamedThing $ fst a : bad)
    _ -> pure ()
  where
  ms = [ (x,ogModule og)
       | NamedThing x <- xs, GlobalName _ og <- [ nameInfo x ]
       ]



{- NOTE: Dependincies on Top Level Constraints
   ===========================================

For the new module system, things using a parameter depend on the parameter
declaration (i.e., `import signature`), which depends on the signature,
so dependencies on constraints in there should be OK.

However, we'd like to have a mechanism for declaring top level constraints in
a functor, that can impose constraints across types from *different*
parameters.  For the moment, we reuse `parameter type constrint C` for this.

Such constraints need to be:
  1. After the signature import
  2. After any type synonyms/newtypes using the parameters
  3. Before any value or type declarations that need to use the parameters.

Note that type declarations used by a constraint cannot use the constraint,
so they need to be well formed without it.

For other types, we use the following rule to determine if they use a
constraint:

  If:
    1. We have a constraint and type declaration
    2. They both mention the same type parameter
    3. There is no explicit dependency of the constraint on the DECL
  Then:
    The type declaration depends on the constraint.

Example:

  type T = 10             // Does not depend on anything so can go first

  signature A where
    type n : #

  import signature A     // Depends on A, so need to be after A

  parameter type constraint n > T
                        // Depends on the import (for @n@) and T

  type Q = [n-T]        // Depends on the top-level constraint
-}



-- This assumes imports have already been processed
renameTopDecls' :: [TopDecl PName] -> RenameM [TopDecl Name]
renameTopDecls' ds =
  do -- rename and compute what names we depend on
     (ds1,deps) <- depGroup (traverse rename ds)

     fromParams <- getNamesFromModParams
     let rawDepsFor x = Map.findWithDefault Set.empty x deps

         isTyParam x = nameNamespace x == NSType && x `Map.member` fromParams


         (noNameDs,nameDs) = partitionEithers (map topDeclName ds1)
         ctrs = [ nm | (_,nm@(ConstratintAt {})) <- nameDs ]


         {- See [NOTE: Dependincies on Top Level Constraints] -}
         addCtr nm ctr =
            case nm of
              NamedThing x
                | nameNamespace x == NSType
                , let ctrDeps = rawDepsFor ctr
                      tyDeps  = rawDepsFor nm
                , not (x `Set.member` ctrDeps)
                , not (Set.null (Set.intersection
                                      (Set.filter isTyParam ctrDeps)
                                      (Set.filter isTyParam tyDeps)))
                  -> Just ctr
              _ -> Nothing

         addCtrs (d,x)
          | usesCtrs d = ctrs
          | otherwise  = mapMaybe (addCtr x) ctrs

         mkDepName x = case Map.lookup x fromParams of
                         Just dn -> dn
                         Nothing -> NamedThing x

         toNode (d,x) = ((d,x),x, addCtrs (d,x) ++
                               map mkDepName
                             ( Set.toList
                             ( Map.findWithDefault Set.empty x deps) ))

         ordered = stronglyConnComp (map toNode nameDs)
         fromSCC x =
            case x of
              AcyclicSCC (d,_) -> pure [d]
              CyclicSCC ds_xs ->
                let (rds,xs) = unzip ds_xs
                in case mapM valid rds of
                     Nothing -> do recordError (InvalidDependency xs)
                                   pure rds
                     Just bs ->
                       do checkSameModule xs
                          pure [Decl TopLevel
                                       { tlDoc = Nothing
                                       , tlExport = Public
                                       , tlValue = DRec bs
                                       }]
                where
                valid d = case d of
                            Decl tl -> validRecursiveD (tlValue tl)
                            _       -> Nothing
     rds <- mapM fromSCC ordered
     pure (concat (noNameDs:rds))
  where

  -- This indicates if a declaration might depend on the constraints in scope.
  -- Since uses of contraints are not implicitly named, value declarations
  -- are assumed to potentially use the constraints.

  -- XXX: This is inacurate, and *I think* it amounts to checking that something
  -- is in the value namespace.   Perhaps the rule should be that a value
  -- depends on a parameter constraint if it mentiones at least one
  -- type parameter somewhere.
  usesCtrs td =
    case td of
      Decl tl                 -> isValDecl (tlValue tl)
      DPrimType {}            -> False
      TDNewtype {}            -> False
      DParameterType {}       -> False
      DParameterConstraint {} -> False

      DParameterFun {}        -> True
      -- Here we may need the constraints to validate the type
      -- (e.g., if the parameter is of type `Z a`)


      DModule tl              -> any usesCtrs (mDecls m)
        where NestedModule m = tlValue tl
      DImport {}              -> False
      DModSig {}              -> False    -- no definitions here
      DModParam {}            -> False    -- no definitions here
      Include {}              -> bad "Include"

  isValDecl d =
    case d of
      DLocated d' _ -> isValDecl d'
      DBind {}      -> True
      DRec {}       -> True

      DType {}      -> False
      DProp {}      -> False

      DSignature {} -> bad "DSignature"
      DFixity {}    -> bad "DFixity"
      DPragma {}    -> bad "DPragma"
      DPatBind {}   -> bad "DPatBind"

  bad msg = panic "renameTopDecls'" [msg]


declName :: Decl Name -> Name
declName decl =
  case decl of
    DLocated d _            -> declName d
    DBind b                 -> thing (bName b)
    DType (TySyn x _ _ _)   -> thing x
    DProp (PropSyn x _ _ _) -> thing x

    DSignature {}           -> bad "DSignature"
    DFixity {}              -> bad "DFixity"
    DPragma {}              -> bad "DPragma"
    DPatBind {}             -> bad "DPatBind"
    DRec {}                 -> bad "DRec"
  where
  bad x = panic "declName" [x]

topDeclName :: TopDecl Name -> Either (TopDecl Name) (TopDecl Name, DepName)
topDeclName topDecl =
  case topDecl of
    Decl d                  -> hasName (declName (tlValue d))
    DPrimType d             -> hasName (thing (primTName (tlValue d)))
    TDNewtype d             -> hasName (thing (nName (tlValue d)))
    DParameterType d        -> hasName (thing (ptName d))
    DParameterFun d         -> hasName (thing (pfName d))
    DModule d               -> hasName (thing (mName m))
      where NestedModule m = tlValue d

    DModSig d               -> hasName (thing (sigName (tlValue d)))

    DParameterConstraint ds ->
      case ds of
        []  -> noName
        _   -> Right (topDecl, ConstratintAt (fromJust (getLoc ds)))
    DImport {}              -> noName

    DModParam m             -> Right ( topDecl
                                     , ModParamName (srcRange (mpSignature m))
                                                    (mpName m))

    Include {}              -> bad "Include"
  where
  noName    = Left topDecl
  hasName n = Right (topDecl, NamedThing n)
  bad x     = panic "topDeclName" [x]




{- | Compute the names introduced by a module parameter.
This should be run in a context containg everything that's in scope
except for the module parameters.  We don't need to compute a fixed point here
because the signatures (and hence module parameters) cannot contain signatures.

The resulting naming environment contains the new names introduced by this
parameter.
-}
doModParam ::
  ModParam PName ->
  RenameM (NamingEnv, RenModParam)
doModParam mp =
  do let sigName = mpSignature mp
         loc     = srcRange sigName
     withLoc loc
       do nm <- resolveName NameUse NSSignature (thing sigName)
          sigEnv <- lookupDefines (ImpNested nm)
          me <- getCurMod
          let newP x = do y <- lift (newModParam me (mpName mp) loc x)
                          sets_ (Map.insert y x)
                          pure y
          (newEnv',nameMap) <- runStateT Map.empty (travNamingEnv newP sigEnv)
          let paramName = mpAs mp
          let newEnv = case paramName of
                         Nothing -> newEnv'
                         Just q  -> qualify q newEnv'
          pure ( newEnv
               , RenModParam
                 { renModParamName     = mpName mp
                 , renModParamRange    = loc
                 , renModParamSig      = nm
                 , renModParamInstance = nameMap
                 }
               )

{- | Process the parameters of a module.
Should be executed in a context where everything's already in the context,
except the module parameters.
-}
doModParams :: [ModParam PName] -> RenameM (NamingEnv, [RenModParam])
doModParams srcParams =
  do (paramEnvs,params) <- unzip <$> mapM doModParam  srcParams

     let repeated = groupBy ((==) `on` renModParamName)
                  $ sortBy (compare `on` renModParamName) params

     forM_ repeated \ps ->
       case ps of
         [_]      -> pure ()
         ~(p : _) -> recordError (MultipleModParams (renModParamName p)
                                                    (map renModParamRange ps))

     pure (mconcat paramEnvs,params)




--------------------------------------------------------------------------------

rnLocated :: (a -> RenameM b) -> Located a -> RenameM (Located b)
rnLocated f loc = withLoc loc $
  do a' <- f (thing loc)
     return loc { thing = a' }






instance Rename TopDecl where
  rename td =
    case td of
      Decl d            -> Decl      <$> traverse rename d
      DPrimType d       -> DPrimType <$> traverse rename d
      TDNewtype n       -> TDNewtype <$> traverse rename n
      Include n         -> return (Include n)
      DParameterFun f   -> DParameterFun  <$> rename f
      DParameterType f  -> DParameterType <$> rename f

      DParameterConstraint ds ->
        case ds of
          [] -> pure (DParameterConstraint [])
          _  -> depsOf (ConstratintAt (fromJust (getLoc ds)))
              $ DParameterConstraint <$> mapM (rnLocated rename) ds

      DModule m  -> DModule <$> traverse rename m
      DImport li -> DImport <$> traverse renI li
        where
        renI i = do m <- rename (iModule i)
                    recordImport m
                    pure i { iModule = m }

      DModParam mp -> DModParam <$> rename mp
      DModSig sig -> DModSig <$> traverse rename sig

instance Rename ModParam where
  rename mp =
    depsOf (ModParamName (srcRange (mpSignature mp)) (mpName mp))
    do x   <- rnLocated (resolveName NameUse NSSignature) (mpSignature mp)
       ren <- renModParamInstance <$> getModParam (mpName mp)

       {- Here we add a single "use" to all type-level names intorduced,
       because this is their binding site.   The warnings for unused names
       are reported for names with a single "use" (i.e., the binding site)
       so if we don't add the bindg site use, we get incorrect warnings -}
       mapM_ recordUse [ t | t <- Map.keys ren, nameNamespace t == NSType ]

       pure mp { mpSignature = x, mpRenaming = ren }

instance Rename Signature where
  rename sig =
    do let pname = thing (sigName sig)
       nm <- resolveName NameBind NSSignature pname
       env <- rmodDefines <$> lookupResolved (ImpNested nm)
       shadowNames' CheckOverlap env $
          depsOf (NamedThing nm)
          do tps <- traverse rename (sigTypeParams sig)
             cts <- traverse (traverse rename) (sigConstraints sig)
             fun <- traverse rename (sigFunParams sig)
             pure Signature
                    { sigName = (sigName sig) { thing = nm }
                    , sigTypeParams = tps
                    , sigConstraints = cts
                    , sigFunParams = fun
                    }

instance Rename ImpName where
  rename i =
    case i of
      ImpTop m -> pure (ImpTop m)
      ImpNested m -> ImpNested <$> resolveName NameUse NSModule m

instance Rename ModuleInstanceArgs where
  rename args =
    case args of
      DefaultInstArg a -> DefaultInstArg <$> rnLocated rename a
      NamedInstArgs xs -> NamedInstArgs  <$> traverse rename xs

instance Rename ModuleInstanceArg where
  rename (ModuleInstanceArg x m) =
    ModuleInstanceArg x <$> rnLocated rename m


instance Rename NestedModule where
  rename (NestedModule m) =
    do let lnm            = mName m
           nm             = thing lnm
       n   <- resolveName NameBind NSModule nm
       depsOf (NamedThing n)
         do -- XXX: we should store in scope somehwere if we want to browse
            -- nested modules properly
            let m' = m { mName = ImpNested <$> mName m }
            (_inScope,m1) <- renameModule' (ImpNested n) m'
            pure (NestedModule m1 { mName = lnm { thing = n } })


instance Rename PrimType where
  rename pt =
    do x <- rnLocated (renameType NameBind) (primTName pt)
       depsOf (NamedThing (thing x))
         do let (as,ps) = primTCts pt
            (_,cts) <- renameQual as ps $ \as' ps' -> pure (as',ps')

            -- Record an additional use for each parameter since we checked
            -- earlier that all the parameters are used exactly once in the
            -- body of the signature.  This prevents incorret warnings
            -- about unused names.
            mapM_ (recordUse . tpName) (fst cts)

            pure pt { primTCts = cts, primTName = x }

instance Rename ParameterType where
  rename a =
    do n' <- rnLocated (renameType NameBind) (ptName a)
       return a { ptName = n' }

instance Rename ParameterFun where
  rename a =
    do n'   <- rnLocated (renameVar NameBind) (pfName a)
       depsOf (NamedThing (thing n'))
         do sig' <- renameSchema (pfSchema a)
            return a { pfName = n', pfSchema = snd sig' }

instance Rename Decl where
  rename d      = case d of
    DBind b           -> DBind <$> rename b

    DType syn         -> DType         <$> rename syn
    DProp syn         -> DProp         <$> rename syn
    DLocated d' r     -> withLoc r
                       $ DLocated      <$> rename d'  <*> pure r

    DFixity{}         -> panic "rename" [ "DFixity" ]
    DSignature {}     -> panic "rename" [ "DSignature" ]
    DPragma  {}       -> panic "rename" [ "DPragma" ]
    DPatBind {}       -> panic "rename" [ "DPatBind " ]
    DRec {}           -> panic "rename" [ "DRec" ]



instance Rename Newtype where
  rename n      =
    shadowNames (nParams n) $
    do name' <- rnLocated (renameType NameBind) (nName n)
       depsOf (NamedThing (thing name')) $
         do ps'   <- traverse rename (nParams n)
            body' <- traverse (traverse rename) (nBody n)
            return Newtype { nName   = name'
                           , nParams = ps'
                           , nBody   = body' }



-- | Try to resolve a name
resolveNameMaybe :: NameType -> Namespace -> PName -> RenameM (Maybe Name)
resolveNameMaybe nt expected qn =
  do ro <- RenameM ask
     let lkpIn here = Map.lookup qn (namespaceMap here (roNames ro))
         use = case expected of
                 NSType -> recordUse
                 _      -> const (pure ())
     case lkpIn expected of
       Just xs ->
         case xs of
          One n ->
            do case nt of
                 NameBind -> pure ()
                 NameUse  -> addDep n
               use n    -- for warning
               return (Just n)
          Ambig symSet ->
            do let syms = Set.toList symSet
               mapM_ use syms    -- mark as used to avoid unused warnings
               n <- located qn
               recordError (MultipleSyms n syms)
               return (Just (head syms))

       Nothing -> pure Nothing

-- | Resolve a name, and report error on failure
resolveName :: NameType -> Namespace -> PName -> RenameM Name
resolveName nt expected qn =
  do mb <- resolveNameMaybe nt expected qn
     case mb of
       Just n -> pure n
       Nothing ->
         do ro <- RenameM ask
            let lkpIn here = Map.lookup qn (namespaceMap here (roNames ro))
                others     = [ ns | ns <- allNamespaces
                                  , ns /= expected
                                  , Just _ <- [lkpIn ns] ]
            nm <- located qn
            case others of
              -- name exists in a different namespace
              actual : _ -> recordError (WrongNamespace expected actual nm)

              -- the value is just missing
              [] -> recordError (UnboundName expected nm)

            mkFakeName expected qn


renameVar :: NameType -> PName -> RenameM Name
renameVar nt = resolveName nt NSValue

renameType :: NameType -> PName -> RenameM Name
renameType nt = resolveName nt NSType



-- | Assuming an error has been recorded already, construct a fake name that's
-- not expected to make it out of the renamer.
mkFakeName :: Namespace -> PName -> RenameM Name
mkFakeName ns pn =
  do ro <- RenameM ask
     liftSupply (mkLocal ns (getIdent pn) (roLoc ro))

-- | Rename a schema, assuming that none of its type variables are already in
-- scope.
instance Rename Schema where
  rename s = snd `fmap` renameSchema s

-- | Rename a schema, assuming that the type variables have already been brought
-- into scope.
renameSchema :: Schema PName -> RenameM (NamingEnv,Schema Name)
renameSchema (Forall ps p ty loc) =
  renameQual ps p $ \ps' p' ->
    do ty' <- rename ty
       pure (Forall ps' p' ty' loc)

-- | Rename a qualified thing.
renameQual :: [TParam PName] -> [Prop PName] ->
              ([TParam Name] -> [Prop Name] -> RenameM a) ->
              RenameM (NamingEnv, a)
renameQual as ps k =
  do env <- liftSupply (defsOf as)
     res <- shadowNames env $ do as' <- traverse rename as
                                 ps' <- traverse rename ps
                                 k as' ps'
     pure (env,res)

instance Rename TParam where
  rename TParam { .. } =
    do n <- renameType NameBind tpName
       return TParam { tpName = n, .. }

instance Rename Prop where
  rename (CType t) = CType <$> rename t


instance Rename Type where
  rename ty0 =
    case ty0 of
      TFun a b       -> TFun <$> rename a <*> rename b
      TSeq n a       -> TSeq <$> rename n <*> rename a
      TBit           -> return TBit
      TNum c         -> return (TNum c)
      TChar c        -> return (TChar c)
      TUser qn ps    -> TUser <$> renameType NameUse qn <*> traverse rename ps
      TTyApp fs      -> TTyApp   <$> traverse (traverse rename) fs
      TRecord fs     -> TRecord  <$> traverse (traverse rename) fs
      TTuple fs      -> TTuple   <$> traverse rename fs
      TWild          -> return TWild
      TLocated t' r  -> withLoc r (TLocated <$> rename t' <*> pure r)
      TParens t'     -> TParens <$> rename t'
      TInfix a o _ b -> do o' <- renameTypeOp o
                           a' <- rename a
                           b' <- rename b
                           mkTInfix a' o' b'

mkTInfix ::
  Type Name -> (Located Name, Fixity) -> Type Name -> RenameM (Type Name)

mkTInfix t@(TInfix x o1 f1 y) op@(o2,f2) z =
  case compareFixity f1 f2 of
    FCLeft  -> return (TInfix t o2 f2 z)
    FCRight -> do r <- mkTInfix y op z
                  return (TInfix x o1 f1 r)
    FCError -> do recordError (FixityError o1 f1 o2 f2)
                  return (TInfix t o2 f2 z)

mkTInfix (TLocated t' _) op z =
  mkTInfix t' op z

mkTInfix t (o,f) z =
  return (TInfix t o f z)


-- | Rename a binding.
instance Rename Bind where
  rename b =
    do n'    <- rnLocated (renameVar NameBind) (bName b)
       depsOf (NamedThing (thing n'))
         do mbSig <- traverse renameSchema (bSignature b)
            shadowNames (fst `fmap` mbSig) $
              do (patEnv,pats') <- renamePats (bParams b)
                 -- NOTE: renamePats will generate warnings,
                 -- so we don't need to trigger them again here.
                 e' <- shadowNames' CheckNone patEnv (rnLocated rename (bDef b))
                 return b { bName      = n'
                          , bParams    = pats'
                          , bDef       = e'
                          , bSignature = snd `fmap` mbSig
                          , bPragmas   = bPragmas b
                          }

instance Rename BindDef where
  rename DPrim     = return DPrim
  rename (DExpr e) = DExpr <$> rename e

-- NOTE: this only renames types within the pattern.
instance Rename Pattern where
  rename p      = case p of
    PVar lv         -> PVar <$> rnLocated (renameVar NameBind) lv
    PWild           -> pure PWild
    PTuple ps       -> PTuple   <$> traverse rename ps
    PRecord nps     -> PRecord  <$> traverse (traverse rename) nps
    PList elems     -> PList    <$> traverse rename elems
    PTyped p' t     -> PTyped   <$> rename p'    <*> rename t
    PSplit l r      -> PSplit   <$> rename l     <*> rename r
    PLocated p' loc -> withLoc loc
                     $ PLocated <$> rename p'    <*> pure loc

-- | Note that after this point the @->@ updates have an explicit function
-- and there are no more nested updates.
instance Rename UpdField where
  rename (UpdField h ls e) =
    -- The plan:
    -- x =  e       ~~~>        x = e
    -- x -> e       ~~~>        x -> \x -> e
    -- x.y = e      ~~~>        x -> { _ | y = e }
    -- x.y -> e     ~~~>        x -> { _ | y -> e }
    case ls of
      l : more ->
       case more of
         [] -> case h of
                 UpdSet -> UpdField UpdSet [l] <$> rename e
                 UpdFun -> UpdField UpdFun [l] <$>
                                        rename (EFun emptyFunDesc [PVar p] e)
                       where
                       p = UnQual . selName <$> last ls
         _ -> UpdField UpdFun [l] <$> rename (EUpd Nothing [ UpdField h more e])
      [] -> panic "rename@UpdField" [ "Empty label list." ]


instance Rename FunDesc where
  rename (FunDesc nm offset) =
    do nm' <- traverse (renameVar NameBind)  nm
       pure (FunDesc nm' offset)

instance Rename Expr where
  rename expr = case expr of
    EVar n          -> EVar <$> renameVar NameUse n
    ELit l          -> return (ELit l)
    ENeg e          -> ENeg    <$> rename e
    EComplement e   -> EComplement
                               <$> rename e
    EGenerate e     -> EGenerate
                               <$> rename e
    ETuple es       -> ETuple  <$> traverse rename es
    ERecord fs      -> ERecord <$> traverse (traverse rename) fs
    ESel e' s       -> ESel    <$> rename e' <*> pure s
    EUpd mb fs      -> do checkLabels fs
                          EUpd <$> traverse rename mb <*> traverse rename fs
    EList es        -> EList   <$> traverse rename es
    EFromTo s n e t -> EFromTo <$> rename s
                               <*> traverse rename n
                               <*> rename e
                               <*> traverse rename t
    EFromToBy isStrict s e b t ->
                       EFromToBy isStrict
                                 <$> rename s
                                 <*> rename e
                                 <*> rename b
                                 <*> traverse rename t
    EFromToDownBy isStrict s e b t ->
                       EFromToDownBy isStrict
                                 <$> rename s
                                 <*> rename e
                                 <*> rename b
                                 <*> traverse rename t
    EFromToLessThan s e t ->
                       EFromToLessThan <$> rename s
                                       <*> rename e
                                       <*> traverse rename t
    EInfFrom a b    -> EInfFrom<$> rename a  <*> traverse rename b
    EComp e' bs     -> do arms' <- traverse renameArm bs
                          let (envs,bs') = unzip arms'
                          -- NOTE: renameArm will generate shadowing warnings; we only
                          -- need to check for repeated names across multiple arms
                          shadowNames' CheckOverlap envs (EComp <$> rename e' <*> pure bs')
    EApp f x        -> EApp    <$> rename f  <*> rename x
    EAppT f ti      -> EAppT   <$> rename f  <*> traverse rename ti
    EIf b t f       -> EIf     <$> rename b  <*> rename t  <*> rename f
    EWhere e' ds    -> shadowNames (map (InModule Nothing) ds) $
                          EWhere <$> rename e' <*> renameDecls ds
    ETyped e' ty    -> ETyped  <$> rename e' <*> rename ty
    ETypeVal ty     -> ETypeVal<$> rename ty
    EFun desc ps e' -> do desc' <- rename desc
                          (env,ps') <- renamePats ps
                          -- NOTE: renamePats will generate warnings, so we don't
                          -- need to duplicate them here
                          shadowNames' CheckNone env (EFun desc' ps' <$> rename e')
    ELocated e' r   -> withLoc r
                     $ ELocated <$> rename e' <*> pure r

    ESplit e        -> ESplit  <$> rename e
    EParens p       -> EParens <$> rename p
    EInfix x y _ z  -> do op <- renameOp y
                          x' <- rename x
                          z' <- rename z
                          mkEInfix x' op z'


checkLabels :: [UpdField PName] -> RenameM ()
checkLabels = foldM_ check [] . map labs
  where
  labs (UpdField _ ls _) = ls

  check done l =
    do case find (overlap l) done of
         Just l' -> recordError (OverlappingRecordUpdate (reLoc l) (reLoc l'))
         Nothing -> pure ()
       pure (l : done)

  overlap xs ys =
    case (xs,ys) of
      ([],_)  -> True
      (_, []) -> True
      (x : xs', y : ys') -> same x y && overlap xs' ys'

  same x y =
    case (thing x, thing y) of
      (TupleSel a _, TupleSel b _)   -> a == b
      (ListSel  a _, ListSel  b _)   -> a == b
      (RecordSel a _, RecordSel b _) -> a == b
      _                              -> False

  reLoc xs = (head xs) { thing = map thing xs }


mkEInfix :: Expr Name             -- ^ May contain infix expressions
         -> (Located Name,Fixity) -- ^ The operator to use
         -> Expr Name             -- ^ Will not contain infix expressions
         -> RenameM (Expr Name)

mkEInfix e@(EInfix x o1 f1 y) op@(o2,f2) z =
   case compareFixity f1 f2 of
     FCLeft  -> return (EInfix e o2 f2 z)

     FCRight -> do r <- mkEInfix y op z
                   return (EInfix x o1 f1 r)

     FCError -> do recordError (FixityError o1 f1 o2 f2)
                   return (EInfix e o2 f2 z)

mkEInfix (ELocated e' _) op z =
     mkEInfix e' op z

mkEInfix e (o,f) z =
     return (EInfix e o f z)


renameOp :: Located PName -> RenameM (Located Name, Fixity)
renameOp ln =
  withLoc ln $
  do n <- renameVar NameUse (thing ln)
     fixity <- lookupFixity n
     return (ln { thing = n }, fixity)

renameTypeOp :: Located PName -> RenameM (Located Name, Fixity)
renameTypeOp ln =
  withLoc ln $
  do n <- renameType NameUse (thing ln)
     fixity <- lookupFixity n
     return (ln { thing = n }, fixity)

lookupFixity :: Name -> RenameM Fixity
lookupFixity n =
  case nameFixity n of
    Just fixity -> return fixity
    Nothing     -> return defaultFixity -- FIXME: should we raise an error instead?

instance Rename TypeInst where
  rename ti = case ti of
    NamedInst nty -> NamedInst <$> traverse rename nty
    PosInst ty    -> PosInst   <$> rename ty

renameArm :: [Match PName] -> RenameM (NamingEnv,[Match Name])

renameArm (m:ms) =
  do (me,m') <- renameMatch m
     -- NOTE: renameMatch will generate warnings, so we don't
     -- need to duplicate them here
     shadowNames' CheckNone me $
       do (env,rest) <- renameArm ms

          -- NOTE: the inner environment shadows the outer one, for examples
          -- like this:
          --
          -- [ x | x <- xs, let x = 10 ]
          return (env `shadowing` me, m':rest)

renameArm [] =
     return (mempty,[])

-- | The name environment generated by a single match.
renameMatch :: Match PName -> RenameM (NamingEnv,Match Name)

renameMatch (Match p e) =
  do (pe,p') <- renamePat p
     e'      <- rename e
     return (pe,Match p' e')

renameMatch (MatchLet b) =
  do be <- liftSupply (defsOf (InModule Nothing b))
     b' <- shadowNames be (rename b)
     return (be,MatchLet b')

-- | Rename patterns, and collect the new environment that they introduce.
renamePat :: Pattern PName -> RenameM (NamingEnv, Pattern Name)
renamePat p =
  do pe <- patternEnv p
     p' <- shadowNames pe (rename p)
     return (pe, p')



-- | Rename patterns, and collect the new environment that they introduce.
renamePats :: [Pattern PName] -> RenameM (NamingEnv,[Pattern Name])
renamePats  = loop
  where
  loop ps = case ps of

    p:rest -> do
      pe <- patternEnv p
      shadowNames pe $
        do p'           <- rename p
           (env',rest') <- loop rest
           return (pe `mappend` env', p':rest')

    [] -> return (mempty, [])

patternEnv :: Pattern PName -> RenameM NamingEnv
patternEnv  = go
  where
  go (PVar Located { .. }) =
    do n <- liftSupply (mkLocal NSValue (getIdent thing) srcRange)
       -- XXX: for deps, we should record a use
       return (singletonNS NSValue thing n)

  go PWild            = return mempty
  go (PTuple ps)      = bindVars ps
  go (PRecord fs)     = bindVars (fmap snd (recordElements fs))
  go (PList ps)       = foldMap go ps
  go (PTyped p ty)    = go p `mappend` typeEnv ty
  go (PSplit a b)     = go a `mappend` go b
  go (PLocated p loc) = withLoc loc (go p)

  bindVars []     = return mempty
  bindVars (p:ps) =
    do env <- go p
       shadowNames env $
         do rest <- bindVars ps
            return (env `mappend` rest)


  typeEnv (TFun a b) = bindTypes [a,b]
  typeEnv (TSeq a b) = bindTypes [a,b]

  typeEnv TBit       = return mempty
  typeEnv TNum{}     = return mempty
  typeEnv TChar{}    = return mempty

  typeEnv (TUser pn ps) =
    do mb <- resolveNameMaybe NameUse NSType pn
       case mb of

         -- The type is already bound, don't introduce anything.
         Just _ -> bindTypes ps

         Nothing

           -- The type isn't bound, and has no parameters, so it names a portion
           -- of the type of the pattern.
           | null ps ->
             do loc <- curLoc
                n   <- liftSupply (mkLocal NSType (getIdent pn) loc)
                return (singletonNS NSType pn n)

           -- This references a type synonym that's not in scope. Record an
           -- error and continue with a made up name.
           | otherwise ->
             do loc <- curLoc
                recordError (UnboundName NSType (Located loc pn))
                n   <- liftSupply (mkLocal NSType (getIdent pn) loc)
                return (singletonNS NSType pn n)

  typeEnv (TRecord fs)      = bindTypes (map snd (recordElements fs))
  typeEnv (TTyApp fs)       = bindTypes (map value fs)
  typeEnv (TTuple ts)       = bindTypes ts
  typeEnv TWild             = return mempty
  typeEnv (TLocated ty loc) = withLoc loc (typeEnv ty)
  typeEnv (TParens ty)      = typeEnv ty
  typeEnv (TInfix a _ _ b)  = bindTypes [a,b]

  bindTypes [] = return mempty
  bindTypes (t:ts) =
    do env' <- typeEnv t
       shadowNames env' $
         do res <- bindTypes ts
            return (env' `mappend` res)


instance Rename Match where
  rename m = case m of
    Match p e  ->                  Match    <$> rename p <*> rename e
    MatchLet b -> shadowNames (InModule Nothing b) (MatchLet <$> rename b)

instance Rename TySyn where
  rename (TySyn n f ps ty) =
    shadowNames ps
    do n' <- rnLocated (renameType NameBind) n
       depsOf (NamedThing (thing n')) $
         TySyn n' <$> pure f <*> traverse rename ps <*> rename ty

instance Rename PropSyn where
  rename (PropSyn n f ps cs) =
    shadowNames ps
    do n' <- rnLocated (renameType NameBind) n
       PropSyn n' <$> pure f <*> traverse rename ps <*> traverse rename cs

--------------------------------------------------------------------------------

instance PP RenamedModule where
  ppPrec _ rn = updPPCfg (\cfg -> cfg { ppcfgShowNameUniques = True }) doc
    where
    doc =
      vcat [ "// --- Defines -----------------------------"
           , pp (rmDefines rn)
           , "// --- In scope ----------------------------"
           , pp (rmInScope rn)
           , "// -- Module -------------------------------"
           , pp (rmModule rn)
           , "// -----------------------------------------"
           ]


