{-# Language BlockArguments, BangPatterns, ImportQualifiedPost, OverloadedStrings #-}
{-# LANGUAGE InstanceSigs #-}
module Cryptol.ModuleSystem.Renamer (
    NamingEnv(), shadowing
  , BindsNames, InModule(..)
  -- , shadowNames
  , Rename(..), runRenamer, RenameM()
  , RenamerError(..)
  , RenamerWarning(..)
  , resolveNameUse
  , renameModule
  , renameTopDecls
  , RenamerInfo(..)
  , RenamedModule(..)
  ) where

-- import Debug.Trace

import Data.List(partition,foldl',find)
import Data.Maybe(mapMaybe)
import Data.Either(partitionEithers)
import Data.Set(Set)
import Data.Set qualified as Set
import Data.Map qualified as Map
import Control.Monad(forM,mapAndUnzipM,foldM_)
import Data.Graph(SCC(..), graphFromEdges', flattenSCC)
import Data.Graph.SCC(sccGraph, stronglyConnComp)

import Cryptol.Utils.Panic(panic)
import Cryptol.Utils.Ident
import Cryptol.Utils.PP
import Cryptol.Parser.Position
import Cryptol.Parser.Selector
import Cryptol.Parser.AST
import Cryptol.ModuleSystem.Name
import Cryptol.ModuleSystem.NamingEnv
import Cryptol.ModuleSystem.Interface
import Cryptol.ModuleSystem.Binds(defsOf, defsOfSig, InModule(..), newFunctorInst, newModParam, BindsNames)
import Cryptol.ModuleSystem.Names
import Cryptol.ModuleSystem.Renamer.Error
import Cryptol.ModuleSystem.Renamer.Monad

-- | The result of renaming a module
data RenamedModule = RenamedModule
  { rmModule   :: Module Name     -- ^ The renamed module
  , rmDefines  :: NamingEnv       -- ^ What this module defines
  , rmImported :: IfaceDecls
    -- ^ Imported declarations.  This provides the types for external
    -- names (used by the type-checker).
  }

instance PP RenamedModule where
  ppPrec _ rn = updPPCfg (\cfg -> cfg { ppcfgShowNameUniques = True }) doc
    where
    doc =
      vcat [ "// --- Defines -----------------------------"
           , pp (rmDefines rn)
           , "// -- Module -------------------------------"
           , pp (rmModule rn)
           -- , "// -- DEPS -------------------------------------"
           -- , vcat [ pp x | 
           --    (x,y) <- Map.toList (ifDecls (rmImported rn))
           --   ]
            , "// -----------------------------------------"
           ]

-- | Entry point. This is used for renaming a top-level module.
renameModule :: Module PName -> RenameM RenamedModule
renameModule m =
  do
    let lnm = mName m
    md  <- withLoc (srcRange lnm) (renameModuleDef (mDef m))
    env <- getCurTopDefs
    ids <- getExternalDeps
    scope <- getCurScope
    pure RenamedModule {
      rmModule = m { mDef = md, mInScope = scope },
      rmDefines = env,
      rmImported = ids
    }


instance Rename NestedModule where
  rename (NestedModule mo) =
    do

      lnm <- traverse (resolveNameDef NSModule) (mName mo)
      let nm = thing lnm
      (defs,env) <-
        withLoc (srcRange lnm)
          (inSubmodule (nameIdent nm)
            do
              d1 <- renameModuleDef (mDef mo)
              env <- getCurTopDefs
              pure (d1,env))
      scope <- getCurScope
      let newMo = mo { mName = lnm, mDef = defs, mInScope = scope }
      addResolvedMod env newMo
      pure (NestedModule newMo)

-- | Rename the definition of a module.
renameModuleDef :: ModuleDefinition PName -> RenameM (ModuleDefinition Name)
renameModuleDef def =
  case def of
    NormalModule decls -> NormalModule <$> renameModTopDecls decls
    FunctorInstance fun args _ -> makeFunctorInstance fun args
    InterfaceModule sig -> InterfaceModule <$> rename sig 


--------------------------------------------------------------------------------
-- Processing Functor Instantiation
--------------------------------------------------------------------------------

makeFunctorInstance ::
  Located (ImpName PName) -> ModuleInstanceArgs PName ->
  RenameM (ModuleDefinition Name)
makeFunctorInstance f args =
  do
    (newF,moF) <- withLoc (srcRange f) (resolveModName AFunctor (thing f))
    newArgs    <- rename args
    -- Note: currently the validation that the arguments match what the
    -- functor expects is done in the type checker.  We may want to do it
    -- here instead.
    inst <- generateFunctorInstance moF
    pure (FunctorInstance f { thing = newF } newArgs inst)

generateFunctorInstance :: Mod -> RenameM (ModuleInstance Name)
generateFunctorInstance mo =
  do
    mpath       <- getCurModPath
    (inst,newE) <- mkModInst mpath mo
    setThisModuleDefs newE
    subI <- doSubs mpath inst
    pure (Map.union inst subI)
  where
  -- Generate fresh instantiations for the modules contained in the
  -- module at this path
  doSubs mpath inst =
    Map.unions <$>
    mapM (doSub mpath)
      [ def | def <- Map.toList inst, nameNamespace (fst def) == NSModule ]
    
  -- Generate a fresh instantiation for the module at the given path
  mkModInst mpath someMo =
    do
      let oldEnv = modDefines someMo
      newEnv <- travNamingEnv (newFunctorInst mpath) oldEnv
      pure (zipByTextName oldEnv newEnv, newEnv)

  -- Instantiate a module contained in the given module path
  doSub mpath (old,new) =
    do
      ogMod <- lookupMod (ImpNested old) Nothing
      let newMPath = Nested mpath (nameIdent new)
      (newI,newE) <- mkModInst newMPath ogMod
      let ren x =
            case Map.lookup x newI of
              Just y -> y
              Nothing -> panic "generateFunctorInstance" ["Missing name"]
      addInstMod new
        Mod {
          modKind = modKind ogMod,
          modDefines = newE,
          modPublic = Set.map ren (modPublic ogMod)
        }
      subMap <- doSubs newMPath newI
      pure (Map.union newI subMap)

instance Rename ModuleInstanceArgs where
  rename args =
    case args of
      DefaultInstAnonArg {} ->
        panic "checkFunctorArgs" ["Nested DefaultInstAnonArg"]
      DefaultInstArg l -> DefaultInstArg <$> rnLocated rename l
      NamedInstArgs as -> NamedInstArgs  <$> mapM rename as

instance Rename ModuleInstanceNamedArg where
  rename (ModuleInstanceNamedArg nm l) =
    ModuleInstanceNamedArg nm <$> rnLocated rename l

instance Rename ModuleInstanceArg where
  rename arg =
    case arg of
      ModuleArg m ->
        do 
          (nm,_) <- resolveModName AModule m
          pure (ModuleArg nm)
      ParameterArg i -> pure (ParameterArg i)
      AddParams -> pure AddParams

--------------------------------------------------------------------------------
-- Processing Interface Modules
--------------------------------------------------------------------------------

instance Rename Signature where
  rename sig =
    do
      mo          <- getCurModPath
      env         <- doDefGroup (defsOfSig mo sig)
      setThisModuleDefs env
      newTopImps  <- mapM (fmap fst . doImport) topImps
      newNestImps <- mapM (fmap fst . doImport) nestImps

      funPs       <- mapM rename (sigFunParams sig)
      tyPs        <- mapM rename (sigTypeParams sig)
      ctrs        <- mapM (rnLocated rename) (sigConstraints sig)
      decls       <- renameSigDecls (sigDecls sig)

      pure Signature {
        sigImports      = newTopImps ++ newNestImps,
        sigTypeParams   = tyPs,
        sigConstraints  = ctrs,
        sigDecls        = decls,
        sigFunParams    = funPs
      }
    where
    (topImps,nestImps) = partition isTop (sigImports sig)
    isTop limp =
      case thing (iModule (thing limp)) of
        ImpTop {} -> True
        ImpNested {} -> False

instance Rename ParameterType where
  rename a =
    do
      n <- rnLocated (resolveNameDef NSType) (ptName a)
      return a { ptName = n }

instance Rename ParameterFun where
  rename a =
    do
      n   <- rnLocated (resolveNameDef NSValue) (pfName a)
      renameSchema (pfSchema a) \sig ->
        pure a { pfName = n, pfSchema = sig }

renameSigDecls :: [SigDecl PName] -> RenameM [SigDecl Name]
renameSigDecls decls =
  do
    gr <- forM decls \d ->
      do
        (d1,xs) <- getDeps (rename d)
        pure (d1, sigDeclName d1, Set.toList xs)
    concat <$> mapM validateRecSigDep (stronglyConnComp gr)
  
sigDeclName :: SigDecl a -> a  
sigDeclName d =
  thing
    case d of
      SigTySyn ts _ -> tsName ts
      SigPropSyn ps _ -> psName ps

validateRecSigDep :: SCC (SigDecl Name) -> RenameM [SigDecl Name]
validateRecSigDep sc =
  case sc of
    AcyclicSCC x -> pure [x]
    CyclicSCC xs ->
      do
        recordError (InvalidDependency (map (NamedThing . sigDeclName) xs))
        pure xs

instance Rename SigDecl where
  rename decl =
    case decl of
      SigTySyn ts mb   -> SigTySyn   <$> rename ts <*> pure mb
      SigPropSyn ps mb -> SigPropSyn <$> rename ps <*> pure mb




--------------------------------------------------------------------------------
-- Processing Top-level Declarations
--------------------------------------------------------------------------------

{- | Entry point. Rename a list of top-level declarations.
This is used for declaration that don't live in a module
(e.g., define on the command line.

NOTE: We used to check that the top-decls are not nested modules, but I can't
see anything that goes wrong if we allow modules, so I lifted the restriction
for now (ISD).
-}
renameTopDecls :: [TopDecl PName] -> RenameM (NamingEnv,[TopDecl Name])
renameTopDecls ds0 =
  do
    mo <- renameModTopDecls ds0
    env <- getCurTopDefs
    pure (env,mo)


-- | Rename the top-level declarations of a module.
renameModTopDecls :: [TopDecl PName] -> RenameM [TopDecl Name]
renameModTopDecls decls =
  do
    mp  <- getCurModPath
    mapM_ doImport topImps
    (env,defs) <- doDefOrdGroup (map (InModule (Just mp)) otherDecls)
    setThisModuleDefs env
    renameAndReorderTopDecls (zip otherDecls defs)
  where
  (topImps,otherDecls) = partitionEithers (map isTopImp decls)
  isTopImp d =
    case d of
      DImport limp ->
        case thing (iModule (thing limp)) of
          ImpTop {} -> Left limp
          _         -> Right d
      _ -> Right d


-- | Rename declarations and order the in dependency order.  Also, we preserve
-- the order of interface constraints as it they were written in the file,
-- but we move them as early as possible (i.e., immediately after all of
-- their dependencies.
renameAndReorderTopDecls :: [(TopDecl PName,Set Name)] -> RenameM [TopDecl Name]
renameAndReorderTopDecls xs =
  do
    gr0 <- go (0 :: Int) [] xs
    let nodeMap = Map.fromList [ (k,d) | (k,d,_,_) <- gr0 ]
        declFromKey k =
          case Map.lookup k nodeMap of
            Just d -> d
            Nothing -> panic "renameAndReorderTopDecls" ["missing node"]
        defMap        = Map.fromList
                        [ (x,k) | (k,_,defs,_) <- gr0, x <- Set.toList defs ]
        edges         = [ (d, k, mapMaybe (`Map.lookup` defMap) (Set.toList deps))
                        | (k,d,_,deps) <- gr0 ]
        compG         = sccGraph (fst (graphFromEdges' edges))
        ifaceCtrKeys  = [ k | (k,d,_,_) <- gr0, isIfaceCtr d ]
        ordered       = reorderTopDecls ifaceCtrKeys compG
        result        = map (fmap declFromKey) ordered
    -- traceM ("DEPS:\n" ++ unlines (map (_dbgShowEdge gr0) edges))
    concat <$> mapM validateTopRecDep result
  where
  -- XXX: report unused top-level module declarations.
  -- An SCC is used if:
  --   * it is a module level constraint, or
  --   * it is public, or
  --   * it is private, and it is a dependency of some other used SCC

  _dbgShowEdge gr (d', k, ds) =
    let d = case d' of
              DModule tl -> DModule (upd <$> tl)
                where upd (NestedModule nm) = NestedModule nm { mInScope = mempty }
              _ -> d'
    in
    let me = [ (prov,uses) | (k',_,prov,uses) <- gr, k == k' ] in
    let
        prov = [ p | (ps,_) <- me, p <- Set.toList ps ]
        uses = [ u | (_,us) <- me, u <- Set.toList us ]
    in
    "  " ++ show k ++ ": " ++ show ds ++ ", provides " ++
      unwords (map (show . pp) prov) ++ ", uses " ++ unwords (map (show . pp) uses) ++
    "\n" ++ unlines (map ("    " ++) (lines (show (pp d))))

  isIfaceCtr d =
    case d of
      DInterfaceConstraint {} -> True
      _ -> False

  -- This does the actual renaming, and assigns each declaration a unique id.
  -- Things earlier in the file order get small ids, which is used when
  -- ordering module level constraints (see `ifaceCtrKeys`)
  go !curId gr ds =
    case ds of
      [] -> pure gr
      (d,bdefs) : more ->
        -- traceM ("RENAMING: " ++ show (pp d)) >>
        case d of
          DImport imp ->
            do
              ((newI,defs),deps) <- getDeps (doImport imp)
              go (curId + 1) ((curId,DImport newI,defs,deps) : gr) more
          DModParam p ->
            do
              ((par,defs),deps) <- getDeps (doModParam p) 
              go (curId + 1) ((curId,DModParam par,defs,deps) : gr) more
          DModule {} ->
            do
              (d',deps) <- getDeps (rename d)
              -- We add implicit imports of all modules nested in this,
              -- as long as the following declaration is not a user specified
              -- import of this module.
              implicit <- implicitImports (getDModName d')
              -- traceM ("ADDING IMPLICIT:\n" ++ unlines [ "  " ++ show (pp i) | (i,_) <- implicit ])
              go (curId + 1) ((curId,d',bdefs,deps) : gr) (implicit ++ more)
          _ ->
            do
              (d',deps) <- getDeps (rename d)
              go (curId + 1) ((curId,d',bdefs,deps) : gr) more
  
  getDModName td =
    case td of
      DModule md
        | NestedModule mo <- tlValue md -> mName mo
      _ -> panic "renameAndReorderTopDecls" ["Not a module decl"]


-- | This computes a topological sort of the SCCs.  We do it manually to
-- enforce some additional constraints: we'd like the top-level module
-- constraints to go as early in the file as possible, and stay in the order
-- they were written in the file.
reorderTopDecls ::
  [Int] {- ^ Keys for top-level constraint declarations.
             Note that the these are the keys *in* the SCC, not the key *of*
            the SCC (i.e., the keys in the graph before its has been quotient-ed) -}->
  [(SCC Int, Int, [Int])] {- ^ Quotient graph -} ->
  [SCC Int]
reorderTopDecls priority grlist = reverse (go Set.empty [] allTodo)
  where
  allTodo = map getUnq priority ++ Map.keys qgraph
  -- The priority elements are in the list twice, but the extra copies will
  -- be skipped by the "visited" check.

  go visited res todo =
    case todo of
      [] -> res
      x : more ->
        case postOrder (visited,res) x of
          (visited1,res1) -> go visited1 res1 more

  postOrder s@(visited,res) k
    | k `Set.member` visited = s
    | otherwise =
      let (v,deps) = getQ k 
          visited1 = Set.insert k visited
          -- There should be no cycles so it doesn't matter if we do this now
          -- or later but we do it sooner to avoid looping if there's a bug.
          (visited2,res1) = foldl' postOrder (visited1,res) deps
      in (visited2, v : res1)

  -- Map nodes in the quotient graph to their declaration and
  -- dependencies (in the quotient graph)
  qgraph = Map.fromList [ (k,(v,deps)) | (v,k,deps) <- grlist ]
  getQ x =
    case Map.lookup x qgraph of
      Just v -> v
      Nothing -> panic "reorderTopDecls" ["missing Q"]

  -- Maps nodes in the original graph to nodes in the quotient graph
  unq    = Map.fromList [ (v,k) | (c,k,_) <- grlist, v <- flattenSCC c ]
  getUnq x =
    case Map.lookup x unq of
      Just v -> v
      Nothing -> panic "reorderTopDecls" ["missing unQ"]


--------------------------------------------------------------------------------
-- Validate Recursive Dependencies
--------------------------------------------------------------------------------

-- | Report errors for invalid recursive dependencies.
validateTopRecDep :: SCC (TopDecl Name) -> RenameM [TopDecl Name]
validateTopRecDep sc =
  case sc of
    AcyclicSCC x -> pure [x]
    CyclicSCC tds ->
      case mapM isDecl tds of
        Nothing ->
          do
            recordError (InvalidDependency (map topDeclName tds))
            pure tds
        Just ds ->
          do
            newDs <- validateRecDep (CyclicSCC (map tlValue ds))
            pure [Decl TopLevel {
              tlValue = d',
              tlDoc = Nothing,
              tlExport =
                if all ((== Private) . tlExport) ds then Private else Public
              -- XXX: This is wrong: it should be possible to have 
              -- recursive declarations where one of the things is public
              -- and the rest are private.  We have no way to represent this
              -- at the moment. Old renamer set this to `Public` always.
            } | d' <- newDs ]
  where
  -- Only decls may be recursive at present.  This would have to change,
  -- if, for example, we allowed recursive `enum`.
  isDecl d =
    case d of
      Decl tl -> Just tl
      _       -> Nothing
      
validateRecDep :: SCC (Decl Name) -> RenameM [Decl Name]
validateRecDep sc =
  case sc of
    AcyclicSCC d -> pure [d]
    CyclicSCC ds ->
      case mapM recOk ds of
        Just bs -> pure [DRec bs]
        Nothing ->
          do
            recordError (InvalidDependency (map (NamedThing . declName) ds))
            pure ds
      where
      recOk d =
        case d of
          DLocated d' _ -> recOk d'
          DBind b -> pure b
          _ -> Nothing


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

topDeclName :: TopDecl Name -> DepName
topDeclName topDecl =
  case topDecl of
    Decl d                  -> NamedThing (declName (tlValue d))
    DPrimType d             -> NamedThing (thing (primTName (tlValue d)))
    TDNewtype d             -> NamedThing (thing (nName (tlValue d)))
    TDEnum d                -> NamedThing (thing (eName (tlValue d)))
    DModule d               -> NamedThing (thing (mName m))
      where NestedModule m = tlValue d

    DInterfaceConstraint _ ds -> ConstratintAt (srcRange ds)
    DImport i               -> ImportAt (srcRange i)
    DModParam m             -> ModParamName (srcRange (mpSignature m)) (mpName m)

    Include {}              -> bad "Include"
    DParamDecl {}           -> bad "DParamDecl"
  where
  bad x         = panic "topDeclName" [x]




--------------------------------------------------------------------------------
-- Resolve names
--------------------------------------------------------------------------------

-- | Resolve a name that refers to something defined.
resolveNameUse :: Namespace -> PName -> RenameM Name
resolveNameUse ns p =
  do
    scope <- getCurScope
    case lookupNS ns p scope of
      Just names -> found names
      Nothing
        -- SPECIAL CASE: if we have a NameUse for NSValue, we also look in NSConstructor
        | ns == NSValue,
          Just names <- lookupNS NSConstructor p scope -> found names
      _ -> reportUnboundName ns p scope
  where
  found names =
    do
      x <-
        case names of
          One x -> pure x
          Ambig xs ->
            do
              p' <- located p
              recordError (MultipleSyms p' (Set.toList xs))
              pure (anyOne names)
      recordNameUses (Set.singleton x)
      pure x


-- | Resolve the name for a top-level definition.
resolveNameDef :: Namespace -> PName -> RenameM Name
resolveNameDef ns p =
  do
    defs <- getCurBinds
    case lookupNS ns p defs of
      Just names -> pure (anyOne names) -- there should be only one
      Nothing ->
        getCurLoc >>= \l ->
        panic "resolveNameDef"
          [ "Missing def"
          , "Location: " ++ show (pp l)
          , "Namespace: " ++ show ns
          , "Name: " ++ show (pp p)
          , "Defs: "
          , show (pp defs)
          ]

resolveModName :: ModKind -> ImpName PName -> RenameM (ImpName Name, Mod)
resolveModName k x =
  do
    nm <-
      case x of
        ImpTop m -> pure (ImpTop m)
        ImpNested y -> ImpNested <$> resolveNameUse NSModule y
    mo <- lookupMod nm (Just k)
    pure (nm, mo)
    


--------------------------------------------------------------------------------
-- Importing Stuff
--------------------------------------------------------------------------------



-- | The declaration should be an import. Add the names coming through
-- the import the current scope.
doImport ::
  Located (ImportG (ImpName PName)) ->
  RenameM (Located (ImportG (ImpName Name)), Set Name)
doImport limp =
  withLoc (srcRange limp)
  do
    let imp   = thing limp
    let lname = iModule imp
    (resMo,mo) <- withLoc (srcRange limp) (resolveModName AModule (thing lname))
    let isSys x = case nameSrc x of
                    SystemName -> True
                    UserName -> False
        isPub x = not (isSys x) && (x `Set.member` modPublic mo)
        newNames = interpImportEnv imp (filterUNames isPub (modDefines mo))
    case thing lname of
      ImpTop x -> recordTopImport x
      _ -> pure ()
    addImported (srcRange limp) newNames
    pure ( limp { thing = imp { iModule = (iModule imp) { thing = resMo } } },
           namingEnvNames newNames
        )

-- | Add the names from module parameters to the current scope
doModParam :: ModParam PName -> RenameM (ModParam Name, Set Name)
doModParam mp =
  do
    x   <- rnLocated (resolveModName ASignature) (mpSignature mp)
    let mo  = snd (thing x)
        rng = srcRange x
        nm  = mpName mp
    mpath <- getCurModPath
    env' <- travNamingEnv (newModParam mpath nm rng) (modDefines mo)
    let env =
          case mpAs mp of
            Nothing -> env'
            Just q  -> qualify q env'
    addModParams (mpSignature mp) { thing = nm } env
    let ren = zipByTextName env' (modDefines mo)
    pure (mp { mpSignature = fst <$> x, mpRenaming = ren }, namingEnvNames env)


--------------------------------------------------------------------------------
-- Implicit Imports
--------------------------------------------------------------------------------

-- | Compute what implicit imports we should add for the given name.
-- Note that the second argument in the pair is just there to make the types
-- fit---we place an empty set there, which will be replaced when the imports
-- are resolved.
implicitImports :: Located Name -> RenameM [(TopDecl PName, Set Name)]
implicitImports lname =
  do
    nts <- nestedModNames (thing lname)
    let imps = concatMap (nameTreeToImports (srcRange lname) []) nts
    pure [ (DImport lname { thing = i },Set.empty) | i <- imps ]

data NameTree = NameTree Name [NameTree]

nestedModNames :: Name -> RenameM [NameTree]
nestedModNames mo
  | identIsNormal (nameIdent mo) =
  do
    info <- lookupMod (ImpNested mo) Nothing
    case modKind info of
      AModule ->
        pure . NameTree mo . concat <$>
          mapM nestedModNames
            [x | x <- Set.toList (modPublic info), nameNamespace x == NSModule ]
      _ -> pure []
  | otherwise = pure []

nameTreeToImports :: Range -> [Ident] -> NameTree -> [ ImportG (ImpName PName) ]
nameTreeToImports rng qs (NameTree x subs) =
  Import {
    iModule = Located { srcRange = rng, thing = ImpNested nm },
    iAs     = Just (isToQual (reverse (i : qs))),
    iSpec   = Nothing,
    iInst   = Nothing,
    iDoc    = Nothing
  } : concatMap (nameTreeToImports rng (i : qs)) subs
  where
  i           = nameIdent x
  isToQual is = packModName (map identText is)
  nm =
    case reverse qs of
      []  -> mkUnqual i -- we don't import system names so this is OK here
      qs' -> mkQual (isToQual qs') i


--------------------------------------------------------------------------------
-- Renaming
--------------------------------------------------------------------------------

class Rename f where
  rename :: f PName -> RenameM (f Name)

-- | Rename a located thing using the given function.
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
      TDEnum n          -> TDEnum    <$> traverse rename n
      Include n         -> return (Include n)
      DModule m         -> DModule <$> traverse rename m
      DInterfaceConstraint d ds ->
        DInterfaceConstraint d <$> rnLocated (mapM rename) ds
      DParamDecl {}     -> panic "rename" ["DParamDecl"]
      DImport {}        -> panic "rename" ["DImport"]
      DModParam {}      -> panic "rename" ["DModParam"]



-- | Rename local declarations (e.g., from `where`), adds them to the local scope.
renameDecls :: [Decl PName] -> ([Decl Name] -> RenameM a) -> RenameM a
renameDecls decls k =
  do
    env <- doDefGroup (defsOf (map (InModule Nothing) decls))
    do
      ds <- inLocalBindScope False env
              do
                gr <- forM decls \d ->
                  do
                    (d1,xs) <- getDeps (rename d)
                    pure (d1, declName d1, Set.toList xs)
                concat <$> mapM validateRecDep (stronglyConnComp gr)

      inLocalScope env (k ds)
  

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

instance Rename PrimType where
  rename pt =
    do
      x <- rnLocated (resolveNameDef NSType) (primTName pt)
      let (as,ps) = primTCts pt
      cts <- renameQual as ps \as' ps' ->
        do
          recordNameUses (Set.fromList (map tpName as'))
          pure (as',ps')
      pure pt { primTCts = cts, primTName = x }


instance Rename Newtype where
  rename n =
    do
      nameT <- rnLocated (resolveNameDef NSType) (nName n)
      nameC <- resolveNameDef NSConstructor (nConName n)
      withTParams (nParams n) \ps' ->
        do
          body'     <- traverse (traverse rename) (nBody n)
          deriving' <- traverse (rnLocated (resolveNameUse NSType)) (nDeriving n)
          pure Newtype {
            nName     = nameT,
            nConName  = nameC,
            nParams   = ps',
            nBody     = body',
            nDeriving = deriving'
          }


instance Rename EnumDecl where
  rename n =
    do
      nameT  <- rnLocated (resolveNameDef NSType) (eName n)

      nameCs <- forM (eCons n) \tlEc ->
        do
          let con = tlValue tlEc
          nameC <- rnLocated (resolveNameDef NSConstructor) (ecName con)             
          pure (nameC,tlEc)

      withTParams (eParams n) \ps' ->
        do
          cons <- forM nameCs \(c,tlEc) ->
            do
              ts' <- traverse rename (ecFields (tlValue tlEc))
              let con = EnumCon { ecName = c, ecFields = ts' }
              pure tlEc { tlValue = con }
          deriving' <- traverse (rnLocated (resolveNameUse NSType)) (eDeriving n)
          pure EnumDecl {
            eName = nameT,
            eParams = ps',
            eCons = cons,
            eDeriving = deriving'
          }

instance Rename TySyn where
  rename (TySyn n f ps ty) =
    do
      n' <- rnLocated (resolveNameDef NSType) n
      withTParams ps \ps' ->
        TySyn n' f ps' <$> rename ty

instance Rename PropSyn where
  rename (PropSyn n f ps cs) =
    do
      n' <- rnLocated (resolveNameDef NSType) n  
      withTParams ps \ps' ->
        PropSyn n' f ps' <$> mapM rename cs





--------------------------------------------------------------------------------
-- Renaming of Types
--------------------------------------------------------------------------------


-- | Rename something with local type parameters.
withTParams ::
  [TParam PName] ->
  ([TParam Name] -> RenameM a) ->
  RenameM a
withTParams as k =
  do
    env <- doDefGroup (defsOf as)
    inLocalBindScope True env
      do
        as' <- traverse (renameTP env) as
        k as'

  where
  renameTP env tp =
    case lookupNS NSType (tpName tp) env of
      Just (One n) -> pure tp { tpName = n }
      _ -> panic "withTParams" ["Missing/ambiguous name"]
      

-- | Rename a qualified thing.
renameQual :: [TParam PName] -> [Prop PName] ->
              ([TParam Name] -> [Prop Name] -> RenameM a) ->
              RenameM a
renameQual as ps k =
  withTParams as \as' ->
    do
      ps' <- traverse rename ps
      k as' ps'

renameSchema :: Schema PName -> (Schema Name -> RenameM a) -> RenameM a
renameSchema (Forall ps p ty loc) k =
  renameQual ps p \ps' p' ->
    do
      ty' <- rename ty
      k (Forall ps' p' ty' loc)



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
      TUser qn ps    -> TUser <$> withLoc (srcRange qn)
                                    (traverse (resolveNameUse NSType) qn)
                              <*> traverse rename ps
      TTyApp fs      -> TTyApp   <$> traverse (traverse rename) fs
      TRecord fs     -> TRecord  <$> traverse (traverse rename) fs
      TTuple fs      -> TTuple   <$> traverse rename fs
      TWild          -> return TWild
      TLocated t' r  -> withLoc r (TLocated <$> rename t' <*> pure r)
      TParens t' k   -> (`TParens` k) <$> rename t'
      TInfix a o _ b -> do o' <- renameTypeOp o
                           a' <- rename a
                           b' <- rename b
                           mkTInfix a' o' b'

instance Rename TypeInst where
  rename ti = case ti of
    NamedInst nty -> NamedInst <$> traverse rename nty
    PosInst ty    -> PosInst   <$> rename ty


--------------------------------------------------------------------------------
-- Fixity Resolution
--------------------------------------------------------------------------------

renameOp :: Located PName -> RenameM (Located Name, Fixity)
renameOp ln =
  withLoc ln $
  do n <- resolveNameUse NSValue (thing ln)
     fixity <- lookupFixity n
     return (ln { thing = n }, fixity)

renameTypeOp :: Located PName -> RenameM (Located Name, Fixity)
renameTypeOp ln =
  withLoc ln $
  do n <- resolveNameUse NSType (thing ln)
     fixity <- lookupFixity n
     return (ln { thing = n }, fixity)

lookupFixity :: Name -> RenameM Fixity
lookupFixity n =
  case nameFixity n of
    Just fixity -> pure fixity
    Nothing     -> pure defaultFixity -- FIXME: should we raise an error instead?

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

mkEInfix :: Maybe Range           -- ^ Location of left expression
         -> Expr Name             -- ^ May contain infix expressions
         -> (Located Name,Fixity) -- ^ The operator to use
         -> Expr Name             -- ^ Will not contain infix expressions
         -> RenameM (Expr Name)

mkEInfix mbR e@(EInfix x o1 f1 y) op@(o2,f2) z =
   case compareFixity f1 f2 of
     FCLeft  -> return (EInfix e o2 f2 z)

     FCRight -> do r <- mkEInfix Nothing y op z
                   return (EInfix x o1 f1 r)

     FCError -> do recordError (FixityError o1 f1 o2 f2)
                   return (EInfix (maybeLoc mbR e) o2 f2 z)

mkEInfix mbR e@(EPrefix o1 x) op@(o2, f2) y =
  case compareFixity (prefixFixity o1) f2 of
    FCRight -> do
      addWarning (PrefixAssocChanged o1 x o2 f2 y)
      r <- mkEInfix Nothing x op y
      return (EPrefix o1 r)

    -- Even if the fixities conflict, we make the prefix operator take
    -- precedence.
    _ -> return (EInfix (maybeLoc mbR e) o2 f2 y)
  
-- Note that for prefix operator on RHS of infix operator we make the prefix
-- operator always have precedence, so we allow a * -b instead of requiring
-- a * (-b).

mkEInfix _ (ELocated e' r) op z =
     mkEInfix (Just r) e' op z

mkEInfix mbR e (o,f) z =
     return (EInfix (maybeLoc mbR e) o f z)
  
maybeLoc :: Maybe Range -> Expr name -> Expr name
maybeLoc mb e =
  case mb of
    Nothing -> e
    Just r  -> ELocated e r


--------------------------------------------------------------------------------
-- Bindings and Expressions
--------------------------------------------------------------------------------

-- | Rename a binding.
instance Rename Bind where
  rename b =
    doBind
    do
      n'    <- rnLocated (resolveNameDef NSValue) (bName b)
      let checkSig k =
            case bSignature b of
              Nothing -> k Nothing
              Just ls -> renameSchema (thing ls) \s' -> k (Just ls { thing = s' }) 
      checkSig \mbSig ->
        renameBindParams (bParams b) \ps ->
        do
          e' <- rnLocated rename (bDef b)
          pure b {
            bName      = n',
            bParams    = ps,
            bDef       = e',
            bSignature = mbSig,
            bPragmas   = bPragmas b
          }

instance Rename BindDef where
  rename DPrim           = return DPrim
  rename (DForeign cc i) = DForeign cc <$> traverse rename i
  rename (DImpl i)       = DImpl <$> rename i

instance Rename BindImpl where
  rename (DExpr e) = DExpr <$> rename e
  rename (DPropGuards {}) = panic "Rename BindImpl" ["DPropGuards"]

instance Rename Expr where
  rename expr =
    case expr of
      EVar n          -> EVar <$> resolveNameUse NSValue n
      ELit l          -> pure (ELit l)
      EGenerate e     -> EGenerate
                                 <$> rename e
      ETuple es       -> ETuple  <$> traverse rename es
      ERecord fs      -> ERecord <$> traverse (traverse rename) fs
      ESel e' s       -> ESel    <$> rename e' <*> pure s
      EUpd mb fs      ->
        do
          checkLabels fs
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

      EComp e' bs ->
        do
          (envs,newArms) <- mapAndUnzipM renameArm bs
          inLocalScope (mconcat envs)
            do
              newE <- rename e'
              pure (EComp newE newArms)

      EApp f x        -> EApp    <$> rename f  <*> rename x
      EAppT f ti      -> EAppT   <$> rename f  <*> traverse rename ti
      EIf b t f       -> EIf     <$> rename b  <*> rename t  <*> rename f
      ECase e as      -> ECase   <$> rename e  <*> traverse rename as

      EWhere e' ds    ->
        renameDecls ds \ds' ->
        do
          newE  <- rename e'
          pure (EWhere newE ds')

      ETyped e' ty    -> ETyped  <$> rename e' <*> rename ty
      ETypeVal ty     -> ETypeVal<$> rename ty
      EFun desc ps e' ->
        do
          desc' <- rename desc
          renamePats ps \newPs -> EFun desc' newPs <$> rename e'

      ELocated e' r   -> withLoc r (ELocated <$> rename e' <*> pure r)

      ESplit e        -> ESplit  <$> rename e
      EParens p       -> EParens <$> rename p
      EInfix x y _ z  -> do op <- renameOp y
                            x' <- rename x
                            z' <- rename z
                            x'' <- located x'
                            mkEInfix (Just (srcRange x'')) x' op z'
      EPrefix op e    -> EPrefix op <$> rename e

instance Rename FunDesc where
  rename (FunDesc nm offset) =
    do
      env <- getLastBindDefs
      nm' <- forM nm \x ->
        case lookupNS NSValue x env of
          Just a -> pure (anyOne a)
          Nothing -> panic "Rename FunDesc" ["Missing"]
      pure (FunDesc nm' offset)


--------------------------------------------------------------------------------
-- Records
--------------------------------------------------------------------------------

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
                       p = mkUnqual . selName <$> last ls           
         _ -> UpdField UpdFun [l] <$> rename (EUpd Nothing [ UpdField h more e])
      [] -> panic "rename@UpdField" [ "Empty label list." ]


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

  -- The input comes from UpdField, and as such, it is expected to be a
  -- non-empty list.
  reLoc xs = x { thing = map thing xs }
    where
      x = case xs of
            x':_ -> x'
            [] -> panic "checkLabels" ["UpdFields with no labels"]




--------------------------------------------------------------------------------
-- List Comprehensions
--------------------------------------------------------------------------------

-- | Rename matches and compute environment.
-- Does not affect the locals.
renameArm :: [Match PName] -> RenameM (NamingEnv,[Match Name])
renameArm ms =
  case ms of
    m : more ->
      renameMatch m \env m' ->
        do
          (env',moreMs) <- renameArm more
          pure (env' `shadowing` env, m' : moreMs)
    [] -> pure (mempty, [])

-- | The name environment generated by a single match.
-- The env is also added to the local environment, but we return it
-- so that we can compute the scope in the head of the comprehension.
renameMatch :: Match PName -> (NamingEnv -> Match Name -> RenameM a) -> RenameM a
renameMatch ma k =
  case ma of
    Match p e ->
      do
        e' <- rename e
        env <- liftSupply (defsOf p)
        inLocalBindScope False env
          do p' <- rename p
             k env (Match p' e')

    MatchLet b ->
      do
        env <- liftSupply (defsOf (InModule Nothing b))
        inLocalBindScope False env
          do
            b' <- rename b
            k env (MatchLet b')


--------------------------------------------------------------------------------
-- Patterns
--------------------------------------------------------------------------------

renameBindParams :: BindParams PName -> (BindParams Name -> RenameM a) -> RenameM a
renameBindParams bps k =
  case bps of
    DroppedParams x y -> k (DroppedParams x y)
    PatternParams ps  -> renamePats ps \ps' -> k (PatternParams ps')

instance Rename CaseAlt where
  rename (CaseAlt p e) =
    do
      env <- liftSupply (defsOf p)
      inLocalBindScope True env (CaseAlt <$> rename p <*> rename e)

-- | Rename a group of patterns from the same place and add their names
-- to the local environment.
renamePats :: [Pattern PName] -> ([Pattern Name] -> RenameM a) -> RenameM a
renamePats ps k =
  do
    env <- doDefGroup (defsOf ps)
    inLocalBindScope True env
      do
        ps' <- mapM rename ps
        k ps'

instance Rename Pattern where
  rename pat =
    case pat of
      PVar x -> PVar <$> rnLocated (resolveNameDef NSValue) x
      PCon c xs ->
        PCon
          <$> rnLocated (resolveNameUse NSConstructor) c
          <*> mapM rename xs
      PLocated p r  -> withLoc r (rename p)
      PTyped p t    -> PTyped <$> rename p <*> rename t
      _ -> panic "renamePat" ["Unexpected pattern"]