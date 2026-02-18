{-# Language BlockArguments, BangPatterns, ImportQualifiedPost #-}
module Cryptol.ModuleSystem.Renamer2 where

import Data.List(partition)
import Data.Set qualified as Set
import Data.Map qualified as Map

import Cryptol.Utils.Panic(panic)
import Cryptol.Utils.Ident
import Cryptol.Parser.Position
import Cryptol.Parser.AST
import Cryptol.ModuleSystem.Name
import Cryptol.ModuleSystem.NamingEnv
import Cryptol.ModuleSystem.Interface
import Cryptol.ModuleSystem.Binds(defsOf, defsOfSig, InModule(..), newFunctorInst)
import Cryptol.ModuleSystem.Names
import Cryptol.ModuleSystem.Renamer.Error
import Cryptol.ModuleSystem.Renamer2.Monad

-- | The result of renaming a module
data RenamedModule = RenamedModule
  { rmModule   :: Module Name     -- ^ The renamed module
  , rmDefines  :: NamingEnv       -- ^ What this module defines
  , rmImported :: IfaceDecls
    -- ^ Imported declarations.  This provides the types for external
    -- names (used by the type-checker).
  }

-- | Entry point. This is used for renaming a top-level module.
renameTopModule :: Module PName -> RenameM RenamedModule
renameTopModule m =
  do
    let lnm = mName m
    mo  <- withLoc (srcRange lnm) (renameModuleDef (mDef m))
    env <- getCurDefs
    ids <- getExternalDeps
    pure RenamedModule {
      rmModule = m { mDef = mo },
      rmDefines = env,
      rmImported = ids
    }

instance Rename NestedModule where
  rename (NestedModule mo) =
    do
      lnm <- traverse (resolveNameDef NSModule) (mName mo)
      let nm = thing lnm
      defs <-
        withLoc (srcRange lnm)
          (inSubmodule (nameIdent nm) (renameModuleDef (mDef mo)))
      let newMo = mo { mName = lnm, mDef = defs }
      addResolvedMod newMo
      pure (NestedModule newMo)

-- | Rename the definition of a module.
renameModuleDef :: ModuleDefinition PName -> RenameM (ModuleDefinition Name)
renameModuleDef def =
  case def of
    NormalModule decls -> NormalModule <$> renameTopDecls decls
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
    doSubs mpath inst
    pure inst
  where
  -- Generate fresh instantiations for the modules contained in the
  -- module at this path
  doSubs mpath inst =
    mapM_ (doSub mpath)
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
      doSubs newMPath newI

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
      ParameterArg i -> pure (ParameterArg i) -- XXX: Add proper names for module parameters
      AddParams -> pure AddParams

--------------------------------------------------------------------------------
-- Processing Interface Modules
--------------------------------------------------------------------------------

instance Rename Signature where
  rename sig =
    do
      mo          <- getCurModPath
      env         <- liftSupply (defsOfSig mo sig)
      setThisModuleDefs env
      newTopImps  <- mapM doImport topImps
      newNestImps <- mapM doImport nestImps

      funPs       <- mapM rename (sigFunParams sig)
      tyPs        <- mapM rename (sigTypeParams sig)
      ctrs        <- mapM (rnLocated rename) (sigConstraints sig)
      decls       <- mapM rename (sigDecls sig)

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



--------------------------------------------------------------------------------
-- Processing Declarations
--------------------------------------------------------------------------------

-- | Rename the top-level declarations of a module.
renameTopDecls :: [TopDecl PName] -> RenameM [TopDecl Name]
renameTopDecls decls =
  do
    mp <- getCurModPath
    defs' <- liftSupply (defsOf (map (InModule (Just mp)) decls))
    mapM_ (recordError . OverlappingSyms) (findAmbig defs')
    setThisModuleDefs (forceUnambig defs')
    mapM_ doImportDecl topImps
    renameDeclBlocks otherDecls
  where
  (topImps,otherDecls) = partition isTopImp decls
  isTopImp d =
    case d of
      DImport limp ->
        case thing (iModule (thing limp)) of
          ImpTop {} -> True
          _         -> False
      _ -> False

-- | Rename top-level declarations, assuming we've processed top-level imports.
renameDeclBlocks :: [TopDecl PName] -> RenameM [TopDecl Name]
renameDeclBlocks ds =
  -- XXX: also break on module to optionally add implicit imports
  case break isImport ds of
    (as,rest) ->
      do
        as' <- mapM rename as
        case rest of
          [] -> pure as'
          imp : more ->
            do
              imp' <- doImportDecl imp
              more' <- renameDeclBlocks more
              pure (imp' : more')
  where
  -- We assume that top-level imports were separated, see `findTopImports`.
  isImport d =
    case d of
      DImport {}  -> True
      _           -> False


--------------------------------------------------------------------------------
-- Resolve names
--------------------------------------------------------------------------------

-- | Resolve a name that refers to something defined.
resolveNameUse :: Namespace -> PName -> RenameM Name
resolveNameUse ns p =
  do
    scope <- getCurScope
    case lookupNS ns p scope of
      Just names ->
        case names of
          One x -> pure x
          Ambig xs ->
            do
              p' <- located p
              recordError (MultipleSyms p' (Set.toList xs))
              pure (anyOne names)
      Nothing -> reportUnboundName ns p scope

-- | Resolve the name for a top-level definition.
resolveNameDef :: Namespace -> PName -> RenameM Name
resolveNameDef ns p =
  do
    defs <- getCurDefs
    case lookupNS ns p defs of
      Just names -> pure (anyOne names) -- there should be only one
      Nothing -> panic "resolveNameDef" ["Missing def"]

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

doImportDecl :: TopDecl PName -> RenameM (TopDecl Name)
doImportDecl d =
  case d of
    DImport imp -> DImport <$> doImport imp
    _ -> panic "doImport" ["Not an import."]

-- | The declaration should be an import. Add the names coming through
-- the import the current scope.
doImport ::
  Located (ImportG (ImpName PName)) -> RenameM (Located (ImportG (ImpName Name)))
doImport = rnLocated \imp ->
  do
    let lname = iModule imp
    (resMo,mo) <- withLoc (srcRange lname) (resolveModName AModule (thing lname))
    let isPub x = x `Set.member` modPublic mo
    addImported (interpImportEnv imp (filterUNames isPub (modDefines mo)))
    pure imp { iModule = (iModule imp) { thing = resMo } }
  


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
  rename = undefined
 
instance Rename TySyn where
  rename (TySyn n f ps ty) = undefined {-
    shadowNames ps
    do n' <- rnLocated (renameType NameBind) n
       depsOf (NamedThing (thing n')) $
         TySyn n' <$> pure f <*> traverse rename ps <*> rename ty -}

instance Rename PropSyn where
  rename (PropSyn n f ps cs) = undefined {-
    shadowNames ps 
    do n' <- rnLocated (renameType NameBind) n
       PropSyn n' <$> pure f <*> traverse rename ps <*> traverse rename cs -}


--------------------------------------------------------------------------------
-- Interface Modules
--------------------------------------------------------------------------------

instance Rename ParameterType where
  rename a = undefined {-
    do n' <- rnLocated (renameType NameBind) (ptName a)
       return a { ptName = n' } -}

instance Rename ParameterFun where
  rename a = undefined {-
    do
      n'   <- rnLocated (resolveNameDef NSValue) (pfName a)
       -- depsOf (NamedThing (thing n'))
      do sig' <- renameSchema (pfSchema a)
         return a { pfName = n', pfSchema = snd sig' }
-}
instance Rename SigDecl where
  rename decl =
    case decl of
      SigTySyn ts mb   -> SigTySyn   <$> rename ts <*> pure mb
      SigPropSyn ps mb -> SigPropSyn <$> rename ps <*> pure mb



--------------------------------------------------------------------------------
-- Renaming of Types
--------------------------------------------------------------------------------

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


--------------------------------------------------------------------------------
-- Fixity Resolution
--------------------------------------------------------------------------------

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
