{-# Language BlockArguments, BangPatterns, ImportQualifiedPost #-}
module Cryptol.ModuleSystem.Renamer2 where

import Data.List(partition,foldl',find)
import Data.Set qualified as Set
import Data.Map qualified as Map
import Control.Monad(forM,mapAndUnzipM,foldM_)

import Cryptol.Utils.Panic(panic)
import Cryptol.Utils.Ident
import Cryptol.Parser.Position
import Cryptol.Parser.Selector
import Cryptol.Parser.AST
import Cryptol.ModuleSystem.Name
import Cryptol.ModuleSystem.NamingEnv
import Cryptol.ModuleSystem.Interface
import Cryptol.ModuleSystem.Binds(defsOf, defsOfSig, InModule(..), newFunctorInst, newModParam)
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
    env <- getCurTopDefs
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
      ParameterArg i -> pure (ParameterArg i) -- XXX: Add proper names for module parameters
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
    mp  <- getCurModPath
    env <- doDefGroup (defsOf (map (InModule (Just mp)) decls))
    setThisModuleDefs env
    mapM_ doImportOrModParamDecl topImps
    renameDeclBlocks otherDecls
    -- XXX: reorder in dependency order
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
              imp' <- doImportOrModParamDecl imp
              more' <- renameDeclBlocks more
              pure (imp' : more')
  where
  -- We assume that top-level imports were already processed,
  -- see `findTopImports`.  We find both local and parameter imports.
  isImport d =
    case d of
      DImport {}    -> True
      DModParam {}  -> True
      _             -> False


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
    case names of
      One x -> pure x
      Ambig xs ->
        do
          p' <- located p
          recordError (MultipleSyms p' (Set.toList xs))
          pure (anyOne names)


-- | Resolve the name for a top-level definition.
resolveNameDef :: Namespace -> PName -> RenameM Name
resolveNameDef ns p =
  do
    defs <- getCurBinds
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

doImportOrModParamDecl :: TopDecl PName -> RenameM (TopDecl Name)
doImportOrModParamDecl d =
  case d of
    DImport imp -> DImport <$> doImport imp
    DModParam p -> DModParam <$> rename p
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

instance Rename ModParam where
  rename mp =
    do
      x   <- rnLocated (resolveModName ASignature) (mpSignature mp)
      let mo  = snd (thing x)
          rng = srcRange x
          nm  = mpName mp
      mpath <- getCurModPath
      env <- travNamingEnv (newModParam mpath nm rng) (modDefines mo)
      addModParams env
      let ren = zipByTextName (modDefines mo) env
      pure mp { mpSignature = fst <$> x, mpRenaming = ren }




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
      DImport {}        -> panic "Rename TopDecl" ["DImport"]
      DModParam {}      -> panic "Rename TopDecl" ["DModParam"]
      DInterfaceConstraint d ds ->
        DInterfaceConstraint d <$> rnLocated (mapM rename) ds
      DParamDecl {} -> panic "rename" ["DParamDecl"]

-- | Rename local declarations (e.g., from `where`), adds them to the local scope.
renameDecls :: [Decl PName] -> RenameM [Decl Name]
renameDecls decls =
  do
    env <- doDefGroup (defsOf (map (InModule Nothing) decls))
    addLocals env
    mapM rename decls

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
      (_,cts) <- renameQual as ps \as' ps' -> pure (as',ps')
      pure pt { primTCts = cts, primTName = x }


instance Rename Newtype where
  rename n =
    do
      nameT <- rnLocated (resolveNameDef NSType) (nName n)
      nameC <- resolveNameDef NSConstructor (nConName n)
      snd <$> withTParams (nParams n) \ps' ->
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

      snd <$> withTParams (eParams n) \ps' ->
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
      snd <$> withTParams ps \ps' ->
        TySyn n' f ps' <$> rename ty

instance Rename PropSyn where
  rename (PropSyn n f ps cs) =
    do
      n' <- rnLocated (resolveNameDef NSType) n  
      snd <$> withTParams ps \ps' ->
        PropSyn n' f ps' <$> mapM rename cs


--------------------------------------------------------------------------------
-- Interface Modules
--------------------------------------------------------------------------------

instance Rename ParameterType where
  rename a =
    do
      n <- rnLocated (resolveNameDef NSType) (ptName a)
      return a { ptName = n }

instance Rename ParameterFun where
  rename a =
    do
      n   <- rnLocated (resolveNameDef NSValue) (pfName a)
      sig <- renameSchema (pfSchema a)
      pure a { pfName = n, pfSchema = snd sig }

instance Rename SigDecl where
  rename decl =
    case decl of
      SigTySyn ts mb   -> SigTySyn   <$> rename ts <*> pure mb
      SigPropSyn ps mb -> SigPropSyn <$> rename ps <*> pure mb



--------------------------------------------------------------------------------
-- Renaming of Types
--------------------------------------------------------------------------------


-- | Rename something with local type parameters.
-- We return the type environment, so that it can be used in other places
-- (e.g., the type vars from a type signature are in scope in its associated
-- definition).
withTParams ::
  [TParam PName] ->
  ([TParam Name] -> RenameM a) ->
  RenameM (NamingEnv, a)
withTParams as k =
  do
    env <- doDefGroup (defsOf as)
    res <- inLocalScope
      do
        as' <- traverse renameTP as
        k as'
    pure (env,res)
  where
  renameTP tp =
    do
      n <- resolveNameDef NSType (tpName tp)
      pure tp { tpName = n }

-- | Rename a qualified thing.
renameQual :: [TParam PName] -> [Prop PName] ->
              ([TParam Name] -> [Prop Name] -> RenameM a) ->
              RenameM (NamingEnv, a)
renameQual as ps k =
  withTParams as \as' ->
    do
      ps' <- traverse rename ps
      k as' ps'

-- | Rename a schema, assuming that the type variables have already been brought
-- into scope.
renameSchema :: Schema PName -> RenameM (NamingEnv,Schema Name)
renameSchema (Forall ps p ty loc) =
  renameQual ps p \ps' p' ->
    do
      ty' <- rename ty
      pure (Forall ps' p' ty' loc)



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
    do
      n'    <- rnLocated (resolveNameDef NSValue) (bName b)
      mbSig <- traverse (traverse renameSchema) (bSignature b)
      inLocalScope
        do
          mapM_ (addLocals . fst . thing) mbSig
          ps <- rename (bParams b)
          e' <- rnLocated rename (bDef b)
          pure b {
            bName      = n',
            bParams    = ps,
            bDef       = e',
            bSignature = fmap snd `fmap` mbSig,
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
        inLocalScope
        do
          (envs,newArms) <- mapAndUnzipM renameArm bs
          addLocals (mconcat envs)
          newE <- rename e'
          pure (EComp newE newArms)

      EApp f x        -> EApp    <$> rename f  <*> rename x
      EAppT f ti      -> EAppT   <$> rename f  <*> traverse rename ti
      EIf b t f       -> EIf     <$> rename b  <*> rename t  <*> rename f
      ECase e as      -> ECase   <$> rename e  <*> traverse rename as

      EWhere e' ds    ->
        inLocalScope
        do
          newDs <- renameDecls ds -- these add definitions to the local scope
          newE  <- rename e'
          pure (EWhere newE newDs)

      ETyped e' ty    -> ETyped  <$> rename e' <*> rename ty
      ETypeVal ty     -> ETypeVal<$> rename ty
      EFun desc ps e' ->
        inLocalScope
        do
          desc' <- rename desc
          newPs <- renamePats ps
          EFun desc' newPs <$> rename e'

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
      nm' <- traverse (resolveNameDef NSValue) nm
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
  inLocalScope
  do
    (envs,newMs) <- mapAndUnzipM renameMatch ms
    let newEnv = foldl' (flip shadowing) mempty envs
    pure (newEnv, newMs)

-- | The name environment generated by a single match.
-- The env is also added to the local environment, but we return it
-- so that we can compute the scope in the head of the comprehension.
renameMatch :: Match PName -> RenameM (NamingEnv, Match Name)
renameMatch ma =
  case ma of
    Match p e ->
      do
        e' <- rename e
        env <- liftSupply (defsOf p)
        p' <- renamePat env p
        addLocals env
        pure (env, Match p' e')

    MatchLet b ->
      do
        env <- liftSupply (defsOf (InModule Nothing b))
        b'  <- inLocalBindScope env (rename b)
        addLocals env
        pure (env, MatchLet b')


--------------------------------------------------------------------------------
-- Patterns
--------------------------------------------------------------------------------

instance Rename BindParams where
  rename bps =
    case bps of
      DroppedParams x y -> pure (DroppedParams x y)
      PatternParams ps  -> PatternParams <$> renamePats ps

instance Rename CaseAlt where
  rename (CaseAlt p e) =
    inLocalScope
    do
      env <- liftSupply (defsOf p)
      newP <- renamePat env p
      addLocals env
      CaseAlt newP <$> rename e

-- | Rename a group of patterns from the same place and add their names
-- to the local environment.
renamePats :: [Pattern PName] -> RenameM [Pattern Name]
renamePats ps =
  do
    env <- doDefGroup (defsOf ps)
    addLocals env
    mapM (renamePat env) ps

renamePat :: NamingEnv -> Pattern PName -> RenameM (Pattern Name)
renamePat defs pat =
  case pat of
    PVar x ->
      case lookupNS NSValue (thing x) defs of
        Just (One y) -> pure (PVar x { thing = y })
        _ -> panic "renamePat" ["Missing/ambiguous pattern variable"]
    PCon c xs ->
      PCon
        <$> rnLocated (resolveNameUse NSConstructor) c
        <*> mapM (renamePat defs) xs
    PLocated p r  -> withLoc r (renamePat defs p)
    PTyped p t    -> PTyped <$> renamePat defs p <*> rename t
    _ -> panic "renamePat" ["Unexpected pattern"]