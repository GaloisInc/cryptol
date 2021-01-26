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
module Cryptol.ModuleSystem.Renamer (
    NamingEnv(), shadowing
  , BindsNames(..), InModule(..)
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
  ) where

import Prelude ()
import Prelude.Compat

import Data.Either(partitionEithers)
import Data.Maybe(fromJust)
import Data.List(find,foldl')
import Data.Foldable(toList)
import Data.Map.Strict(Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Graph(SCC(..))
import Data.Graph.SCC(stronglyConnComp)
import           MonadLib hiding (mapM, mapM_)


import Cryptol.ModuleSystem.Name
import Cryptol.ModuleSystem.NamingEnv
import Cryptol.ModuleSystem.Exports
import Cryptol.Parser.Position(getLoc)
import Cryptol.Parser.AST
import Cryptol.Parser.Selector(selName)
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.RecordMap
import Cryptol.Utils.Ident(allNamespaces)

import Cryptol.ModuleSystem.Interface
import Cryptol.ModuleSystem.Renamer.Error
import Cryptol.ModuleSystem.Renamer.Monad


renameModule :: Module PName -> RenameM (IfaceDecls,NamingEnv,Module Name)
renameModule m =
  do env      <- liftSupply (defsOf m)
     nested   <- liftSupply (collectNestedModules env m)
     setNestedModule (nestedModuleNames nested)
       do (ifs,m1) <- collectIfaceDeps
                 $ renameModule' nested env (TopModule (thing (mName m))) m
          pure (ifs,env,m1)

renameTopDecls ::
  ModName -> [TopDecl PName] -> RenameM (NamingEnv,[TopDecl Name])
renameTopDecls m ds =
  do let mpath = TopModule m
     env    <- liftSupply (defsOf (map (InModule (Just mpath)) ds))
     nested <- liftSupply (collectNestedModulesDecls env m ds)

     setNestedModule (nestedModuleNames nested)
       do ds1 <- shadowNames' CheckOverlap env
                                        (renameTopDecls' (nested,mpath) ds)
          pure (env,ds1)


nestedModuleNames :: NestedMods -> Map ModPath Name
nestedModuleNames mp = Map.fromList (map entry (Map.keys mp))
  where
  entry n = case nameInfo n of
              Declared p _ -> (Nested p (nameIdent n),n)
              _ -> panic "nestedModuleName" [ "Not a top-level name" ]


class Rename f where
  rename :: f PName -> RenameM (f Name)


-- | Returns:
--
--    * Interfaces for imported things,
--    * Things defines in the module
--    * Renamed module
renameModule' ::
  NestedMods -> NamingEnv -> ModPath -> ModuleG mname PName ->
  RenameM (ModuleG mname Name)
renameModule' thisNested env mpath m =
  setCurMod mpath
  do (moreNested,imps) <- mconcat <$> mapM doImport (mImports m)
     let allNested = Map.union moreNested thisNested
         openDs    = map thing (mSubmoduleImports m)
         allImps   = openLoop allNested env openDs imps

     decls' <- shadowNames allImps $
               shadowNames' CheckOverlap env $
               renameTopDecls' (allNested,mpath) $
               mDecls m
     let m1      = m { mDecls = decls' }
         exports = modExports m1
     mapM_ recordUse (exported NSType exports)
     return m1


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
                    Nothing -> do record (InvalidDependency xs)
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
              record $ InvalidDependency $ map NamedThing $ fst a : bad
    _ -> pure ()
  where
  ms = [ (x,p) | NamedThing x <- xs, Declared p _ <- [ nameInfo x ] ]


renameTopDecls' ::
  (NestedMods,ModPath) -> [TopDecl PName] -> RenameM [TopDecl Name]
renameTopDecls' info ds =
  do (ds1,deps) <- depGroup (traverse (renameWithMods info) ds)


     let (noNameDs,nameDs) = partitionEithers (map topDeclName ds1)
         ctrs = [ nm | (_,nm@(ConstratintAt {})) <- nameDs ]
         toNode (d,x) = ((d,x),x, (if usesCtrs d then ctrs else []) ++
                               map NamedThing
                             ( Set.toList
                             ( Map.findWithDefault Set.empty x deps) ))
         ordered = stronglyConnComp (map toNode nameDs)
         fromSCC x =
            case x of
              AcyclicSCC (d,_) -> pure [d]
              CyclicSCC ds_xs ->
                let (rds,xs) = unzip ds_xs
                in case mapM valid rds of
                     Nothing -> do record (InvalidDependency xs)
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
  usesCtrs td =
    case td of
      Decl tl                 -> isValDecl (tlValue tl)
      DPrimType {}            -> False
      TDNewtype {}            -> False
      DParameterType {}       -> False
      DParameterConstraint {} -> False
      DParameterFun {}        -> False
      DModule tl              -> any usesCtrs (mDecls m)
        where NestedModule m = tlValue tl
      DImport {}              -> False
      Include {}              -> bad "Include"

  isValDecl d =
    case d of
      DLocated d' _ -> isValDecl d'
      DBind {}      -> True
      DType {}      -> False
      DProp {}      -> False
      DRec {}       -> bad "DRec"
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

    DParameterConstraint ds ->
      case ds of
        []  -> noName
        _   -> Right (topDecl, ConstratintAt (fromJust (getLoc ds)))
    DImport {}              -> noName

    Include {}              -> bad "Include"
  where
  noName    = Left topDecl
  hasName n = Right (topDecl, NamedThing n)
  bad x     = panic "topDeclName" [x]


-- | Returns:
--  * The public interface of the imported module
--  * Infromation about nested modules in this module
--  * New names introduced through this import
doImport :: Located Import -> RenameM (NestedMods, NamingEnv)
doImport li =
  do let i = thing li
     decls <- lookupImport i
     let declsOf = unqualifiedEnv . ifPublic
         nested  = declsOf <$> ifModules decls
     pure (nested, interpImportIface i decls)



--------------------------------------------------------------------------------
-- Compute names coming through `open` statements.

data OpenLoopState = OpenLoopState
  { unresolvedOpen  :: [ImportG PName]
  , scopeImports    :: NamingEnv    -- names from open/impot
  , scopeDefs       :: NamingEnv    -- names defined in this module
  , scopingRel      :: NamingEnv    -- defs + imports with shadowing
                                    -- (just a cache)
  , openLoopChange  :: Bool
  }

-- | Processing of a single @open@ declaration
processOpen :: NestedMods -> OpenLoopState -> ImportG PName -> OpenLoopState
processOpen modEnvs s o =
  case lookupNS NSModule (iModule o) (scopingRel s) of
    []  -> s { unresolvedOpen = o : unresolvedOpen s }
    [n] ->
      case Map.lookup n modEnvs of
        Nothing  -> panic "openLoop" [ "Missing defintion for module", show n ]
        Just def ->
          let new = interpImportEnv o def
              newImps = new <> scopeImports s
          in s { scopeImports   = newImps
               , scopingRel     = scopeDefs s `shadowing` newImps
               , openLoopChange = True
               }
    _ -> s
    {- Notes:
       * ambiguity will be reported later when we do the renaming
       * assumes scoping only grows, which should be true
       * we are not adding the names from *either* of the imports
         so this may give rise to undefined names, so we may want to
         suppress reporing undefined names if there ambiguities for
         module names.  Alternatively we could add the defitions from
         *all* options, but that might lead to spurious ambiguity errors.
    -}

{- | Complete the set of import using @open@ declarations.
This should terminate because on each iteration either @unresolvedOpen@
decreases or @openLoopChange@ remians @False@. We don't report errors
here, as they will be reported during renaming anyway. -}
openLoop ::
  NestedMods      {- ^ Definitions of all known nested modules  -} ->
  NamingEnv       {- ^ Definitions of the module (these shadow) -} ->
  [ImportG PName] {- ^ Open declarations                        -} ->
  NamingEnv       {- ^ Imported declarations                    -} ->
  NamingEnv       {- ^ Completed imports                        -}
openLoop modEnvs defs os imps =
  scopingRel $ loop OpenLoopState
                      { unresolvedOpen = os
                      , scopeImports   = imps
                      , scopeDefs      = defs
                      , scopingRel     = defs `shadowing` imps
                      , openLoopChange = True
                      }
  where
  loop s
    | openLoopChange s =
      loop $ foldl' (processOpen modEnvs)
                    s { unresolvedOpen = [], openLoopChange = False }
                    (unresolvedOpen s)
    | otherwise = s


--------------------------------------------------------------------------------


data WithMods f n = WithMods (NestedMods,ModPath) (f n)

forgetMods :: WithMods f n -> f n
forgetMods (WithMods _ td) = td

renameWithMods ::
  Rename (WithMods f) => (NestedMods,ModPath) -> f PName -> RenameM (f Name)
renameWithMods info m = forgetMods <$> rename (WithMods info m)


instance Rename (WithMods TopDecl) where
  rename (WithMods info td) = WithMods info <$>
    case td of
      Decl d      -> Decl      <$> traverse rename d
      DPrimType d -> DPrimType <$> traverse rename d
      TDNewtype n -> TDNewtype <$> traverse rename n
      Include n   -> return (Include n)
      DParameterFun f  -> DParameterFun  <$> rename f
      DParameterType f -> DParameterType <$> rename f

      DParameterConstraint ds ->
        case ds of
          [] -> pure (DParameterConstraint [])
          _  -> depsOf (ConstratintAt (fromJust (getLoc ds)))
              $ DParameterConstraint <$> mapM renameLocated ds
      DModule m -> DModule <$> traverse (renameWithMods info) m
      DImport li -> DImport <$> traverse renI li
        where
        renI i = do m <- rename (iModule i)
                    pure i { iModule = m }

instance Rename ImpName where
  rename i =
    case i of
      ImpTop m -> pure (ImpTop m)
      ImpNested m -> ImpNested <$> resolveName NameUse NSModule m

instance Rename (WithMods NestedModule) where
  rename (WithMods info (NestedModule m)) = WithMods info <$>
    do let (nested,mpath) = info
           lnm            = mName m
           nm             = thing lnm
           newMPath       = Nested mpath (getIdent nm)
       n   <- resolveName NameBind NSModule nm
       depsOf (NamedThing n)
         do let env = case Map.lookup n (fst info) of
                        Just defs -> defs
                        Nothing -> panic "rename"
                           [ "Missing environment for nested module", show n ]
            m1 <- renameModule' nested env newMPath m
            pure (NestedModule m1 { mName = lnm { thing = n } })


renameLocated :: Rename f => Located (f PName) -> RenameM (Located (f Name))
renameLocated x =
  do y <- rename (thing x)
     return x { thing = y }

instance Rename PrimType where
  rename pt =
    do x <- rnLocated (renameType NameBind) (primTName pt)
       depsOf (NamedThing (thing x))
         do let (as,ps) = primTCts pt
            (_,cts) <- renameQual as ps $ \as' ps' -> pure (as',ps')
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

rnLocated :: (a -> RenameM b) -> Located a -> RenameM (Located b)
rnLocated f loc = withLoc loc $
  do a' <- f (thing loc)
     return loc { thing = a' }

instance Rename Decl where
  rename d      = case d of
    DBind b           -> DBind <$> rename b

    DType syn         -> DType         <$> rename syn
    DProp syn         -> DProp         <$> rename syn
    DLocated d' r     -> withLoc r
                       $ DLocated      <$> rename d'  <*> pure r

    DFixity{}         -> panic "renaem" [ "DFixity" ]
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
       Just [n]  ->
          do case nt of
               NameBind -> pure ()
               NameUse  -> addDep n
             use n    -- for warning
             return (Just n)
       Just []   -> panic "Renamer" ["Invalid expression renaming environment"]
       Just syms ->
         do mapM_ use syms    -- mark as used to avoid unused warnings
            n <- located qn
            record (MultipleSyms n syms)
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
              actual : _ -> record (WrongNamespace expected actual nm)

              -- the value is just missing
              [] -> record (UnboundName expected nm)

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
     liftSupply (mkParameter ns (getIdent pn) (roLoc ro))

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
    FCError -> do record (FixityError o1 f1 o2 f2)
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
                 UpdFun -> UpdField UpdFun [l] <$> rename (EFun emptyFunDesc [PVar p] e)
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
         Just l' -> record (OverlappingRecordUpdate (reLoc l) (reLoc l'))
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

     FCError -> do record (FixityError o1 f1 o2 f2)
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
    do n <- liftSupply (mkParameter NSValue (getIdent thing) srcRange)
       -- XXX: for deps, we should record a use
       return (singletonE thing n)

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
                n   <- liftSupply (mkParameter NSType (getIdent pn) loc)
                return (singletonT pn n)

           -- This references a type synonym that's not in scope. Record an
           -- error and continue with a made up name.
           | otherwise ->
             do loc <- curLoc
                record (UnboundName NSType (Located loc pn))
                n   <- liftSupply (mkParameter NSType (getIdent pn) loc)
                return (singletonT pn n)

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
