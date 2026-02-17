{-# Language BlockArguments, BangPatterns, ImportQualifiedPost #-}
module Cryptol.ModuleSystem.Renamer2 where

import Data.List(partition)
import Data.Set qualified as Set

import Cryptol.Utils.Panic(panic)
import Cryptol.Utils.Ident
import Cryptol.Parser.AST
import Cryptol.ModuleSystem.Name
import Cryptol.ModuleSystem.NamingEnv
import Cryptol.ModuleSystem.Interface
import Cryptol.ModuleSystem.Binds(defsOf, InModule(..))
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
    mo  <- renameModuleDef (mDef m)
    env <- getCurDefs
    ids <- getExternalDeps
    pure RenamedModule {
      rmModule = m { mDef = mo },
      rmDefines = env,
      rmImported = ids
    }

-- | Rename the definition of a module.
renameModuleDef :: ModuleDefinition PName -> RenameM (ModuleDefinition Name)
renameModuleDef def =
  case def of
    NormalModule decls -> NormalModule <$> renameTopDecls decls
    FunctorInstance fun args _ -> undefined
    InterfaceModule sig -> undefined 

-- | Rename the top-level declarations of a module.
renameTopDecls :: [TopDecl PName] -> RenameM [TopDecl Name]
renameTopDecls decls =
  do
    mp <- getCurModPath
    defs' <- withSupply (defsOf (map (InModule (Just mp)) decls))
    mapM_ (recordError . OverlappingSyms) (findAmbig defs')
    setThisModuleDefs (forceUnambig defs')
    mapM_ doImport topImps
    renameDeclBlocks otherDecls
  where
  (topImps,otherDecls) = partition isTopImp decls
  isTopImp d =
    case d of
      DImport (Located { thing = Import { iModule = Located { thing = ImpTop {} } } }) -> True
      _ -> False

-- | Rename top-level declarations, assuming we've processed top-level imports.
renameDeclBlocks :: [TopDecl PName] -> RenameM [TopDecl Name]
renameDeclBlocks ds =
  -- XXX: also break on module to optionally add implicit imports
  case break isImport ds of
    (as,rest) ->
      do
        as' <- mapM renameTopDecl as
        case rest of
          [] -> pure as'
          imp : more ->
            do
              imp' <- doImport imp
              more' <- renameDeclBlocks more
              pure (imp' : more')
  where
  -- We assume that top-level imports were separated, see `findTopImports`.
  isImport d =
    case d of
      DImport {} -> True
      _ -> False


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


--------------------------------------------------------------------------------
-- Importing Stuff
--------------------------------------------------------------------------------

-- | The declaration should be an import. Add the names coming through
-- the import the current scope.
doImport :: TopDecl PName -> RenameM (TopDecl Name)
doImport d =
  case d of
    DImport limport ->
      do
        let imp = thing limport
        resMo <- resolveMod (thing (iModule imp))
        mo <- lookupMod resMo
        let isPub x = x `Set.member` modPublic mo
        case modKind mo of
          AModule ->
            addImported (interpImportEnv imp (filterUNames isPub (modDefines mo)))
          mk ->
            recordError (ModuleKindMismatch (srcRange limport) resMo AModule mk)
        let newI = imp { iModule = (iModule imp) { thing = resMo } }
        pure (DImport limport { thing = newI })
      where
      resolveMod mo =
        case mo of
          ImpNested pnm -> ImpNested <$> resolveNameUse NSModule pnm
          ImpTop nm ->
            do
              recordTopImport nm
              pure (ImpTop nm)
      
    _ -> panic "doImport" ["Not an import."]


-- | Process the definitions in the module, and add a `Mod` to the known modules.
doNestedModule :: NestedModule PName -> RenameM (NestedModule Name)
doNestedModule (NestedModule mo) =
  do
    nm   <- traverse (resolveNameDef NSModule) (mName mo)
    defs <- inSubmodule (nameIdent (thing nm)) (renameModuleDef (mDef mo))
    let newMo = mo { mName = nm, mDef = defs }
    addResolvedMod newMo
    pure (NestedModule newMo)


--------------------------------------------------------------------------------
-- Renaming
--------------------------------------------------------------------------------

-- | Rename a non-import top-level declaration
renameTopDecl :: TopDecl PName -> RenameM (TopDecl Name)
renameTopDecl = undefined


