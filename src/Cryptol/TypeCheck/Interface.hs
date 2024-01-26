{-# LANGUAGE Safe #-}

module Cryptol.TypeCheck.Interface where

import qualified Data.Map as Map
import Data.Set(Set)
import qualified Data.Set as Set

import Cryptol.ModuleSystem.Interface
import Cryptol.ModuleSystem.Exports(allExported)
import Cryptol.TypeCheck.AST


-- | Information about a declaration to be stored an in interface.
mkIfaceDecl :: Decl -> IfaceDecl
mkIfaceDecl d = IfaceDecl
  { ifDeclName    = dName d
  , ifDeclSig     = dSignature d
  , ifDeclIsPrim  = case dDefinition d of
                      DPrim {} -> True
                      _        -> False
  , ifDeclPragmas = dPragmas d
  , ifDeclInfix   = dInfix d
  , ifDeclFixity  = dFixity d
  , ifDeclDoc     = dDoc d
  }

-- | Compute information about the names in a module.
genIfaceNames :: ModuleG name -> IfaceNames name
genIfaceNames m = IfaceNames
  { ifsName     = mName m
  , ifsNested   = mNested m
  , ifsDefines  = genModDefines m
  , ifsPublic   = allExported (mExports m)
  , ifsDoc      = mDoc m
  }

-- | Things defines by a module
genModDefines :: ModuleG name -> Set Name
genModDefines m =
  Set.unions
    [ Map.keysSet  (mTySyns m)
    , Map.keysSet  (mNominalTypes m)
    , Set.fromList (concatMap (map fst . nominalTypeConTypes)
                              (Map.elems (mNominalTypes m)))
    , Map.keysSet  (mPrimTypes m)
    , Set.fromList (map dName (concatMap groupDecls (mDecls m)))
    , Map.keysSet  (mSubmodules m)
    , Map.keysSet  (mFunctors m)
    , Map.keysSet  (mSignatures m)
    ] `Set.difference` nestedInSet (mNested m)
  where
  nestedInSet = Set.unions . map inNested . Set.toList
  inNested x  = case Map.lookup x (mSubmodules m) of
                  Just y  -> ifsDefines y `Set.union` nestedInSet (ifsNested y)
                  Nothing -> Set.empty -- must be signature or a functor

genIface :: ModuleG name -> IfaceG name
genIface m = genIfaceWithNames (genIfaceNames m) m

-- | Generate an Iface from a typechecked module.
genIfaceWithNames :: IfaceNames name -> ModuleG ignored -> IfaceG name
genIfaceWithNames names m =
  Iface
  { ifNames       = names

  , ifDefines = IfaceDecls
    { ifTySyns          = mTySyns m
    , ifNominalTypes    = mNominalTypes m
    , ifAbstractTypes   = mPrimTypes m
    , ifDecls           = Map.fromList [ (qn,mkIfaceDecl d)
                                       | dg <- mDecls m
                                       , d  <- groupDecls dg
                                       , let qn = dName d
                                       ]
    , ifModules         = mSubmodules m
    , ifSignatures      = mSignatures m
    , ifFunctors        = genIface <$> mFunctors m
    }

  , ifParams = mParams m
  }


