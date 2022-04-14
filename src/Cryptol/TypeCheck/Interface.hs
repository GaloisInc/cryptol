module Cryptol.TypeCheck.Interface where

import qualified Data.Map as Map
import Data.Set(Set)
import qualified Data.Set as Set

import Cryptol.Utils.Ident(Namespace(..))
import Cryptol.ModuleSystem.Interface
import Cryptol.ModuleSystem.Exports(allExported)
import Cryptol.TypeCheck.AST


mkIfaceDecl :: Decl -> IfaceDecl
mkIfaceDecl d = IfaceDecl
  { ifDeclName    = dName d
  , ifDeclSig     = dSignature d
  , ifDeclPragmas = dPragmas d
  , ifDeclInfix   = dInfix d
  , ifDeclFixity  = dFixity d
  , ifDeclDoc     = dDoc d
  }

genIfaceNames :: ModuleG name -> IfaceNames name
genIfaceNames m = IfaceNames
  { ifsName = mName m
  , ifsNested = mNested m
  , ifsDefines = genModDefines m
  , ifsPublic = allExported (mExports m)
  }

genModDefines :: ModuleG name -> Set Name
genModDefines m =
  Set.unions
    [ Map.keysSet  (mTySyns m)
    , Map.keysSet  (mNewtypes m)
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

-- | Generate an Iface from a typechecked module.
genIface :: ModuleG name -> IfaceG name
genIface m = Iface
  { ifNames = genIfaceNames m

  , ifPublic      = IfaceDecls
    { ifTySyns    = tsPub
    , ifNewtypes  = ntPub
    , ifAbstractTypes = atPub
    , ifDecls     = dPub
    , ifModules   = mPub
    , ifSignatures  = sPub
    , ifFunctors  = fPub
    }

  , ifPrivate = IfaceDecls
    { ifTySyns    = tsPriv
    , ifNewtypes  = ntPriv
    , ifAbstractTypes = atPriv
    , ifDecls     = dPriv
    , ifModules   = mPriv
    , ifSignatures  = sPriv
    , ifFunctors  = fPriv
    }

  , ifParams =
    if Map.null (mParams m)
      then -- old style
        let d = IfaceParams
                  { ifParamTypes = mParamTypes m
                  , ifParamConstraints = mParamConstraints m
                  , ifParamFuns  = mParamFuns m
                  , ifParamDoc = Nothing
                  }
        in if isEmptyIfaceParams d
             then Nothing
             else Just (OldStyle d)

      else Just (NewStyle (mParams m))


  }
  where

  (tsPub,tsPriv) =
      Map.partitionWithKey (\ qn _ -> qn `isExportedType` mExports m )
                          (mTySyns m)
  (ntPub,ntPriv) =
      Map.partitionWithKey (\ qn _ -> qn `isExportedType` mExports m )
                           (mNewtypes m)

  (atPub,atPriv) =
    Map.partitionWithKey (\qn _ -> qn `isExportedType` mExports m)
                         (mPrimTypes m)

  (dPub,dPriv) =
      Map.partitionWithKey (\ qn _ -> qn `isExportedBind` mExports m)
      $ Map.fromList [ (qn,mkIfaceDecl d) | dg <- mDecls m
                                          , d  <- groupDecls dg
                                          , let qn = dName d
                                          ]

  (mPub,mPriv) =
      Map.partitionWithKey (\ qn _ -> isExported NSModule qn (mExports m))
      $ mSubmodules m

  (sPub,sPriv) =
      Map.partitionWithKey (\ qn _ -> isExported NSSignature qn (mExports m))
      $ mSignatures m

  (fPub,fPriv) =
      Map.partitionWithKey (\ qn _ -> isExported NSModule qn (mExports m))
      $ (genIface <$> mFunctors m)


