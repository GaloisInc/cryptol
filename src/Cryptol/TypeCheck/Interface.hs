module Cryptol.TypeCheck.Interface where

import qualified Data.Map as Map

import Cryptol.Utils.Ident(Namespace(..))
import Cryptol.ModuleSystem.Interface
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

-- | Generate an Iface from a typechecked module.
genIface :: ModuleG mname -> IfaceG mname
genIface m = Iface
  { ifModName = mName m

  , ifPublic      = IfaceDecls
    { ifTySyns    = tsPub
    , ifNewtypes  = ntPub
    , ifAbstractTypes = atPub
    , ifDecls     = dPub
    , ifModules   = mPub
    , ifSignatures  = sPub
    }

  , ifPrivate = IfaceDecls
    { ifTySyns    = tsPriv
    , ifNewtypes  = ntPriv
    , ifAbstractTypes = atPriv
    , ifDecls     = dPriv
    , ifModules   = mPriv
    , ifSignatures  = sPriv
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
      $ mSubModules m

  (sPub,sPriv) =
      Map.partitionWithKey (\ qn _ -> isExported NSSignature qn (mExports m))
      $ mSignatures m


