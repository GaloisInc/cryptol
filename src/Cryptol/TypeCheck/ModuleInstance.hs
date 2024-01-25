{-# Language ImplicitParams, ConstraintKinds #-}
module Cryptol.TypeCheck.ModuleInstance where

import Data.Map(Map)
import qualified Data.Map as Map
import Data.Set(Set)
import qualified Data.Set as Set

import Cryptol.Parser.Position(Located)
import Cryptol.ModuleSystem.Interface(IfaceNames(..))
import Cryptol.ModuleSystem.NamingEnv(NamingEnv,mapNamingEnv)
import Cryptol.IR.TraverseNames(TraverseNames,mapNames)
import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Subst(Subst,TVars,apSubst)


{- | `?tVarSu` substitutes 'Type's for 'TVar's which are module type parameters.
     `?nameSu` substitutes fresh 'Name's for the functor's 'Name's
       (in all namespaces). -}
type Su = (?tVarSu :: Subst, ?nameSu :: Map Name Name)

-- | Instantiate something that has 'Name's.
doNameInst :: (Su, TraverseNames a) => a -> a
doNameInst = mapNames (\x -> Map.findWithDefault x x ?nameSu)

-- | Instantiate something that has 'TVar's.
doTVarInst :: (Su, TVars a) => a -> a
doTVarInst = apSubst ?tVarSu

-- | Instantiate something that has both 'TVar's and 'Name's.
-- Order is important here because '?tVarSu' might insert 'Name's.
doInst :: (Su, TVars a, TraverseNames a) => a -> a
doInst = doNameInst . doTVarInst

doMap :: (Su, ModuleInstance a) => Map Name a -> Map Name a
doMap mp =
  Map.fromList [ (moduleInstance x, moduleInstance d) | (x,d) <- Map.toList mp ]

doSet :: Su => Set Name -> Set Name
doSet = Set.fromList . map moduleInstance . Set.toList




class ModuleInstance t where
  moduleInstance :: Su => t -> t

instance ModuleInstance a => ModuleInstance [a] where
  moduleInstance = map moduleInstance

instance ModuleInstance a => ModuleInstance (Located a) where
  moduleInstance l = moduleInstance <$> l

instance ModuleInstance Name where
  moduleInstance = doNameInst

instance ModuleInstance NamingEnv where
  moduleInstance = mapNamingEnv doNameInst

instance ModuleInstance name => ModuleInstance (ImpName name) where
  moduleInstance x =
    case x of
      ImpTop t -> ImpTop t
      ImpNested n -> ImpNested (moduleInstance n)

instance ModuleInstance (ModuleG name) where
  moduleInstance m =
    Module { mName             = mName m
           , mDoc              = Nothing
           , mExports          = doNameInst (mExports m)
           , mParamTypes       = doMap (mParamTypes m)
           , mParamFuns        = doMap (mParamFuns m)
           , mParamConstraints = moduleInstance (mParamConstraints m)
           , mParams           = moduleInstance <$> mParams m
           , mFunctors         = doMap (mFunctors m)
           , mNested           = doSet (mNested m)
           , mTySyns           = doMap (mTySyns m)
           , mNewtypes         = doMap (mNewtypes m)
           , mPrimTypes        = doMap (mPrimTypes m)
           , mDecls            = moduleInstance (mDecls m)
           , mSubmodules       = doMap (mSubmodules m)
           , mSignatures       = doMap (mSignatures m)
           , mInScope          = moduleInstance (mInScope m)
           }

instance ModuleInstance Type where
  moduleInstance = doInst

instance ModuleInstance Schema where
  moduleInstance = doInst

instance ModuleInstance TySyn where
  moduleInstance ts =
    TySyn { tsName        = moduleInstance (tsName ts)
          , tsParams      = tsParams ts
          , tsConstraints = moduleInstance (tsConstraints ts)
          , tsDef         = moduleInstance (tsDef ts)
          , tsDoc         = tsDoc ts
          }

instance ModuleInstance Newtype where
  moduleInstance nt =
    Newtype { ntName        = moduleInstance (ntName nt)
            , ntParams      = ntParams nt
            , ntConstraints = moduleInstance (ntConstraints nt)
            , ntDef         = moduleInstance (ntDef nt)
            , ntDoc         = ntDoc nt
            }

instance ModuleInstance NewtypeDef where
  moduleInstance def =
    case def of
      Struct c -> Struct (moduleInstance c)
      Enum cs  -> Enum   (moduleInstance cs)

instance ModuleInstance StructCon where
  moduleInstance c =
    StructCon
      { ntConName     = moduleInstance (ntConName c)
      , ntFields      = moduleInstance <$> ntFields c
      }

instance ModuleInstance EnumCon where
  moduleInstance c =
    EnumCon
      { ecName        = moduleInstance (ecName c)
      , ecNumber      = ecNumber c
      , ecFields      = moduleInstance (ecFields c)
      , ecPublic      = ecPublic c
      , ecDoc         = ecDoc c
      }


instance ModuleInstance AbstractType where
  moduleInstance at =
    AbstractType { atName     = moduleInstance (atName at)
                 , atKind     = atKind at
                 , atCtrs     = let (ps,cs) = atCtrs at
                                in (ps, moduleInstance cs)
                 , atFixitiy  = atFixitiy at
                 , atDoc      = atDoc at
                 }

instance ModuleInstance DeclGroup where
  moduleInstance dg =
    case dg of
      Recursive ds    -> Recursive (moduleInstance ds)
      NonRecursive d -> NonRecursive (moduleInstance d)

instance ModuleInstance Decl where
  moduleInstance = doInst


instance ModuleInstance name => ModuleInstance (IfaceNames name) where
  moduleInstance ns =
    IfaceNames { ifsName     = moduleInstance (ifsName ns)
               , ifsNested   = doSet (ifsNested ns)
               , ifsDefines  = doSet (ifsDefines ns)
               , ifsPublic   = doSet (ifsPublic ns)
               , ifsDoc      = ifsDoc ns
               }

instance ModuleInstance ModParamNames where
  moduleInstance si =
    ModParamNames { mpnTypes       = doMap (mpnTypes si)
                  , mpnConstraints = moduleInstance (mpnConstraints si)
                  , mpnFuns        = doMap (mpnFuns si)
                  , mpnTySyn       = doMap (mpnTySyn si)
                  , mpnDoc         = mpnDoc si
                  }

instance ModuleInstance ModTParam where
  moduleInstance mp =
    ModTParam { mtpName = moduleInstance (mtpName mp)
              , mtpKind = mtpKind mp
              , mtpDoc  = mtpDoc mp
              }

instance ModuleInstance ModVParam where
  moduleInstance mp =
    ModVParam { mvpName   = moduleInstance (mvpName mp)
              , mvpType   = moduleInstance (mvpType mp)
              , mvpDoc    = mvpDoc mp
              , mvpFixity = mvpFixity mp
              }

instance ModuleInstance ModParam where
  moduleInstance p =
    ModParam { mpName        = mpName p
             , mpIface       = moduleInstance (mpIface p)
             , mpParameters  = moduleInstance (mpParameters p)
             , mpQual        = mpQual p
             }





