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


{- | `?tSu` should be applied to all types.
     `?vSu` shoudl be applied to all values. -}
type Su = (?tSu :: Subst, ?vSu :: Map Name Name)

-- | Has value names but no types.
doVInst :: (Su, TraverseNames a) => a -> a
doVInst = mapNames (\x -> Map.findWithDefault x x ?vSu)

-- | Has types but not values.
doTInst :: (Su, TVars a) => a -> a
doTInst = apSubst ?tSu

-- | Has both value names and types.
doTVInst :: (Su, TVars a, TraverseNames a) => a -> a
doTVInst = doVInst . doTInst

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
  moduleInstance = doVInst

instance ModuleInstance NamingEnv where
  moduleInstance = mapNamingEnv doVInst

instance ModuleInstance name => ModuleInstance (ImpName name) where
  moduleInstance x =
    case x of
      ImpTop t -> ImpTop t
      ImpNested n -> ImpNested (moduleInstance n)

instance ModuleInstance (ModuleG name) where
  moduleInstance m =
    Module { mName             = mName m
           , mDoc              = Nothing
           , mExports          = doVInst (mExports m)
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
  moduleInstance = doTInst

instance ModuleInstance Schema where
  moduleInstance = doTInst

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
            , ntConName     = moduleInstance (ntConName nt)
            , ntFields      = moduleInstance <$> ntFields nt
            , ntDoc         = ntDoc nt
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
  moduleInstance = doTVInst


instance ModuleInstance name => ModuleInstance (IfaceNames name) where
  moduleInstance ns =
    IfaceNames { ifsName     = moduleInstance (ifsName ns)
               , ifsNested   = doSet (ifsNested ns)
               , ifsDefines  = doSet (ifsDefines ns)
               , ifsPublic   = doSet (ifsPublic ns)
               , ifsInScope  = moduleInstance (ifsInScope ns)
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





