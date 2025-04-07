{-# Language ImplicitParams #-}
module Cryptol.IR.TraverseNames where

import Data.Set(Set)
import qualified Data.Set as Set
import Data.Functor.Identity

import Cryptol.ModuleSystem.Name(nameUnique)
import Cryptol.Utils.RecordMap(traverseRecordMap)
import Cryptol.Parser.Position(Located(..))
import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.FFI.FFIType

traverseNames ::
  (TraverseNames t, Applicative f) => (Name -> f Name) -> (t -> f t)
traverseNames f = let ?name = f in traverseNamesIP

mapNames :: (TraverseNames t) => (Name -> Name) -> t -> t
mapNames f x = result
  where
  Identity result = let ?name = pure . f
                    in traverseNamesIP x

class TraverseNames t where
  traverseNamesIP :: (Applicative f, ?name :: Name -> f Name) => t -> f t

instance TraverseNames a => TraverseNames [a] where
  traverseNamesIP = traverse traverseNamesIP

instance TraverseNames a => TraverseNames (Maybe a) where
  traverseNamesIP = traverse traverseNamesIP

instance (Ord a, TraverseNames a) => TraverseNames (Set a) where
  traverseNamesIP = fmap Set.fromList . traverseNamesIP . Set.toList

instance TraverseNames a => TraverseNames (Located a) where
  traverseNamesIP (Located r a) = Located r <$> traverseNamesIP a

instance TraverseNames Name where
  traverseNamesIP = ?name

instance (Ord a, TraverseNames a) => TraverseNames (ExportSpec a) where
  traverseNamesIP (ExportSpec mp) = ExportSpec <$> traverse traverseNamesIP mp

instance TraverseNames Expr where
  traverseNamesIP expr =
    case expr of
      EList es t        -> EList  <$> traverseNamesIP es <*> traverseNamesIP t

      ETuple es         -> ETuple <$> traverseNamesIP es

      ERec mp           -> ERec <$> traverseRecordMap (\_ -> traverseNamesIP) mp

      ESel e l          -> (`ESel` l) <$> traverseNamesIP e

      ESet t e1 l e2    -> ESet <$> traverseNamesIP t
                                <*> traverseNamesIP e1
                                <*> pure l
                                <*> traverseNamesIP e2

      EIf e1 e2 e3      -> EIf <$> traverseNamesIP e1
                               <*> traverseNamesIP e2
                               <*> traverseNamesIP e3
      ECase e as d      -> ECase <$> traverseNamesIP e
                                 <*> traverse traverseNamesIP as
                                 <*> traverse traverseNamesIP d

      EComp t1 t2 e mss -> EComp <$> traverseNamesIP t1
                                 <*> traverseNamesIP t2
                                 <*> traverseNamesIP e
                                 <*> traverseNamesIP mss

      EVar x            -> EVar <$> traverseNamesIP x
      ETAbs tp e        -> ETAbs <$> traverseNamesIP tp <*> traverseNamesIP e
      ETApp e t         -> ETApp <$> traverseNamesIP e <*> traverseNamesIP t
      EApp e1 e2        -> EApp <$> traverseNamesIP e1 <*> traverseNamesIP e2
      EAbs x t e        -> EAbs <$> traverseNamesIP x
                                <*> traverseNamesIP t
                                <*> traverseNamesIP e
      ELocated r e      -> ELocated r <$> traverseNamesIP e
      EProofAbs p e     -> EProofAbs <$> traverseNamesIP p <*> traverseNamesIP e
      EProofApp e       -> EProofApp <$> traverseNamesIP e
      EWhere e ds       -> EWhere <$> traverseNamesIP e <*> traverseNamesIP ds

      EPropGuards gs t  -> EPropGuards <$> traverse doG gs <*> traverseNamesIP t
        where doG (xs, e) = (,) <$> traverseNamesIP xs <*> traverseNamesIP e

instance TraverseNames CaseAlt where
  traverseNamesIP (CaseAlt xs e) =
    CaseAlt <$> traverse doPair xs <*> traverseNamesIP e
      where doPair (x,y) = (,) <$> traverseNamesIP x <*> traverseNamesIP y

instance TraverseNames Match where
  traverseNamesIP mat =
    case mat of
      From x t1 t2 e -> From <$> traverseNamesIP x
                             <*> traverseNamesIP t1
                             <*> traverseNamesIP t2
                             <*> traverseNamesIP e
      Let d          -> Let <$> traverseNamesIP d

instance TraverseNames DeclGroup where
  traverseNamesIP dg =
    case dg of
      NonRecursive d -> NonRecursive <$> traverseNamesIP d
      Recursive ds   -> Recursive    <$> traverseNamesIP ds

instance TraverseNames Decl where
  traverseNamesIP decl = mk <$> traverseNamesIP (dName decl)
                            <*> traverseNamesIP (dSignature decl)
                            <*> traverseNamesIP (dDefinition decl)
    where mk nm sig def = decl { dName = nm
                               , dSignature = sig
                               , dDefinition = def
                               }

instance TraverseNames DeclDef where
  traverseNamesIP d =
    case d of
      DPrim   -> pure d
      DForeign t me -> DForeign <$> traverseNamesIP t <*> traverseNamesIP me
      DExpr e -> DExpr <$> traverseNamesIP e

instance TraverseNames FFI where
  traverseNamesIP f =
    case f of
      CallC t -> CallC <$> traverseNamesIP t
      CallAbstract t -> CallAbstract <$> traverseNamesIP t

instance TraverseNames Schema where
  traverseNamesIP (Forall as ps t) =
    Forall <$> traverseNamesIP as
           <*> traverseNamesIP ps
           <*> traverseNamesIP t

instance TraverseNames TParam where
  traverseNamesIP tp = mk <$> traverseNamesIP (tpFlav tp)
                          <*> traverseNamesIP (tpInfo tp)
    -- XXX: module parameters should probably be represented directly
    -- as (abstract) user-defined types, rather than type variables.
    where mk f i = case f of
                     TPModParam x ->
                      tp { tpUnique = nameUnique x, tpFlav = f, tpInfo = i }
                     _ -> tp { tpFlav = f, tpInfo = i }


instance TraverseNames TPFlavor where
  traverseNamesIP tpf =
    case tpf of
      TPModParam x      -> TPModParam     <$> traverseNamesIP x
      TPUnifyVar        -> pure tpf
      TPSchemaParam x   -> TPSchemaParam  <$> traverseNamesIP x
      TPTySynParam x    -> TPTySynParam   <$> traverseNamesIP x
      TPPropSynParam x  -> TPPropSynParam <$> traverseNamesIP x
      TPNominalParam x  -> TPNominalParam <$> traverseNamesIP x
      TPPrimParam x     -> TPPrimParam    <$> traverseNamesIP x

instance TraverseNames TVarInfo where
  traverseNamesIP (TVarInfo r s) = TVarInfo r <$> traverseNamesIP s

instance TraverseNames TypeSource where
  traverseNamesIP src =
    case src of
      TVFromModParam x            -> TVFromModParam <$> traverseNamesIP x
      TVFromSignature x           -> TVFromSignature <$> traverseNamesIP x
      TypeWildCard                -> pure src
      TypeOfRecordField {}        -> pure src
      TypeOfTupleField {}         -> pure src
      TypeOfSeqElement            -> pure src
      LenOfSeq                    -> pure src
      TypeParamInstNamed x i      -> TypeParamInstNamed <$> traverseNamesIP x
                                                        <*> pure i
      TypeParamInstPos   x i      -> TypeParamInstPos   <$> traverseNamesIP x
                                                        <*> pure i
      DefinitionOf x              -> DefinitionOf <$> traverseNamesIP x
      LenOfCompGen                -> pure src
      TypeOfArg arg               -> TypeOfArg <$> traverseNamesIP arg
      TypeOfRes                   -> pure src
      FunApp                      -> pure src
      TypeOfIfCondExpr            -> pure src
      TypeFromUserAnnotation      -> pure src
      GeneratorOfListComp         -> pure src
      TypeErrorPlaceHolder        -> pure src
      CasedExpression             -> pure src
      ConPat                      -> pure src

instance TraverseNames ArgDescr where
  traverseNamesIP arg = mk <$> traverseNamesIP (argDescrFun arg)
    where mk n = arg { argDescrFun = n }

instance TraverseNames Type where
  traverseNamesIP ty =
    case ty of
      TCon tc ts    -> TCon tc <$> traverseNamesIP ts
      TVar x        -> TVar <$> traverseNamesIP x
      TUser x ts t  -> TUser <$> traverseNamesIP x
                             <*> traverseNamesIP ts
                             <*> traverseNamesIP t
      TRec rm       -> TRec <$> traverseRecordMap (const traverseNamesIP) rm
      TNominal nt ts -> TNominal <$> traverseNamesIP nt <*> traverseNamesIP ts


instance TraverseNames TVar where
  traverseNamesIP tvar =
    case tvar of
      TVFree x k ys i -> TVFree x k <$> traverseNamesIP ys <*> traverseNamesIP i
      TVBound x       -> TVBound <$> traverseNamesIP x

instance TraverseNames NominalType where
  traverseNamesIP nt =
    NominalType
      <$> traverseNamesIP (ntName nt)
      <*> traverseNamesIP (ntParams nt)
      <*> pure (ntKind nt)
      <*> traverseNamesIP (ntConstraints nt)
      <*> traverseNamesIP (ntDef nt)
      <*> pure (ntFixity nt)
      <*> pure (ntDoc nt)

instance TraverseNames NominalTypeDef where
  traverseNamesIP def =
    case def of
      Struct c -> Struct <$> traverseNamesIP c
      Enum cs  -> Enum   <$> traverseNamesIP cs
      Abstract -> pure Abstract

instance TraverseNames StructCon where
  traverseNamesIP c =
    StructCon <$> traverseNamesIP (ntConName c)
              <*> traverseRecordMap (const traverseNamesIP) (ntFields c)

instance TraverseNames EnumCon where
  traverseNamesIP c =
    EnumCon <$> traverseNamesIP (ecName c)
            <*> pure (ecNumber c)
            <*> traverseNamesIP (ecFields c)
            <*> pure (ecPublic c)
            <*> pure (ecDoc c)



instance TraverseNames ModTParam where
  traverseNamesIP nt = mk <$> traverseNamesIP (mtpName nt)
    where
    mk x = nt { mtpName = x }

instance TraverseNames ModVParam where
  traverseNamesIP nt = mk <$> traverseNamesIP (mvpName nt)
                          <*> traverseNamesIP (mvpType nt)
    where
    mk x t = nt { mvpName = x, mvpType = t }

instance TraverseNames t => TraverseNames (FFIFunType t) where
  traverseNamesIP fi = mk <$> traverseNamesIP (ffiArgTypes fi)
                          <*> traverseNamesIP (ffiRetType fi)
    where
    mk as b =
      FFIFunType
        { ffiTParams  = ffiTParams fi
        , ffiArgTypes = as
        , ffiRetType  = b
        }

instance TraverseNames FFIType where
  traverseNamesIP ft =
    case ft of
      FFIBool       -> pure ft
      FFIBasic _    -> pure ft   -- assumes no names here
      FFIArray sz t -> (`FFIArray` t) <$> traverseNamesIP sz
      FFITuple ts   -> FFITuple  <$> traverseNamesIP ts
      FFIRecord mp  -> FFIRecord <$> traverseRecordMap
                                                (\_ -> traverseNamesIP) mp
instance TraverseNames TySyn where
  traverseNamesIP ts = mk <$> traverseNamesIP (tsName ts)
                          <*> traverseNamesIP (tsParams ts)
                          <*> traverseNamesIP (tsConstraints ts)
                          <*> traverseNamesIP (tsDef ts)
    where mk n ps cs t =
            TySyn  { tsName        = n
                   , tsParams      = ps
                   , tsConstraints = cs
                   , tsDef         = t
                   , tsDoc         = tsDoc ts
                   }


