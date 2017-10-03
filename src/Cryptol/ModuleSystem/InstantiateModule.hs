{-# Language FlexibleInstances, PatternGuards #-}
-- | Assumes that local names do not shadow top level names.
module Cryptol.ModuleSystem.InstantiateModule
  ( instantiateModule
  ) where

import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Map (Map)
import qualified Data.Map as Map
import           MonadLib(Id,ReaderT,runReaderT,runId,ask)

import Cryptol.ModuleSystem.Name
import Cryptol.ModuleSystem.Exports(ExportSpec(..))
import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Subst(listSubst, apSubst)
import Cryptol.Utils.Ident(ModName)
import Cryptol.Utils.Panic(panic)



{-
XXX: Should we simplify constraints in the instantiated modules?

If so, we also need to adjust the constraint parameters appropriately,
especially when working with dictionaries.
-}


-- | Convert a module instantiation into an actual module.
instantiateModule :: Supply {- ^ To generate fresh names -} ->
                      Module {- ^ Parametrized module -} ->
                      Module {- ^ Instantiating module -} ->
                      ([Prop], Module, Supply) -- XXX: errors
instantiateModule = undefined {-
instantiateModule s func mi = (ps, m, s1)
  where
  ((ps,m),s1) = runInstM (mName mi) s $
    do env <- computeEnv mi
       let renamedExports = inst env (mExports func)
           renamedTySyns   = fmap (inst env) (mTySyns func)
           renamedNewtypes = fmap (inst env) (mNewtypes func)

           su = listSubst
                  [ (TVBound tp, t) | (tp,t) <- Map.toList (tyParamMap env) ]

           goals = apSubst su (mParamConstraints func)
           -- Constraints to discharge about the type instances

       let renamedDecls = inst env (mDecls func)

       return ( goals
              , Module
                 { mName              = mName mi
                 , mExports           = renamedExports

                 , mImports           = mImports func ++ mImports mi
                   -- There just record all the dependencies for the
                   -- instantiated module.  Note that the resulting list
                   -- of imports is not necessarily good for resolving names
                   -- as things which were unambiguous separately may clash
                   -- when merged.  Since things have already been renamed,
                   -- we don't worry about this for the moment.


                 , mTySyns            = Map.union (mTySyns mi) renamedTySyns
                 , mNewtypes          = Map.union (mNewtypes mi) renamedNewtypes
                 , mParamTypes        = mParamTypes mi
                 , mParamConstraints  = mParamConstraints mi
                 , mParamFuns         = mParamFuns mi
                 , mDecls             = mDecls mi ++ renamedDecls
                 } )


type Error = String

findParams :: Module {- ^ Functor -} ->
              Module {- ^ Instnace -} ->
              Either Error (Map TParam Type, Map Name Expr)
findParams = undefined
-}

--------------------------------------------------------------------------------
-- Things that need to be renamed

class Defines t where
  defines :: t -> Set Name

instance Defines t => Defines [t] where
  defines = Set.unions . map defines

instance Defines Decl where
  defines = Set.singleton . dName

instance Defines DeclGroup where
  defines d =
    case d of
      NonRecursive x -> defines x
      Recursive x    -> defines x


--------------------------------------------------------------------------------

type InstM = ReaderT ModName (SupplyT Id)

runInstM :: ModName -> Supply -> InstM a -> (a, Supply)
runInstM mn s = runId . runSupplyT s . runReaderT mn


-- | Generate a new instance of a declared name.
freshenName :: Name -> InstM Name
freshenName x =
  do m <- ask
     liftSupply (mkDeclared m (nameIdent x) (nameFixity x) (nameLoc x))

{-
-- | Compute renaming environment from a module instantiation.
-- computeEnv :: ModInst -> InstM Env
computeEnv :: Module {- ^ Parametrized module -} ModInst -> InstM Env
computeEnv m =
  do tss <- mapM freshTy (Map.toList (mTySyns m))
     nts <- mapM freshTy (Map.toList (mNewtypes m))
     let tnMap = Map.fromList (tss ++ nts)

     tps <- mapM mkTParam (mParamTypes m)
     let tpMap = Map.fromList tps

     defHere <- mapM mkVParam (Set.toList (defines (mDecls m)))
     vps     <- mapM mkVParam (Map.keys (mParamFuns m))
     let fnMap = Map.fromList (vps ++ defHere)

     return Env { funNameMap  = fnMap
                , tyNameMap   = tnMap
                , tyParamMap  = tpMap
                }
  where
  freshTy (x,_) = do y <- freshenName x
                     return (x,y)

  mkVParam x = do y <- freshenName x
                  return (x,y)

  mkTParam tp =
    case tpName tp of
      Nothing -> panic "computeEnv" ["Type param with no name"]
      Just x ->
        case Map.lookup tp (modInstTyParams mi) of
          Nothing -> panic "computeEnv"
                            ["Missing definition for type parameter"]
          Just t ->
            do y <- freshenName x
               return (tp, TUser y [] t)
-}

--------------------------------------------------------------------------------
-- Do the renaming

data Env = Env
  { funNameMap  :: Map Name Name
  , tyNameMap   :: Map Name Name
  , tyParamMap  :: Map TParam Type
  }


class Inst t where
  inst :: Env -> t -> t

instance Inst a => Inst [a] where
  inst env = map (inst env)

instance Inst Expr where
  inst env = go
    where
    go expr =
      case expr of
        EVar x -> case Map.lookup x (funNameMap env) of
                    Just y -> EVar y
                    _      -> expr

        EList xs t                -> EList (inst env xs) (inst env t)
        ETuple es                 -> ETuple (inst env es)
        ERec xs                   -> ERec [ (f,go e) | (f,e) <- xs ]
        ESel e s                  -> ESel (go e) s
        EIf e1 e2 e3              -> EIf (go e1) (go e2) (go e3)
        EComp t1 t2 e mss         -> EComp (inst env t1) (inst env t2)
                                           (go e)
                                           (inst env mss)
        ETAbs t e                 -> ETAbs t (go e)
        ETApp e t                 -> ETApp (go e) (inst env t)
        EApp e1 e2                -> EApp (go e1) (go e2)
        EAbs x t e                -> EAbs x (inst env t) (go e)
        EProofAbs p e             -> EProofAbs (inst env p) (go e)
        EProofApp e               -> EProofApp (go e)
        EWhere e ds               -> EWhere (go e) (inst env ds)


instance Inst DeclGroup where
  inst env dg =
    case dg of
      NonRecursive d -> NonRecursive (inst env d)
      Recursive ds   -> Recursive (inst env ds)

instance Inst DeclDef where
  inst env d =
    case d of
      DPrim   -> DPrim
      DExpr e -> DExpr (inst env e)

instance Inst Decl where
  inst env d = d { dSignature = inst env (dSignature d)
                 , dDefinition = inst env (dDefinition d)
                 }

instance Inst Match where
  inst env m =
    case m of
      From x t1 t2 e -> From x (inst env t1) (inst env t2) (inst env e)
      Let d          -> Let (inst env d)

instance Inst Schema where
  inst env s = s { sProps = inst env (sProps s)
                 , sType  = inst env (sType s)
                 }

instance Inst Type where
  inst env ty =
    case ty of
      TCon tc ts    -> TCon (inst env tc) (inst env ts)
      TVar tv       ->
        case tv of
          TVBound tp | Just t <- Map.lookup tp (tyParamMap env) -> t
          _ -> ty
      TUser x ts t  -> TUser y (inst env ts) (inst env t)
        where y = Map.findWithDefault x x (tyNameMap env)
      TRec fs       -> TRec [ (f, inst env t) | (f,t) <- fs ]

instance Inst TCon where
  inst env tc =
    case tc of
      TC x -> TC (inst env x)
      _    -> tc

instance Inst TC where
  inst env tc =
    case tc of
      TCNewtype x -> TCNewtype (inst env x)
      _           -> tc

instance Inst UserTC where
  inst env (UserTC x t) = UserTC y t
    where y = Map.findWithDefault x x (tyNameMap env)

instance Inst (ExportSpec Name) where
  inst env es = ExportSpec { eTypes = Set.map instT (eTypes es)
                           , eBinds = Set.map instV (eBinds es)
                           }
    where instT x = Map.findWithDefault x x (tyNameMap env)
          instV x = Map.findWithDefault x x (funNameMap env)

instance Inst TySyn where
  inst env ts = TySyn { tsName = Map.findWithDefault x x (tyNameMap env)
                      , tsParams = tsParams ts
                      , tsConstraints = inst env (tsConstraints ts)
                      , tsDef = inst env (tsDef ts)
                      , tsDoc = tsDoc ts
                      }
    where x = tsName ts

instance Inst Newtype where
  inst env nt = Newtype { ntName = Map.findWithDefault x x (tyNameMap env)
                        , ntParams = ntParams nt
                        , ntConstraints = inst env (ntConstraints nt)
                        , ntFields = [ (f,inst env t) | (f,t) <- ntFields nt ]
                        , ntDoc = ntDoc nt
                        }
    where x = ntName nt








