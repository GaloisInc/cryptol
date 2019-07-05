{-# Language FlexibleInstances, PatternGuards #-}
-- | Assumes that local names do not shadow top level names.
module Cryptol.ModuleSystem.InstantiateModule
  ( instantiateModule
  ) where

import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Map (Map)
import qualified Data.Map as Map
import           MonadLib(ReaderT,runReaderT,ask)

import Cryptol.Parser.Position(Located(..))
import Cryptol.ModuleSystem.Name
import Cryptol.ModuleSystem.Exports(ExportSpec(..))
import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Subst(listParamSubst, apSubst)
import Cryptol.Utils.Ident(ModName,modParamIdent)

{-
XXX: Should we simplify constraints in the instantiated modules?

If so, we also need to adjust the constraint parameters on terms appropriately,
especially when working with dictionaries.
-}


-- | Convert a module instantiation into a partial module.
-- The resulting module is incomplete because it is missing the definitions
-- from the instantiation.
instantiateModule :: FreshM m =>
                     Module           {- ^ Parametrized module -} ->
                     ModName          {- ^ Name of the new module -} ->
                     Map TParam Type  {- ^ Type params -} ->
                     Map Name Expr    {- ^ Value parameters -} ->
                     m ([Located Prop], Module)
                     -- ^ Instantiated constraints, fresh module, new supply
instantiateModule func newName tpMap vpMap =
  runReaderT newName $
    do let oldVpNames = Map.keys vpMap
       newVpNames <- mapM freshParamName (Map.keys vpMap)
       let vpNames = Map.fromList (zip oldVpNames newVpNames)

       env <- computeEnv func tpMap vpNames

       let rnMp :: Inst a => (a -> Name) -> Map Name a -> Map Name a
           rnMp f m = Map.fromList [ (f x, x) | a <- Map.elems m
                                              , let x = inst env a ]

           renamedExports  = inst env (mExports func)
           renamedTySyns   = rnMp tsName (mTySyns func)
           renamedNewtypes = rnMp ntName (mNewtypes func)
           renamedPrimTys  = rnMp atName (mPrimTypes func)

           su = listParamSubst (Map.toList (tyParamMap env))

           goals = map (fmap (apSubst su)) (mParamConstraints func)
           -- Constraints to discharge about the type instances

       let renamedDecls = inst env (mDecls func)
           paramDecls = map (mkParamDecl su vpNames) (Map.toList vpMap)

       return ( goals
              , Module
                 { mName              = newName
                 , mExports           = renamedExports
                 , mImports           = mImports func
                 , mTySyns            = renamedTySyns
                 , mNewtypes          = renamedNewtypes
                 , mPrimTypes         = renamedPrimTys
                 , mParamTypes        = Map.empty
                 , mParamConstraints  = []
                 , mParamFuns         = Map.empty
                 , mDecls             = paramDecls ++ renamedDecls
                 } )

  where
  mkParamDecl su vpNames (x,e) =
      NonRecursive Decl
        { dName        = Map.findWithDefault (error "OOPS") x vpNames
        , dSignature   = apSubst su
                       $ mvpType
                       $ Map.findWithDefault (error "UUPS") x (mParamFuns func)
        , dDefinition  = DExpr e
        , dPragmas     = []      -- XXX: which if any pragmas?
        , dInfix       = False   -- XXX: get from parameter?
        , dFixity      = Nothing -- XXX: get from parameter
        , dDoc         = Nothing -- XXX: get from parametr(or instance?)
        }


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

type InstM = ReaderT ModName

-- | Generate a new instance of a declared name.
freshenName :: FreshM m => Name -> InstM m Name
freshenName x =
  do m <- ask
     let sys = case nameInfo x of
                 Declared _ s -> s
                 _            -> UserName
     liftSupply (mkDeclared m sys (nameIdent x) (nameFixity x) (nameLoc x))

freshParamName :: FreshM m => Name -> InstM m Name
freshParamName x =
  do m <- ask
     let newName = modParamIdent (nameIdent x)
     liftSupply (mkDeclared m UserName newName (nameFixity x) (nameLoc x))




-- | Compute renaming environment from a module instantiation.
-- computeEnv :: ModInst -> InstM Env
computeEnv :: FreshM m =>
              Module {- ^ Functor being instantiated -} ->
              Map TParam Type {- replace type params by type -} ->
              Map Name Name {- replace value parameters by other names -} ->
              InstM m Env
computeEnv m tpMap vpMap =
  do tss <- mapM freshTy (Map.toList (mTySyns m))
     nts <- mapM freshTy (Map.toList (mNewtypes m))
     let tnMap = Map.fromList (tss ++ nts)

     defHere <- mapM mkVParam (Set.toList (defines (mDecls m)))
     let fnMap = Map.union vpMap (Map.fromList defHere)

     return Env { funNameMap  = fnMap
                , tyNameMap   = tnMap
                , tyParamMap  = tpMap
                }
  where
  freshTy (x,_) = do y <- freshenName x
                     return (x,y)

  mkVParam x = do y <- freshenName x
                  return (x,y)



--------------------------------------------------------------------------------
-- Do the renaming

data Env = Env
  { funNameMap  :: Map Name Name
  , tyNameMap   :: Map Name Name
  , tyParamMap  :: Map TParam Type
  } deriving Show


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
        ESet e x v                -> ESet (go e) x (go v)
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
                 , dName = Map.findWithDefault (dName d) (dName d)
                                                         (funNameMap env)
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
      TCNewtype x  -> TCNewtype (inst env x)
      TCAbstract x -> TCAbstract (inst env x)
      _            -> tc

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
  inst env ts = TySyn { tsName = instTyName env x
                      , tsParams = tsParams ts
                      , tsConstraints = inst env (tsConstraints ts)
                      , tsDef = inst env (tsDef ts)
                      , tsDoc = tsDoc ts
                      }
    where x = tsName ts

instance Inst Newtype where
  inst env nt = Newtype { ntName = instTyName env x
                        , ntParams = ntParams nt
                        , ntConstraints = inst env (ntConstraints nt)
                        , ntFields = [ (f,inst env t) | (f,t) <- ntFields nt ]
                        , ntDoc = ntDoc nt
                        }
    where x = ntName nt

instance Inst AbstractType where
  inst env a = AbstractType { atName    = instTyName env (atName a)
                            , atKind    = atKind a
                            , atCtrs    = case atCtrs a of
                                            (xs,ps) -> (xs, inst env ps)
                            , atFixitiy = atFixitiy a
                            , atDoc     = atDoc a
                            }

instTyName :: Env -> Name -> Name
instTyName env x = Map.findWithDefault x x (tyNameMap env)






