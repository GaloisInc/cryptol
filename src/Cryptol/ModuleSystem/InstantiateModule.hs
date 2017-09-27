-- | Assumes that local names do not shadow top level names.
module Cryptol.ModuleSystem.InstantiateModule (instantiateModule) where

import Data.Set (Set)
import qualified Data.Set as Set

import Cryptol.ModuleSystem.Name
import Cryptol.TypeCheck.AST

instantiateModule ::
  Supply           {- ^ Use to generate fresh names -} ->
  Module           {- ^ This is the functor the instantiate -} ->
  Map TParam Type  {- ^ Definitions of type parameters -} ->
  Map Name Expr    {- ^ Definitions of function parameters -} ->
  (Module,Supply)
instantiateModule = undefined

type InstM = IO

data Env = Env
  { funNameMap  :: Map Name Name
  , tyNameMap   :: Map Name Name
  , tyParamMap  :: Map TParam Name
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
        EVar x                    -> undefined

        EList xs t                -> EList (go xs) (inst env t)
        ETuple es                 -> ETuple (go es)
        ERec xs                   -> ERec [ (f,go e) | (f,e) <- xs ]
        ESel e s                  -> ESel (go e) s
        EIf e1 e2 e3              -> EIf (go e1) (go e2) (go e3)
        EComp t1 t2 e mss         -> EComp (inst env t1) (inst env t2)
                                           (go e)
                                           (inst mss)
        ETAbs t e                 -> ETAbs t (go e)
        ETApp e t                 -> ETApp (go e) (inst env t)
        EApp e1 e2                -> EApp (go e1) (go e2)
        EAbs x t e                -> EAbs x (inst env t) (go e)
        EProofAbs p e             -> EProofAbs (inst env t) (go e)
        EProofApp e               -> EProofApp (go e)
        EWhere e ds               -> EWhere (go e) (inst env ds)


instance Inst DeclGroup where
  inst env d =
    case d of
      NonRecursive d -> NonRecursive (inst env d)
      Recursive ds   -> Recursive (inst env ds)

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
      TVar tv       -> undefined
      TUser x ts t  -> TUser (undefined x) (inst env ts) (inst env t)
      TRec fs       -> TRec [ (f, inst env t) | (f,t) <- fs ]



class Defines t where
  defines :: t -> Set Name

instance Defines t => Defines [t]
  defines = Set.unoins . map defines

instance Defines Decl where
  defines = Set.singleton . dName

instance Defines DeclGroup where
  defines d =
    case d of
      NonRecursive x -> defines x
      Recursive x    -> defines x

