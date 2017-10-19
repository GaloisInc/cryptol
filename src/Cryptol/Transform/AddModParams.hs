-- | Transformed a parametrized module into an ordinary module
-- where everything is parameterized by the module's parameters.
module Cryptol.Transform.AddModParams (addModParams) where

import qualified Data.Map as Map
import           Data.Set ( Set )
import qualified Data.Set as Set

import Cryptol.TypeCheck.AST
import Cryptol.Parser.Position(thing)

addModParams :: Module -> Maybe Module
addModParams m =
  do ps <- getParams m
     let toInst = Set.unions ( Map.keysSet (mTySyns m)
                             : Map.keysSet (mNewtypes m)
                             : map defs (mDecls m)
                             )
         inp = (toInst, ps)

     return m { mTySyns = fmap (fixUp inp) (mTySyns m)
              , mNewtypes = fmap (fixUp inp) (mNewtypes m)
              , mDecls = fixUp inp (mDecls m)
              , mParamTypes = []
              , mParamConstraints = []
              , mParamFuns = Map.empty
              }

defs :: DeclGroup -> Set Name
defs dg =
  case dg of
    Recursive ds -> Set.fromList (map dName ds)
    NonRecursive d -> Set.singleton (dName d)

fixUp :: (AddParams a, Inst a) => Inp -> a -> a
fixUp i = addParams (snd i) . inst i

--------------------------------------------------------------------------------

data Params = Params
  { pTypes            :: [TParam]
  , pTypeConstraints  :: [Prop]
  , pFuns             :: [(Name,Type)]
  }


-- XXX: do we need to change the flavor of the parameter?
getParams :: Module -> Maybe Params
getParams m =
  do pfs <- mapM checkFunP (Map.toList (mParamFuns m))
     return Params { pTypes = mParamTypes m
                   , pTypeConstraints = map thing (mParamConstraints m)
                   , pFuns = pfs
                   }
  where
  checkFunP (x,s) = do t <- isMono s
                       return (x,t)


--------------------------------------------------------------------------------

class AddParams a where
  addParams :: Params -> a -> a

instance AddParams a => AddParams [a] where
  addParams ps = map (addParams ps)

instance AddParams Schema where
  addParams ps s = s { sVars  = pTypes ps ++ sVars s
                     , sProps = pTypeConstraints ps ++ sProps s
                     , sType  = addParams ps (sType s)
                     }

instance AddParams Type where
  addParams ps t = foldr tFun t (map snd (pFuns ps))


instance AddParams Expr where
  addParams ps e = foldr ETAbs withProps (pTypes ps)
    where withProps = foldr EProofAbs withArgs (pTypeConstraints ps)
          withArgs  = foldr (uncurry EAbs) e (pFuns ps)


instance AddParams DeclGroup where
  addParams ps dg =
    case dg of
      Recursive ds -> Recursive (addParams ps ds)
      NonRecursive d -> NonRecursive (addParams ps d)

instance AddParams Decl where
  addParams ps d =
    case dDefinition d of
      DPrim   -> d
      DExpr e -> d { dSignature = addParams ps (dSignature d)
                   , dDefinition = DExpr (addParams ps e)
                   }

instance AddParams TySyn where
  addParams ps ts = ts { tsParams = pTypes ps ++ tsParams ts
                       , tsConstraints = pTypeConstraints ps ++ tsConstraints ts
                          -- do we need these here?
                       }

instance AddParams Newtype where
  addParams ps nt = nt { ntParams = pTypes ps ++ ntParams nt
                       , ntConstraints = pTypeConstraints ps ++ ntConstraints nt
                       }



--------------------------------------------------------------------------------


-- | Adjust uses of names to account for the new parameters.
-- Assumes unique names---no capture or shadowing.
class Inst a where
  inst :: Inp -> a -> a

-- | Set of top-level names which need to be instantiate, and module parameters.
type Inp = (Set Name, Params)


nameInst :: Inp -> Name -> Expr
nameInst (_,ps) x = foldl ETApp withProofs (map (TVar . tpVar) (pTypes ps))
  where withProofs = foldl (\e _ -> EProofApp e) withArgs (pTypeConstraints ps)
        withArgs = foldl EApp (EVar x) (map (EVar . fst) (pFuns ps))

-- | Extra parameters to dd when instantiating a type
instTyParams :: Inp -> [Type]
instTyParams (_,ps) = map (TVar . tpVar) (pTypes ps)


needsInst :: Inp -> Name -> Bool
needsInst (xs,_) x = Set.member x xs



instance Inst a => Inst [a] where
  inst ps = map (inst ps)

instance Inst Expr where
  inst ps expr =
    case expr of
     EVar x -> if needsInst ps x then nameInst ps x else EVar x

     EList es t -> EList (inst ps es) (inst ps t)
     ETuple es -> ETuple (inst ps es)
     ERec fs   -> ERec [ (f,inst ps e) | (f,e) <- fs ]
     ESel e s  -> ESel (inst ps e) s

     EIf e1 e2 e3 -> EIf (inst ps e1) (inst ps e2) (inst ps e3)
     EComp t1 t2 e ms -> EComp (inst ps t1) (inst ps t2)
                               (inst ps e) (inst ps ms)

     ETAbs x e -> ETAbs x (inst ps e)
     ETApp e t -> ETApp (inst ps e) (inst ps t)

     EApp e1 e2 -> EApp (inst ps e1) (inst ps e2)
     EAbs x t e -> EAbs x (inst ps t) (inst ps e)

     EProofAbs p e -> EProofAbs (inst ps p) (inst ps e)
     EProofApp e   -> EProofApp (inst ps e)
     EWhere e dgs  -> EWhere (inst ps e) (inst ps dgs)

instance Inst Match where
  inst ps m =
    case m of
      From x t1 t2 e -> From x (inst ps t1) (inst ps t2) (inst ps e)
      Let d          -> Let (inst ps d)

instance Inst DeclGroup where
  inst ps dg =
    case dg of
      Recursive ds -> Recursive (inst ps ds)
      NonRecursive d -> NonRecursive (inst ps d)

instance Inst Decl where
  inst ps d = d { dDefinition = inst ps (dDefinition d) }

instance Inst DeclDef where
  inst ps d =
    case d of
      DPrim -> DPrim
      DExpr e -> DExpr (inst ps e)

instance Inst Type where
  inst ps ty =
    case ty of
      TUser x ts t
        | needsInst ps x -> TUser x (instTyParams ps ++ ts1) t1
        | otherwise      -> TUser x ts1 t1
        where ts1 = inst ps ts
              t1  = inst ps t

      TCon tc ts ->
        case tc of
          TC (TCNewtype (UserTC x k))
            | needsInst ps x -> TCon (TC (TCNewtype (UserTC x (k1 k))))
                                     (newTs ++ ts1)
          _ -> TCon tc ts1
        where
        ts1 = inst ps ts
        newTs = instTyParams ps
        k1 k = foldr (:->) k (map kindOf newTs)

      TVar _ -> ty

      TRec xs -> TRec [ (f,inst ps t) | (f,t) <- xs ]

instance Inst TySyn where
  inst ps ts = ts { tsConstraints = inst ps (tsConstraints ts)
                  , tsDef = inst ps (tsDef ts)
                  }

instance Inst Newtype where
  inst ps nt = nt { ntConstraints = inst ps (ntConstraints nt)
                  , ntFields = [ (f, inst ps t) | (f,t) <- ntFields nt ]
                  }


