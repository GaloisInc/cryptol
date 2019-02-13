-- | Transformed a parametrized module into an ordinary module
-- where everything is parameterized by the module's parameters.
-- Note that this reuses the names from the original parameterized module.
module Cryptol.Transform.AddModParams (addModParams) where

import           Data.Map ( Map )
import qualified Data.Map as Map
import           Data.Set ( Set )
import qualified Data.Set as Set
import           Data.Either(partitionEithers)
import           Data.List(find,sortBy)
import           Data.Ord(comparing)

import Cryptol.TypeCheck.AST
import Cryptol.Parser.Position(thing)
import Cryptol.ModuleSystem.Name(toParamInstName,asParamName,nameIdent
                                ,paramModRecParam)
import Cryptol.Utils.Ident(paramInstModName)

{-
Note that we have to be careful when doing this transformation on
polyomorphic values.  In particular,


Consider type parameters AS, with constraints CS, and value
parameters (xs : TS).

    f : {as} PS => t
    f = f`{as} (<> ..)

    ~~>

    f : {AS ++ as} (CS ++ PS) => { TS } -> t
    f = /\ (AS ++ as) ->
        \\ (CS ++ PS) ->
        \r -> f`{AS ++ as} (<> ...) r

The tricky bit is that we can't just replace `f` with
a new version of `f` with some arguments, instead ew have
to modify the whole instantiation of `f` : f`{as} (<>...)

-}


addModParams :: Module -> Either [Name] Module
addModParams m =
  case getParams m of
    Left errs -> Left errs
    Right ps ->
     let toInst = Set.unions ( Map.keysSet (mTySyns m)
                             : Map.keysSet (mNewtypes m)
                             : map defs (mDecls m)
                             )
         inp = (toInst, ps { pTypeConstraints = inst inp (pTypeConstraints ps) })

     in Right m { mName = paramInstModName (mName m)
                , mTySyns = fixMap inp (mTySyns m)
                , mNewtypes = fixMap inp (mNewtypes m)
                , mDecls = fixUp inp (mDecls m)
                , mParamTypes = Map.empty
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

fixMap :: (AddParams a, Inst a) => Inp -> Map Name a -> Map Name a
fixMap i m =
  Map.fromList [ (toParamInstName x, fixUp i a) | (x,a) <- Map.toList m ]

--------------------------------------------------------------------------------

data Params = Params
  { pTypes            :: [TParam]
  , pTypeConstraints  :: [Prop]
  , pFuns             :: [(Name,Type)]
  }


getParams :: Module -> Either [Name] Params
getParams m
  | null errs =
     let ps = Params { pTypes = map rnTP
                              $ sortBy (comparing mtpNumber)
                              $ Map.elems
                              $ mParamTypes m
                     , pTypeConstraints = map thing (mParamConstraints m)
                     , pFuns = oks
                     }
     in Right ps
  | otherwise = Left errs
  where
  (errs,oks) = partitionEithers (map checkFunP (Map.toList (mParamFuns m)))

  checkFunP (x,s) = case isMono (mvpType s) of
                      Just t  -> Right (asParamName x, t)
                      Nothing -> Left x

  rnTP tp = mtpParam tp { mtpName = asParamName (mtpName tp) }

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
  addParams ps t
    | null (pFuns ps) = t
    | otherwise       = tFun (paramRecTy ps) t


instance AddParams Expr where
  addParams ps e = foldr ETAbs withProps (pTypes ps ++ as)
    where (as,rest1) = splitWhile splitTAbs e
          (bs,rest2) = splitWhile splitProofAbs rest1
          withProps = foldr EProofAbs withArgs (pTypeConstraints ps ++ bs)
          withArgs
            | null (pFuns ps) = rest2
            | otherwise       = EAbs paramModRecParam (paramRecTy ps) rest2



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
                   , dName = toParamInstName (dName d)
                   }

instance AddParams TySyn where
  addParams ps ts = ts { tsParams = pTypes ps ++ tsParams ts
                       , tsConstraints = pTypeConstraints ps ++ tsConstraints ts
                          --  do we need these here ^ ?
                       , tsName = toParamInstName (tsName ts)
                       }

instance AddParams Newtype where
  addParams ps nt = nt { ntParams = pTypes ps ++ ntParams nt
                       , ntConstraints = pTypeConstraints ps ++ ntConstraints nt
                       , ntName = toParamInstName (ntName nt)
                       }



--------------------------------------------------------------------------------





-- | Adjust uses of names to account for the new parameters.
-- Assumes unique names---no capture or shadowing.
class Inst a where
  inst :: Inp -> a -> a

-- | Set of top-level names which need to be instantiate, and module parameters.
type Inp = (Set Name, Params)


paramRecTy :: Params -> Type
paramRecTy ps = tRec [ (nameIdent x, t) | (x,t) <- pFuns ps ]


nameInst :: Inp -> Name -> [Type] -> Int -> Expr
nameInst (_,ps) x ts prfs
  | null (pFuns ps) = withProofs
  | otherwise       = EApp withProofs (EVar paramModRecParam)
  where
  withProofs = iterate EProofApp withTys !!
                                        (length (pTypeConstraints ps) + prfs)

  withTys    = foldl ETApp (EVar (toParamInstName x))
                           (map (TVar . tpVar) (pTypes ps) ++ ts)


-- | Extra parameters to dd when instantiating a type
instTyParams :: Inp -> [Type]
instTyParams (_,ps) = map (TVar . tpVar) (pTypes ps)


needsInst :: Inp -> Name -> Bool
needsInst (xs,_) x = Set.member x xs

isVParam :: Inp -> Name -> Bool
isVParam (_,ps) x = x `elem` map fst (pFuns ps)

isTParam :: Inp -> TVar -> Maybe TParam
isTParam (_,ps) x =
  case x of
    TVBound tp -> find thisName (pTypes ps)
      where thisName y = tpName tp == tpName y
    _ -> Nothing


instance Inst a => Inst [a] where
  inst ps = map (inst ps)

instance Inst Expr where
  inst ps expr =
    case expr of
     EVar x
      | needsInst ps x -> nameInst ps x [] 0
      | isVParam ps x ->
        let sh = map (nameIdent . fst) (pFuns (snd ps))
        in ESel (EVar paramModRecParam) (RecordSel (nameIdent x) (Just sh))
      | otherwise -> EVar x

     EList es t -> EList (inst ps es) (inst ps t)
     ETuple es -> ETuple (inst ps es)
     ERec fs   -> ERec [ (f,inst ps e) | (f,e) <- fs ]
     ESel e s  -> ESel (inst ps e) s
     ESet e s v -> ESet (inst ps e) s (inst ps v)

     EIf e1 e2 e3 -> EIf (inst ps e1) (inst ps e2) (inst ps e3)
     EComp t1 t2 e ms -> EComp (inst ps t1) (inst ps t2)
                               (inst ps e) (inst ps ms)

     ETAbs x e -> ETAbs x (inst ps e)
     ETApp e1 t ->
      case splitExprInst expr of
         (EVar x, ts, prfs) | needsInst ps x -> nameInst ps x ts prfs
         _ -> ETApp (inst ps e1) t

     EApp e1 e2 -> EApp (inst ps e1) (inst ps e2)
     EAbs x t e -> EAbs x (inst ps t) (inst ps e)

     EProofAbs p e -> EProofAbs (inst ps p) (inst ps e)
     EProofApp e1 ->
       case splitExprInst expr of
         (EVar x, ts, prfs) | needsInst ps x -> nameInst ps x ts prfs
         _ -> EProofApp (inst ps e1)

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

      TVar x | Just x' <- isTParam ps x -> TVar (TVBound x')
             | otherwise  -> ty

      TRec xs -> TRec [ (f,inst ps t) | (f,t) <- xs ]

instance Inst TySyn where
  inst ps ts = ts { tsConstraints = inst ps (tsConstraints ts)
                  , tsDef = inst ps (tsDef ts)
                  }

instance Inst Newtype where
  inst ps nt = nt { ntConstraints = inst ps (ntConstraints nt)
                  , ntFields = [ (f, inst ps t) | (f,t) <- ntFields nt ]
                  }


