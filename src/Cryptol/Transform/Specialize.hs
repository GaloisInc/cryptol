-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

module Cryptol.Transform.Specialize
where

import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.TypeMap
import Cryptol.TypeCheck.Subst
import qualified Cryptol.ModuleSystem as M
import qualified Cryptol.ModuleSystem.Env as M
import qualified Cryptol.ModuleSystem.Monad as M

import Control.Applicative
import Data.List (intercalate)
import           Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (catMaybes)
import Data.Traversable (traverse)

import MonadLib


-- | A QName should have an entry in the SpecCache iff it is
-- specializable. Each QName starts out with an empty TypesMap.
type SpecCache = Map QName (Decl, TypesMap (QName, Maybe Decl))

type M = M.ModuleT (StateT SpecCache IO)

specialize :: Expr -> M.ModuleCmd Expr
specialize expr modEnv = do
  let extDgs = allDeclGroups modEnv
  run $ specializeEWhere expr extDgs
  where
  run = fmap fst . runStateT Map.empty . M.runModuleT modEnv


specializeExpr :: Expr -> M Expr
specializeExpr expr =
  case expr of
    ECon _econ    -> pure expr
    EList es t    -> EList <$> traverse specializeExpr es <*> pure t
    ETuple es     -> ETuple <$> traverse specializeExpr es
    ERec fs       -> ERec <$> traverse (traverseSnd specializeExpr) fs
    ESel e s      -> ESel <$> specializeExpr e <*> pure s
    EIf e1 e2 e3  -> EIf <$> specializeExpr e1 <*> specializeExpr e2 <*> specializeExpr e3
    EComp t e mss -> EComp t <$> specializeExpr e <*> traverse (traverse specializeMatch) mss
    -- FIXME: this is wrong. Think about scoping rules.
    EVar {}       -> specializeConst expr
    ETAbs t e     -> ETAbs t <$> specializeExpr e
    ETApp {}      -> specializeConst expr
    EApp e1 e2    -> EApp <$> specializeExpr e1 <*> specializeExpr e2
    EAbs qn t e   -> EAbs qn t <$> specializeExpr e
    EProofAbs p e -> EProofAbs p <$> specializeExpr e
    EProofApp {}  -> specializeConst expr
    ECast e t     -> ECast <$> specializeExpr e <*> pure t
    -- TODO: if typeOf e == t, then drop the coercion.
    EWhere e dgs  -> specializeEWhere e dgs

specializeMatch :: Match -> M Match
specializeMatch (From qn t e) = From qn t <$> specializeExpr e
specializeMatch (Let decl)
  | null (sVars (dSignature decl)) = return (Let decl)
  | otherwise = fail "unimplemented: specializeMatch Let unimplemented"
  -- TODO: should treat this case like EWhere.



specializeEWhere :: Expr -> [DeclGroup] -> M Expr
specializeEWhere e dgs = do
  let decls = concatMap groupDecls dgs
  let newCache = Map.fromList [ (dName d, (d, emptyTM)) | d <- decls ]
  -- We assume that the names bound in dgs are disjoint from the other names in scope.
  modifySpecCache (Map.union newCache)
  e' <- specializeExpr e
  -- Then reassemble the DeclGroups.
  let splitDecl :: Decl -> M [Decl]
      splitDecl d = do
        Just (_, tm) <- Map.lookup (dName d) <$> getSpecCache
        return (catMaybes $ map (snd . snd) $ toListTM tm)
  let splitDeclGroup :: DeclGroup -> M [DeclGroup]
      splitDeclGroup (Recursive ds) = do
        ds' <- concat <$> traverse splitDecl ds
        if null ds'
          then return []
          else return [Recursive ds']
      splitDeclGroup (NonRecursive d) = map NonRecursive <$> splitDecl d
  dgs' <- concat <$> traverse splitDeclGroup dgs
  modifySpecCache (flip Map.difference newCache) -- Remove local definitions from cache.
  return $ if null dgs'
    then e'
    else EWhere e' dgs'



specializeConst :: Expr -> M Expr
specializeConst e0 = do
  let (e1, n) = destEProofApps e0
  let (e2, ts) = destETApps e1
  case e2 of
    EVar qname ->
      do cache <- getSpecCache
         case Map.lookup qname cache of
           Nothing -> return e0 -- Primitive/unspecializable variable; leave it alone
           Just (decl, tm) ->
             case lookupTM ts tm of
               Just (qname', _) -> return (EVar qname') -- Already specialized
               Nothing -> do  -- A new type instance of this function
                 qname' <- freshName qname ts -- New type instance, record new name
                 sig' <- instantiateSchema ts n (dSignature decl)
                 modifySpecCache (Map.adjust (fmap (insertTM ts (qname', Nothing))) qname)
                 rhs' <- specializeExpr =<< instantiateExpr ts n (dDefinition decl)
                 let decl' = decl { dName = qname', dSignature = sig', dDefinition = rhs' }
                 modifySpecCache (Map.adjust (fmap (insertTM ts (qname', Just decl'))) qname)
                 return (EVar qname')
    _ -> return e0 -- type/proof application to non-variable; not specializable

destEProofApps :: Expr -> (Expr, Int)
destEProofApps = go 0
  where
    go n (EProofApp e) = go (n + 1) e
    go n e             = (e, n)

destETApps :: Expr -> (Expr, [Type])
destETApps = go []
  where
    go ts (ETApp e t) = go (t : ts) e
    go ts e           = (e, ts)

-- Any top-level declarations in the current module can be found in the 
--  ModuleEnv's LoadedModules, and so we can count of freshName to avoid collisions with them.
-- Additionally, decls in 'where' clauses can only (currently) be parsed with unqualified names.
--  Any generated name for a specialized function will be qualified with the current @ModName@,
--  so genned names will not collide with local decls either.
freshName :: QName -> [Type] -> M QName
freshName (QName m name) tys = do
  let name' = reifyName name tys
  bNames <- matchingBoundNames m
  let loop i = let nm = name' ++ "_" ++ show i
                 in if nm `elem` bNames
                      then loop $ i + 1
                      else nm
  let go = if name' `elem` bNames
               then loop (1 :: Integer)
               else name'
  return $ QName m (Name go)

matchingBoundNames :: (Maybe ModName) -> M [String]
matchingBoundNames m = do
  qns <- allPublicQNames <$> M.getModuleEnv
  return [ n | QName m' (Name n) <- qns , m == m' ]

reifyName :: Name -> [Type] -> String
reifyName name tys = intercalate "_" (showName name : concatMap showT tys)
  where
    tvInt (TVFree i _ _ _) = i
    tvInt (TVBound i _) = i
    showT typ =
      case typ of
        TCon tc ts  -> showTCon tc : concatMap showT ts
        TUser _ _ t -> showT t
        TVar tvar   -> [ "a" ++ show (tvInt tvar) ]
        TRec trec   -> "rec" : concatMap showRecFld trec
    showTCon tcon =
      case tcon of
        TC tc -> showTC tc
        PC pc -> showPC pc
        TF tf -> showTF tf
    showPC pc =
      case pc of
        PEqual   -> "eq"
        PNeq     -> "neq"
        PGeq     -> "geq"
        PFin     -> "fin"
        PHas sel -> "sel_" ++ showSel sel
        PArith   -> "arith"
        PCmp     -> "cmp"
    showTC tc =
      case tc of
        TCNum n     -> show n
        TCInf       -> "inf"
        TCBit       -> "bit"
        TCSeq       -> "seq"
        TCFun       -> "fun"
        TCTuple n   -> "t" ++ show n
        TCNewtype _ -> "user"
    showSel sel = intercalate "_" $
      case sel of
        TupleSel  _ sig -> "tup"  : maybe [] ((:[]) . show) sig
        RecordSel x sig -> "rec"  : showName x : map showName (maybe [] id sig)
        ListSel   _ sig -> "list" : maybe [] ((:[]) . show) sig
    showName nm = 
      case nm of
        Name s       -> s
        NewName _ n -> "x" ++ show n
    showTF tf =
      case tf of
        TCAdd           -> "add"
        TCSub           -> "sub"
        TCMul           -> "mul"
        TCDiv           -> "div"
        TCMod           -> "mod"
        TCLg2           -> "lg2"
        TCExp           -> "exp"
        TCWidth         -> "width"
        TCMin           -> "min"
        TCMax           -> "max"
        TCLenFromThen   -> "len_from_then"
        TCLenFromThenTo -> "len_from_then_to"
    showRecFld (nm,t) = showName nm : showT t



instantiateSchema :: [Type] -> Int -> Schema -> M Schema
instantiateSchema ts n (Forall params props ty)
  | length params /= length ts = fail "instantiateSchema: wrong number of type arguments"
  | length props /= n          = fail "instantiateSchema: wrong number of prop arguments"
  | otherwise                  = return $ Forall [] [] (apSubst sub ty)
  where sub = listSubst [ (tpVar p, t) | (p, t) <- zip params ts ]

-- | Reduce `length ts` outermost type abstractions and `n` proof abstractions.
instantiateExpr :: [Type] -> Int -> Expr -> M Expr
instantiateExpr [] 0 e = return e
instantiateExpr [] n (EProofAbs _ e) = instantiateExpr [] (n - 1) e
instantiateExpr (t : ts) n (ETAbs param e) =
  instantiateExpr ts n (apSubst (singleSubst (tpVar param) t) e)
instantiateExpr _ _ _ = fail "instantiateExpr: wrong number of type/proof arguments"



allDeclGroups :: M.ModuleEnv -> [DeclGroup]
allDeclGroups =
    concatMap mDecls
  . M.loadedModules

allLoadedModules :: M.ModuleEnv -> [M.LoadedModule]
allLoadedModules =
    M.getLoadedModules
  . M.meLoadedModules

allPublicQNames :: M.ModuleEnv -> [QName]
allPublicQNames =
    concatMap
      ( Map.keys
      . M.ifDecls
      . M.ifPublic
      . M.lmInterface
      )
  . allLoadedModules

getSpecCache :: M SpecCache
getSpecCache = lift get

setSpecCache :: SpecCache -> M ()
setSpecCache = lift . set

modifySpecCache :: (SpecCache -> SpecCache) -> M ()
modifySpecCache = lift . modify

modify :: StateM m s => (s -> s) -> m ()
modify f = get >>= (set . f)

traverseSnd :: Functor f => (b -> f c) -> (a, b) -> f (a, c)
traverseSnd f (x, y) = (,) x <$> f y

