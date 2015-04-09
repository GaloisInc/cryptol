-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
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

import Data.List (intercalate)
import           Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (catMaybes)

import MonadLib

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
import Data.Traversable (traverse)
#endif

-- Specializer Monad -----------------------------------------------------------

-- | A QName should have an entry in the SpecCache iff it is
-- specializable. Each QName starts out with an empty TypesMap.
type SpecCache = Map QName (Decl, TypesMap (QName, Maybe Decl))

-- | The specializer monad.
type SpecT m a = StateT SpecCache (M.ModuleT m) a

type SpecM a = SpecT IO a

runSpecT :: SpecCache -> SpecT m a -> M.ModuleT m (a, SpecCache)
runSpecT s m = runStateT s m

liftSpecT :: Monad m => M.ModuleT m a -> SpecT m a
liftSpecT m = lift m

getSpecCache :: Monad m => SpecT m SpecCache
getSpecCache = get

setSpecCache :: Monad m => SpecCache -> SpecT m ()
setSpecCache = set

modifySpecCache :: Monad m => (SpecCache -> SpecCache) -> SpecT m ()
modifySpecCache = modify

modify :: StateM m s => (s -> s) -> m ()
modify f = get >>= (set . f)


-- Specializer -----------------------------------------------------------------

-- | Add a `where` clause to the given expression containing
-- type-specialized versions of all functions called (transitively) by
-- the body of the expression.
specialize :: Expr -> M.ModuleCmd Expr
specialize expr modEnv = run $ do
  let extDgs = allDeclGroups modEnv
  let (tparams, expr') = destETAbs expr
  spec' <- specializeEWhere expr' extDgs
  return (foldr ETAbs spec' tparams)
  where
  run = M.runModuleT modEnv . fmap fst . runSpecT Map.empty

specializeExpr :: Expr -> SpecM Expr
specializeExpr expr =
  case expr of
    ECon _econ    -> pure expr
    EList es t    -> EList <$> traverse specializeExpr es <*> pure t
    ETuple es     -> ETuple <$> traverse specializeExpr es
    ERec fs       -> ERec <$> traverse (traverseSnd specializeExpr) fs
    ESel e s      -> ESel <$> specializeExpr e <*> pure s
    EIf e1 e2 e3  -> EIf <$> specializeExpr e1 <*> specializeExpr e2 <*> specializeExpr e3
    EComp t e mss -> EComp t <$> specializeExpr e <*> traverse (traverse specializeMatch) mss
    -- Bindings within list comprehensions always have monomorphic types.
    EVar {}       -> specializeConst expr
    ETAbs t e     -> do
      cache <- getSpecCache
      setSpecCache Map.empty
      e' <- specializeExpr e
      setSpecCache cache
      return (ETAbs t e')
    -- We need to make sure that after processing `e`, no specialized
    -- decls mentioning type variable `t` escape outside the
    -- `ETAbs`. To avoid this, we reset to an empty SpecCache while we
    -- run `specializeExpr e`, and restore it afterward: this
    -- effectively prevents the specializer from registering any type
    -- instantiations involving `t` for any decls bound outside the
    -- scope of `t`.
    ETApp {}      -> specializeConst expr
    EApp e1 e2    -> EApp <$> specializeExpr e1 <*> specializeExpr e2
    EAbs qn t e   -> EAbs qn t <$> specializeExpr e
    EProofAbs p e -> EProofAbs p <$> specializeExpr e
    EProofApp {}  -> specializeConst expr
    ECast e t     -> ECast <$> specializeExpr e <*> pure t
    -- TODO: if typeOf e == t, then drop the coercion.
    EWhere e dgs  -> specializeEWhere e dgs

specializeMatch :: Match -> SpecM Match
specializeMatch (From qn t e) = From qn t <$> specializeExpr e
specializeMatch (Let decl)
  | null (sVars (dSignature decl)) = return (Let decl)
  | otherwise = fail "unimplemented: specializeMatch Let unimplemented"
  -- TODO: should treat this case like EWhere.


-- | Add the declarations to the SpecCache, run the given monadic
-- action, and then pull the specialized declarations back out of the
-- SpecCache state. Return the result along with the declarations and
-- a table of names of specialized bindings.
withDeclGroups :: [DeclGroup] -> SpecM a
                  -> SpecM (a, [DeclGroup], Map QName (TypesMap QName))
withDeclGroups dgs action = do
  let decls = concatMap groupDecls dgs
  let newCache = Map.fromList [ (dName d, (d, emptyTM)) | d <- decls ]
  -- We assume that the names bound in dgs are disjoint from the other names in scope.
  modifySpecCache (Map.union newCache)
  result <- action
  -- Then reassemble the DeclGroups.
  let splitDecl :: Decl -> SpecM [Decl]
      splitDecl d = do
        Just (_, tm) <- Map.lookup (dName d) <$> getSpecCache
        return (catMaybes $ map (snd . snd) $ toListTM tm)
  let splitDeclGroup :: DeclGroup -> SpecM [DeclGroup]
      splitDeclGroup (Recursive ds) = do
        ds' <- concat <$> traverse splitDecl ds
        if null ds'
          then return []
          else return [Recursive ds']
      splitDeclGroup (NonRecursive d) = map NonRecursive <$> splitDecl d
  dgs' <- concat <$> traverse splitDeclGroup dgs
  -- Get updated map of only the local entries we added.
  newCache' <- flip Map.intersection newCache <$> getSpecCache
  let nameTable = fmap (fmap fst . snd) newCache'
  -- Remove local definitions from the cache.
  modifySpecCache (flip Map.difference newCache)
  return (result, dgs', nameTable)

-- | Compute the specialization of `EWhere e dgs`. A decl within `dgs`
-- is replicated once for each monomorphic type instance at which it
-- is used; decls not mentioned in `e` (even monomorphic ones) are
-- simply dropped.
specializeEWhere :: Expr -> [DeclGroup] -> SpecM Expr
specializeEWhere e dgs = do
  (e', dgs', _) <- withDeclGroups dgs (specializeExpr e)
  return $ if null dgs'
    then e'
    else EWhere e' dgs'

-- | Transform the given declaration groups into a set of monomorphic
-- declarations. All of the original declarations with monomorphic
-- types are kept; additionally the result set includes instantiated
-- versions of polymorphic decls that are referenced by the
-- monomorphic bindings. We also return a map relating generated names
-- to the names from the original declarations.
specializeDeclGroups :: [DeclGroup] -> SpecM ([DeclGroup], Map QName (TypesMap QName))
specializeDeclGroups dgs = do
  let decls = concatMap groupDecls dgs
  let isMono s = null (sVars s) && null (sProps s)
  let monos = [ EVar (dName d) | d <- decls, isMono (dSignature d) ]
  (_, dgs', names) <- withDeclGroups dgs $ mapM specializeExpr monos
  return (dgs', names)

specializeConst :: Expr -> SpecM Expr
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


-- Utility Functions -----------------------------------------------------------

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

destEProofAbs :: Expr -> ([Prop], Expr)
destEProofAbs = go []
  where
    go ps (EProofAbs p e) = go (p : ps) e
    go ps e               = (ps, e)

destETAbs :: Expr -> ([TParam], Expr)
destETAbs = go []
  where
    go ts (ETAbs t e) = go (t : ts) e
    go ts e           = (ts, e)

-- Any top-level declarations in the current module can be found in the 
--  ModuleEnv's LoadedModules, and so we can count of freshName to avoid collisions with them.
-- Additionally, decls in 'where' clauses can only (currently) be parsed with unqualified names.
--  Any generated name for a specialized function will be qualified with the current @ModName@,
--  so genned names will not collide with local decls either.
freshName :: QName -> [Type] -> SpecM QName
freshName qn [] = return qn
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

matchingBoundNames :: (Maybe ModName) -> SpecM [String]
matchingBoundNames m = do
  qns <- allPublicQNames <$> liftSpecT M.getModuleEnv
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
        TVar tv     -> [ "a" ++ show (tvInt tv) ]
        TRec tr     -> "rec" : concatMap showRecFld tr
    showTCon tCon =
      case tCon of
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



instantiateSchema :: [Type] -> Int -> Schema -> SpecM Schema
instantiateSchema ts n (Forall params props ty)
  | length params /= length ts = fail "instantiateSchema: wrong number of type arguments"
  | length props /= n          = fail "instantiateSchema: wrong number of prop arguments"
  | otherwise                  = return $ Forall [] [] (apSubst sub ty)
  where sub = listSubst [ (tpVar p, t) | (p, t) <- zip params ts ]

-- | Reduce `length ts` outermost type abstractions and `n` proof abstractions.
instantiateExpr :: [Type] -> Int -> Expr -> SpecM Expr
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

traverseSnd :: Functor f => (b -> f c) -> (a, b) -> f (a, c)
traverseSnd f (x, y) = (,) x <$> f y
