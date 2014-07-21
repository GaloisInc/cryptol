-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE ScopedTypeVariables #-}
module Cryptol.Symbolic where

import Control.Applicative
import Control.Monad (foldM, liftM2, replicateM, when)
import Control.Monad.Fix (mfix)
import Control.Monad.IO.Class
import Control.Monad.Reader (ask, local)
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Data.Monoid (Monoid(..))
import Data.Traversable (traverse)
import qualified Control.Exception as X

import qualified Data.SBV as SBV
import Data.SBV (SBool)

import qualified Cryptol.ModuleSystem as M
import qualified Cryptol.ModuleSystem.Env as M

import Cryptol.Symbolic.BitVector
import Cryptol.Symbolic.Prims
import Cryptol.Symbolic.Value

import qualified Cryptol.Eval.Value as Eval
import Cryptol.Eval.Value (TValue, isTSeq)
import qualified Cryptol.Eval.Type (evalType)
import qualified Cryptol.Eval.Env (EvalEnv(..))
import Cryptol.TypeCheck.AST
import Cryptol.Utils.PP
import Cryptol.Utils.Panic(panic)

-- External interface ----------------------------------------------------------

lookupProver :: String -> SBV.SMTConfig
lookupProver "cvc4"  = SBV.cvc4
lookupProver "yices" = SBV.yices
lookupProver "z3"    = SBV.z3
lookupProver s       = error $ "invalid prover: " ++ s

prove :: (String, Bool, Bool) -> (Expr, Schema) -> M.ModuleCmd (Either String (Maybe [Eval.Value]))
prove (proverName, useSolverIte, verbose) (expr, schema) = protectStack useSolverIte $ \modEnv -> do
  let extDgs = allDeclGroups modEnv
  let prover = lookupProver proverName
  case predArgTypes schema of
    Left msg -> return (Right (Left msg, modEnv), [])
    Right ts -> do when verbose $ putStrLn "Simulating..."
                   let runE = do args <- mapM forallFinType ts
                                 env <- evalDecls emptyEnv extDgs
                                 v <- evalExpr env expr
                                 b <- foldM vApply v args
                                 return (fromVBit b)
                   let simenv = SimEnv
                        { simConfig = prover
                        , simPath = SBV.true
                        , simIteSolver = useSolverIte
                        , simVerbose = verbose
                        }
                   result <- SBV.proveWith prover $ do
                               b <- runTheMonad runE simenv
                               when verbose $ liftIO $ putStrLn $ "Calling " ++ proverName ++ "..."
                               return b
                   let solution = case result of
                         SBV.ThmResult (SBV.Satisfiable {}) -> Right (Just vs)
                           where Right (_, cws) = SBV.getModel result
                                 (vs, _) = parseValues ts cws
                         SBV.ThmResult (SBV.Unsatisfiable {}) -> Right Nothing
                         SBV.ThmResult _ -> Left (show result)
                   return (Right (solution, modEnv), [])

sat :: (String, Bool, Bool) -> (Expr, Schema) -> M.ModuleCmd (Either String (Maybe [Eval.Value]))
sat (proverName, useSolverIte, verbose) (expr, schema) = protectStack useSolverIte $ \modEnv -> do
  let extDgs = allDeclGroups modEnv
  let prover = lookupProver proverName
  case predArgTypes schema of
    Left msg -> return (Right (Left msg, modEnv), [])
    Right ts -> do when verbose $ putStrLn "Simulating..."
                   let runE = do args <- mapM existsFinType ts
                                 env <- evalDecls emptyEnv extDgs
                                 v <- evalExpr env expr
                                 b <- foldM vApply v args
                                 return (fromVBit b)
                   let simenv = SimEnv
                        { simConfig = prover
                        , simPath = SBV.true
                        , simIteSolver = useSolverIte
                        , simVerbose = verbose
                        }
                   result <- SBV.satWith prover $ do
                               b <- runTheMonad runE simenv
                               when verbose $ liftIO $ putStrLn $ "Calling " ++ proverName ++ "..."
                               return b
                   let solution = case result of
                         SBV.SatResult (SBV.Satisfiable {}) -> Right (Just vs)
                           where Right (_, cws) = SBV.getModel result
                                 (vs, _) = parseValues ts cws
                         SBV.SatResult (SBV.Unsatisfiable {}) -> Right Nothing
                         SBV.SatResult _ -> Left (show result)
                   return (Right (solution, modEnv), [])

protectStack :: Bool -> M.ModuleCmd (Either String a) -> M.ModuleCmd (Either String a)
protectStack usingITE cmd modEnv = X.catchJust isOverflow (cmd modEnv) handler
  where isOverflow X.StackOverflow = Just ()
        isOverflow _               = Nothing
        msg | usingITE  = msgBase
            | otherwise = msgBase ++ "\n" ++
                          "Using ':set iteSolver=on' might help."
        msgBase = "Symbolic evaluation failed to terminate."
        handler () = return (Right (Left msg, modEnv), [])

parseValues :: [FinType] -> [SBV.CW] -> ([Eval.Value], [SBV.CW])
parseValues [] cws = ([], cws)
parseValues (t : ts) cws = (v : vs, cws'')
  where (v, cws') = parseValue t cws
        (vs, cws'') = parseValues ts cws'

parseValue :: FinType -> [SBV.CW] -> (Eval.Value, [SBV.CW])
parseValue FTBit [] = error "parseValue"
parseValue FTBit (cw : cws) = (Eval.VBit (SBV.fromCW cw), cws)
parseValue (FTSeq 0 FTBit) cws = (Eval.VWord 0 0, cws)
parseValue (FTSeq n FTBit) (cw : cws)
  | SBV.isBounded cw = (Eval.VWord (toInteger n) (SBV.fromCW cw), cws)
  | otherwise = error "parseValue"
parseValue (FTSeq n FTBit) cws = (Eval.VSeq True vs, cws')
  where (vs, cws') = parseValues (replicate n FTBit) cws
parseValue (FTSeq n t) cws = (Eval.VSeq False vs, cws')
  where (vs, cws') = parseValues (replicate n t) cws
parseValue (FTTuple ts) cws = (Eval.VTuple (length vs) vs, cws')
  where (vs, cws') = parseValues ts cws
parseValue (FTRecord fs) cws = (Eval.VRecord (zip ns vs), cws')
  where (ns, ts) = unzip fs
        (vs, cws') = parseValues ts cws

allDeclGroups :: M.ModuleEnv -> [DeclGroup]
allDeclGroups = concatMap mDecls . M.loadedModules

data FinType
    = FTBit
    | FTSeq Int FinType
    | FTTuple [FinType]
    | FTRecord [(Name, FinType)]

numType :: Type -> Maybe Int
numType (TCon (TC (TCNum n)) [])
  | 0 <= n && n <= toInteger (maxBound :: Int) = Just (fromInteger n)
numType (TUser _ _ t) = numType t
numType _ = Nothing

finType :: Type -> Maybe FinType
finType ty =
  case ty of
    TCon (TC TCBit) []       -> Just FTBit
    TCon (TC TCSeq) [n, t]   -> FTSeq <$> numType n <*> finType t
    TCon (TC (TCTuple _)) ts -> FTTuple <$> traverse finType ts
    TRec fields              -> FTRecord <$> traverse (traverseSnd finType) fields
    TUser _ _ t              -> finType t
    _                        -> Nothing

predArgTypes :: Schema -> Either String [FinType]
predArgTypes schema@(Forall ts ps ty)
  | null ts && null ps =
      case go ty of
        Just fts -> Right fts
        Nothing  -> Left $ "Not a valid predicate type:\n" ++ show (pp schema)
  | otherwise = Left $ "Not a monomorphic type:\n" ++ show (pp schema)
  where
    go (TCon (TC TCBit) []) = Just []
    go (TCon (TC TCFun) [ty1, ty2]) = (:) <$> finType ty1 <*> go ty2
    go (TUser _ _ t) = go t
    go _ = Nothing

forallFinType :: FinType -> TheMonad Value
forallFinType ty =
  case ty of
    FTBit         -> VBit <$> liftSymbolic SBV.forall_
    FTSeq 0 FTBit -> return $ VWord (SBV.literal (bv 0 0))
    FTSeq n FTBit -> VWord <$> liftSymbolic (forallBV_ n)
    FTSeq n t     -> vSeq <$> replicateM n (mkThunk t)
    FTTuple ts    -> VTuple <$> mapM mkThunk ts
    FTRecord fs   -> VRecord <$> mapM (traverseSnd mkThunk) fs
  where
    mkThunk :: FinType -> TheMonad Thunk
    mkThunk t = Ready <$> forallFinType t

existsFinType :: FinType -> TheMonad Value
existsFinType ty =
  case ty of
    FTBit         -> VBit <$> liftSymbolic SBV.exists_
    FTSeq 0 FTBit -> return $ VWord (SBV.literal (bv 0 0))
    FTSeq n FTBit -> VWord <$> liftSymbolic (existsBV_ n)
    FTSeq n t     -> vSeq <$> replicateM n (mkThunk t)
    FTTuple ts    -> VTuple <$> mapM mkThunk ts
    FTRecord fs   -> VRecord <$> mapM (traverseSnd mkThunk) fs
  where
    mkThunk :: FinType -> TheMonad Thunk
    mkThunk t = Ready <$> existsFinType t

-- Simulation environment ------------------------------------------------------

data Env = Env
  { envVars :: Map.Map QName Thunk
  , envTypes :: Map.Map TVar TValue
  }

instance Monoid Env where
  mempty = Env
    { envVars  = Map.empty
    , envTypes = Map.empty
    }

  mappend l r = Env
    { envVars  = Map.union (envVars  l) (envVars  r)
    , envTypes = Map.union (envTypes l) (envTypes r)
    }

emptyEnv :: Env
emptyEnv = Env Map.empty Map.empty

-- | Bind a variable in the evaluation environment.
bindVar :: (QName, Thunk) -> Env -> Env
bindVar (n, thunk) env = env { envVars = Map.insert n thunk (envVars env) }

-- | Lookup a variable in the environment.
lookupVar :: QName -> Env -> Maybe Thunk
lookupVar n env = Map.lookup n (envVars env)

-- | Bind a type variable of kind *.
bindType :: TVar -> TValue -> Env -> Env
bindType p ty env = env { envTypes = Map.insert p ty (envTypes env) }

-- | Lookup a type variable.
lookupType :: TVar -> Env -> Maybe TValue
lookupType p env = Map.lookup p (envTypes env)

-- Path conditions -------------------------------------------------------------

thenBranch :: SBool -> TheMonad a -> TheMonad a
thenBranch s = local $ \e -> e { simPath = (SBV.&&&) s (simPath e) }

elseBranch :: SBool -> TheMonad a -> TheMonad a
elseBranch s = thenBranch (SBV.bnot s)

isFeasible :: SBool -> TheMonad Bool
isFeasible path
  | path `SBV.isConcretely` (== False) = return False
  | path `SBV.isConcretely` (== True)  = return True
  | otherwise = do
    useSolverIte <- simIteSolver <$> ask
    verbose <- simVerbose <$> ask
    config <- simConfig <$> ask
    if useSolverIte then do
                   when verbose $ liftIO $ putStrLn "Testing branch condition with solver..."
                   res <- liftSymbolic $ SBV.internalIsTheoremWith config (Just 5) (SBV.bnot path)
                   case res of
                     Just isThm -> do let msg = if isThm then "Infeasible." else "Feasible."
                                      when verbose $ liftIO $ putStrLn msg
                                      return (not isThm)
                     Nothing    -> do when verbose $ liftIO $ putStrLn "Undetermined."
                                      return True
      else return True

evalIf :: SBool -> TheMonad Value -> TheMonad Value -> TheMonad Value
evalIf s m1 m2 = do
  path <- simPath <$> ask
  let path1 = (SBV.&&&) path s
  let path2 = (SBV.&&&) path (SBV.bnot s)
  c1 <- isFeasible path1
  if not c1
    then elseBranch s m2
    else do
      c2 <- isFeasible path2
      if not c2
        then thenBranch s m1
        else do
          v1 <- thenBranch s m1
          v2 <- elseBranch s m2
          ite s v1 v2

-- Expressions -----------------------------------------------------------------

evalExpr :: Env -> Expr -> TheMonad Value
evalExpr env expr =
  case expr of
    ECon econ         -> return $ evalECon econ
    EList es _ty      -> vSeq <$> traverse eval' es
    ETuple es         -> VTuple <$> traverse eval' es
    ERec fields       -> VRecord <$> traverse (traverseSnd eval') fields
    ESel e sel        -> evalSel sel =<< eval e
    EIf b e1 e2 -> do
      VBit s <- evalExpr env b
      evalIf s (evalExpr env e1) (evalExpr env e2)

    EComp ty e mss    -> evalComp env (evalType env ty) e mss
    EVar n            -> force $ fromJust (lookupVar n env)
    -- TODO: how to deal with uninterpreted functions?
    ETAbs tv e        -> return $ VPoly $ \ty -> evalExpr (bindType (tpVar tv) ty env) e
    ETApp e ty        -> do VPoly f <- eval e
                            f (evalType env ty)
    EApp e1 e2        -> do VFun f <- eval e1
                            f =<< eval' e2
    EAbs n _ty e      -> return $ VFun $ \th -> evalExpr (bindVar (n, th) env) e
    EProofAbs _prop e -> eval e
    EProofApp e       -> eval e
    ECast e _ty       -> eval e
    EWhere e ds       -> do env' <- evalDecls env ds
                            evalExpr env' e
    where
      eval e = evalExpr env e
      eval' e = delay (evalExpr env e)

evalType :: Env -> Type -> TValue
evalType env ty = Cryptol.Eval.Type.evalType env' ty
  where env' = Cryptol.Eval.Env.EvalEnv Map.empty (envTypes env)


evalSel :: Selector -> Value -> TheMonad Value
evalSel sel v =
  case sel of
    TupleSel n _  ->
      case v of
        VTuple xs -> force $ xs !! (n - 1) -- 1-based indexing
        VNil      -> return VNil
        VCons {}  -> liftList v
        VFun f    -> return $ VFun $ \x -> evalSel sel =<< f x

    RecordSel n _ ->
      case v of
        VRecord bs  -> force $ fromJust (lookup n bs)
        VNil        -> return VNil
        VCons {}    -> liftList v
        VFun f      -> return $ VFun $ \x -> evalSel sel =<< f x

    ListSel n _   -> case v of
                       --VSeq xs -> force $ xs !! n  -- 0-based indexing
                       VWord s -> return $ VBit (SBV.sbvTestBit s n)
                       _       -> let go :: Int -> Value -> TheMonad Thunk
                                      go 0 (VCons x _) = return x
                                      go i (VCons _ y) = go (i - 1) =<< force y
                                      go _ _ = error "internal error"
                                  in force =<< go n v

  where
  liftList VNil         = return VNil
  liftList (VCons x xs) = do x'  <- delay (evalSel sel =<< force x)
                             xs' <- delay (liftList    =<< force xs)
                             return (VCons x' xs')
  liftList _            = panic "Cryptol.Symbolic.evalSel"
                                  ["Malformed list, while lifting selector"]

-- Declarations ----------------------------------------------------------------

evalDecls :: Env -> [DeclGroup] -> TheMonad Env
evalDecls = foldM evalDeclGroup

evalDeclGroup :: Env -> DeclGroup -> TheMonad Env
evalDeclGroup env dg =
  case dg of
    NonRecursive d -> do binding <- evalDecl env d
                         return $ bindVar binding env
    Recursive ds   -> mfix $ \env' -> do
                        bindings <- traverse (evalDecl env') ds
                        return $ foldr bindVar env bindings

evalDecl :: Env -> Decl -> TheMonad (QName, Thunk)
evalDecl env d = do
  thunk <- delay $ evalExpr env (dDefinition d)
  return (dName d, thunk)

-- List Comprehensions ---------------------------------------------------------

data LazySeq a = LSNil | LSCons a (MLazySeq a)
type MLazySeq a = TheMonad (LazySeq a)

instance Functor LazySeq where
  fmap _ LSNil = LSNil
  fmap f (LSCons x xs) = LSCons (f x) (fmap f <$> xs)

singleLS :: a -> LazySeq a
singleLS x = LSCons x (return LSNil)

zipWithLS :: (a -> b -> c) -> LazySeq a -> LazySeq b -> LazySeq c
zipWithLS f (LSCons x xs) (LSCons y ys) = LSCons (f x y) (liftM2 (zipWithLS f) xs ys)
zipWithLS _ _ _ = LSNil

repeatLS :: a -> LazySeq a
repeatLS x = xs where xs = LSCons x (return xs)

transposeLS :: [LazySeq a] -> LazySeq [a]
transposeLS = foldr (zipWithLS (:)) (repeatLS [])

appendLS :: LazySeq a -> LazySeq a -> LazySeq a
appendLS LSNil ys = ys
appendLS (LSCons x xs') ys =
  LSCons x $ do
    xs <- xs'
    return (appendLS xs ys)

appendMLS :: MLazySeq a -> MLazySeq a -> MLazySeq a
appendMLS xs ys = do
  l <- xs
  case l of
    LSNil -> ys
    LSCons x xs' -> return (LSCons x (appendMLS xs' ys))

bindMLS :: MLazySeq a -> (a -> MLazySeq b) -> MLazySeq b
bindMLS xs k = do
  l <- xs
  case l of
    LSNil -> return LSNil
    LSCons x xs' -> appendMLS (k x) (bindMLS xs' k)

toLazySeq :: Value -> LazySeq Thunk
toLazySeq (VCons th1 th2) = LSCons th1 (toLazySeq <$> force th2)
toLazySeq VNil = LSNil
toLazySeq (VWord w) = go (SBV.bitSize w - 1)
  where go i | i < 0     = LSNil
             | otherwise = LSCons (Ready (VBit (SBV.sbvTestBit w i))) (return (go (i - 1)))
toLazySeq _ = error "toLazySeq"

toSeq :: LazySeq Thunk -> TheMonad Value
toSeq LSNil = return VNil
toSeq (LSCons x xs) = VCons x <$> delay (toSeq =<< xs)

evalComp :: Env -> TValue -> Expr -> [[Match]] -> TheMonad Value
evalComp env seqty body ms =
  case isTSeq seqty of
    Nothing -> evalPanic "Cryptol.Eval" [ "evalComp given a non sequence", show seqty ]
    Just (_len, _el) -> do
      -- generate a new environment for each iteration of each parallel branch
      (benvs :: [LazySeq Env]) <- mapM (branchEnvs env) ms
      -- take parallel slices of each environment.
      let slices :: LazySeq [Env]
          slices = transposeLS benvs

      -- join environments to produce environments at each step through the process.
      let envs :: LazySeq Env
          envs = fmap mconcat slices

      thunks <- bindMLS (return envs) (\e -> singleLS <$> delay (evalExpr e body))
      toSeq thunks

-- | Turn a list of matches into the final environments for each iteration of
-- the branch.
branchEnvs :: Env -> [Match] -> MLazySeq Env
branchEnvs env matches =
  case matches of
    []     -> return (singleLS env)
    m : ms -> bindMLS (evalMatch env m) (\env' -> branchEnvs env' ms)

-- | Turn a match into the list of environments it represents.
evalMatch :: Env -> Match -> MLazySeq Env
evalMatch env m = case m of

  From n _ty expr -> do
    ths <- toLazySeq <$> evalExpr env expr
    return $ fmap (\th -> bindVar (n, th) env) ths

  Let d -> do
    binding <- evalDecl env d
    return $ singleLS (bindVar binding env)
