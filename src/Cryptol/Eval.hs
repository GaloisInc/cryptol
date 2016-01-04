-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe #-}
{-# LANGUAGE PatternGuards #-}

module Cryptol.Eval (
    moduleEnv
  , EvalEnv()
  , emptyEnv
  , evalExpr
  , evalDecls
  , EvalError(..)
  , WithBase(..)
  ) where

import Cryptol.Eval.Error
import Cryptol.Eval.Env
import Cryptol.Eval.Type
import Cryptol.Eval.Value
import Cryptol.ModuleSystem.Name
import Cryptol.TypeCheck.AST
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.PP
import Cryptol.Prims.Eval

import qualified Data.Map as Map

import Prelude ()
import Prelude.Compat

-- Expression Evaluation -------------------------------------------------------

moduleEnv :: Module -> EvalEnv -> EvalEnv
moduleEnv m env = evalDecls (mDecls m) (evalNewtypes (mNewtypes m) env)

evalExpr :: EvalEnv -> Expr -> Value
evalExpr env expr = case expr of

  EList es ty -> VSeq (isTBit (evalType env ty)) (map (evalExpr env) es)

  ETuple es -> VTuple (map eval es)

  ERec fields -> VRecord [ (f,eval e) | (f,e) <- fields ]

  ESel e sel -> evalSel env e sel

  EIf c t f | fromVBit (eval c) -> eval t
            | otherwise         -> eval f

  EComp l h gs -> evalComp env (evalType env l) h gs

  EVar n -> case lookupVar n env of
    Just val -> val
    Nothing  -> panic "[Eval] evalExpr"
                     ["var `" ++ show (pp n) ++ "` is not defined"
                     , pretty (WithBase defaultPPOpts env)
                     ]

  ETAbs tv b -> VPoly $ \ty -> evalExpr (bindType (tpVar tv) ty env) b

  ETApp e ty -> case eval e of
    VPoly f -> f (evalType env ty)
    val     -> panic "[Eval] evalExpr"
                    ["expected a polymorphic value"
                    , show (ppV val), show e, show ty
                    ]

  EApp f x -> case eval f of
    VFun f' -> f' (eval x)
    it       -> panic "[Eval] evalExpr" ["not a function", show (ppV it) ]

  EAbs n _ty b -> VFun (\ val -> evalExpr (bindVar n val env) b )

  -- XXX these will likely change once there is an evidence value
  EProofAbs _ e -> evalExpr env e
  EProofApp e   -> evalExpr env e

  ECast e _ty -> evalExpr env e

  EWhere e ds -> evalExpr (evalDecls ds env) e

  where

  eval = evalExpr env

  ppV = ppValue defaultPPOpts


-- Newtypes --------------------------------------------------------------------

evalNewtypes :: Map.Map Name Newtype -> EvalEnv -> EvalEnv
evalNewtypes nts env = Map.foldl (flip evalNewtype) env nts

-- | Introduce the constructor function for a newtype.
evalNewtype :: Newtype -> EvalEnv -> EvalEnv
evalNewtype nt = bindVar (ntName nt) (foldr tabs con (ntParams nt))
  where
  tabs _tp body = tlam (\ _ -> body)
  con           = VFun id


-- Declarations ----------------------------------------------------------------

evalDecls :: [DeclGroup] -> EvalEnv -> EvalEnv
evalDecls dgs env = foldl (flip evalDeclGroup) env dgs

evalDeclGroup :: DeclGroup -> EvalEnv -> EvalEnv
evalDeclGroup dg env = env'
  where
  -- the final environment is passed in for each declaration, to permit
  -- recursive values.
  env' = case dg of
    Recursive ds   -> foldr (evalDecl env') env ds
    NonRecursive d -> evalDecl env d env

evalDecl :: ReadEnv -> Decl -> EvalEnv -> EvalEnv
evalDecl renv d =
  bindVar (dName d) $
    case dDefinition d of
      DPrim   -> evalPrim d
      DExpr e -> evalExpr renv e


-- Selectors -------------------------------------------------------------------

evalSel :: ReadEnv -> Expr -> Selector -> Value
evalSel env e sel = case sel of

  TupleSel n _  -> tupleSel n val
  RecordSel n _ -> recordSel n val
  ListSel ix _  -> fromSeq val !! ix

  where

  val = evalExpr env e

  tupleSel n v =
    case v of
      VTuple vs     -> vs !! n
      VSeq False vs -> VSeq False [ tupleSel n v1 | v1 <- vs ]
      VStream vs    -> VStream [ tupleSel n v1 | v1 <- vs ]
      VFun f        -> VFun (\x -> tupleSel n (f x))
      _             -> evalPanic "Cryptol.Eval.evalSel"
                          [ "Unexpected value in tuple selection"
                          , show (ppValue defaultPPOpts v) ]

  recordSel n v =
    case v of
      VRecord {}    -> lookupRecord n v
      VSeq False vs -> VSeq False [ recordSel n v1 | v1 <- vs ]
      VStream vs    -> VStream [recordSel n v1 | v1 <- vs ]
      VFun f        -> VFun (\x -> recordSel n (f x))
      _             -> evalPanic "Cryptol.Eval.evalSel"
                          [ "Unexpected value in record selection"
                          , show (ppValue defaultPPOpts v) ]





-- List Comprehension Environments ---------------------------------------------

-- | A variation of the ZipList type from Control.Applicative, with a
-- separate constructor for pure values. This datatype is used to
-- represent the list of values that each variable takes on within a
-- list comprehension. The @Zip@ constructor is for bindings that take
-- different values at different positions in the list, while the
-- @Pure@ constructor is for bindings originating outside the list
-- comprehension, which have the same value for all list positions.
data ZList a = Pure a | Zip [a]

getZList :: ZList a -> [a]
getZList (Pure x) = repeat x
getZList (Zip xs) = xs

instance Functor ZList where
  fmap f (Pure x) = Pure (f x)
  fmap f (Zip xs) = Zip (map f xs)

instance Applicative ZList where
  pure x = Pure x
  Pure f <*> Pure x = Pure (f x)
  Pure f <*> Zip xs = Zip (map f xs)
  Zip fs <*> Pure x = Zip (map ($ x) fs)
  Zip fs <*> Zip xs = Zip (zipWith ($) fs xs)

-- | Evaluation environments for list comprehensions: Each variable
-- name is bound to a list of values, one for each element in the list
-- comprehension.
data ListEnv = ListEnv
  { leVars :: Map.Map Name (ZList Value)
  , leTypes :: Map.Map TVar TValue
  }

instance Monoid ListEnv where
  mempty = ListEnv
    { leVars  = Map.empty
    , leTypes = Map.empty
    }

  mappend l r = ListEnv
    { leVars  = Map.union (leVars  l) (leVars  r)
    , leTypes = Map.union (leTypes l) (leTypes r)
    }

toListEnv :: EvalEnv -> ListEnv
toListEnv e =
  ListEnv
  { leVars = fmap Pure (envVars e)
  , leTypes = envTypes e
  }

-- | Take parallel slices of the list environment. If some names are
-- bound to longer lists of values (e.g. if they come from a different
-- parallel branch of a comprehension) then the last elements will be
-- dropped as the lists are zipped together.
zipListEnv :: ListEnv -> [EvalEnv]
zipListEnv (ListEnv vm tm) =
  [ EvalEnv { envVars = v, envTypes = tm }
  | v <- getZList (sequenceA vm) ]

bindVarList :: Name -> [Value] -> ListEnv -> ListEnv
bindVarList n vs lenv = lenv { leVars = Map.insert n (Zip vs) (leVars lenv) }


-- List Comprehensions ---------------------------------------------------------

-- | Evaluate a comprehension.
evalComp :: ReadEnv -> TValue -> Expr -> [[Match]] -> Value
evalComp env seqty body ms
  | Just (len,el) <- isTSeq seqty = toSeq len el [ evalExpr e body | e <- envs ]
  | otherwise = evalPanic "Cryptol.Eval" [ "evalComp given a non sequence"
                                         , show seqty
                                         ]

  -- XXX we could potentially print this as a number if the type was available.
  where
  -- generate a new environment for each iteration of each parallel branch
  benvs :: [ListEnv]
  benvs = map (branchEnvs (toListEnv env)) ms

  -- join environments to produce environments at each step through the process.
  envs :: [EvalEnv]
  envs = zipListEnv (mconcat benvs)

-- | Turn a list of matches into the final environments for each iteration of
-- the branch.
branchEnvs :: ListEnv -> [Match] -> ListEnv
branchEnvs env matches = foldl evalMatch env matches

-- | Turn a match into the list of environments it represents.
evalMatch :: ListEnv -> Match -> ListEnv
evalMatch lenv m = case m of

  -- many envs
  From n _ty expr -> bindVarList n (concat vss) lenv'
    where
      vss = [ fromSeq (evalExpr env expr) | env <- zipListEnv lenv ]
      stutter (Pure x) = Pure x
      stutter (Zip xs) = Zip [ x | (x, vs) <- zip xs vss, _ <- vs ]
      lenv' = lenv { leVars = fmap stutter (leVars lenv) }

  -- XXX we don't currently evaluate these as though they could be recursive, as
  -- they are typechecked that way; the read environment to evalExpr is the same
  -- as the environment to bind a new name in.
  Let d -> bindVarList (dName d) (map f (zipListEnv lenv)) lenv
    where f env =
            case dDefinition d of
              DPrim   -> evalPrim d
              DExpr e -> evalExpr env e
