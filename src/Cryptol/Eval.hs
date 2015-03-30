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
import Cryptol.TypeCheck.AST
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.PP
import Cryptol.Prims.Eval

import Data.List (transpose)
import qualified Data.Map as Map

#if __GLASGOW_HASKELL__ < 710
import Data.Monoid (Monoid(..),mconcat)
#endif

-- Expression Evaluation -------------------------------------------------------

moduleEnv :: Module -> EvalEnv -> EvalEnv
moduleEnv m env = evalDecls (mDecls m) (evalNewtypes (mNewtypes m) env)

evalExpr :: EvalEnv -> Expr -> Value
evalExpr env expr = case expr of

  ECon con -> evalECon con

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

evalNewtypes :: Map.Map QName Newtype -> EvalEnv -> EvalEnv
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
evalDecl renv d = bindVar (dName d) (evalExpr renv (dDefinition d))


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
  benvs = map (branchEnvs env) ms

  -- take parallel slices of each environment.  when the length of the list
  -- drops below the number of branches, one branch has terminated.
  allBranches es = length es == length ms
  slices         = takeWhile allBranches (transpose benvs)

  -- join environments to produce environments at each step through the process.
  envs = map mconcat slices

-- | Turn a list of matches into the final environments for each iteration of
-- the branch.
branchEnvs :: ReadEnv -> [Match] -> [EvalEnv]
branchEnvs env matches = case matches of

  m:ms -> do
    env' <- evalMatch env m
    branchEnvs env' ms

  [] -> return env

-- | Turn a match into the list of environments it represents.
evalMatch :: EvalEnv -> Match -> [EvalEnv]
evalMatch env m = case m of

  -- many envs
  From n _ty expr -> do
    e <- fromSeq (evalExpr env expr)
    return (bindVar n e env)

  -- XXX we don't currently evaluate these as though they could be recursive, as
  -- they are typechecked that way; the read environment to evalDecl is the same
  -- as the environment to bind a new name in.
  Let d -> [evalDecl env d env]
