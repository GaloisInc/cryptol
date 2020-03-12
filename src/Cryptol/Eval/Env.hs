-- |
-- Module      :  Cryptol.Eval.Env
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe #-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
module Cryptol.Eval.Env where

import Cryptol.Eval.Monad( Eval, delay, ready, PPOpts )
import Cryptol.Eval.Type
import Cryptol.Eval.Value
import Cryptol.ModuleSystem.Name
import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Solver.InfNat
import Cryptol.Utils.PP


import qualified Data.Map.Strict as Map
import Data.Semigroup

import GHC.Generics (Generic)

import Prelude ()
import Prelude.Compat

-- Evaluation Environment ------------------------------------------------------

data GenEvalEnv sym = EvalEnv
  { envVars       :: !(Map.Map Name (Eval (GenValue sym)))
  , envTypes      :: !TypeEnv
  } deriving Generic

instance Semigroup (GenEvalEnv sym) where
  l <> r = EvalEnv
    { envVars     = Map.union (envVars     l) (envVars     r)
    , envTypes    = Map.union (envTypes    l) (envTypes    r)
    }

instance Monoid (GenEvalEnv sym) where
  mempty = EvalEnv
    { envVars       = Map.empty
    , envTypes      = Map.empty
    }

  mappend l r = l <> r

ppEnv :: Backend sym => sym -> PPOpts -> GenEvalEnv sym -> Eval Doc
ppEnv sym opts env = brackets . fsep <$> mapM bind (Map.toList (envVars env))
  where
   bind (k,v) = do vdoc <- ppValue sym opts =<< v
                   return (pp k <+> text "->" <+> vdoc)

-- | Evaluation environment with no bindings
emptyEnv :: GenEvalEnv sym
emptyEnv  = mempty

-- | Bind a variable in the evaluation environment.
bindVar :: Name
        -> Eval (GenValue sym)
        -> GenEvalEnv sym
        -> Eval (GenEvalEnv sym)
bindVar n val env = do
  let nm = show $ ppLocName n
  val' <- delay (Just nm) val
  return $ env{ envVars = Map.insert n val' (envVars env) }

-- | Bind a variable to a value in the evaluation environment, without
--   creating a thunk.
bindVarDirect :: Name
              -> GenValue sym
              -> GenEvalEnv sym
              -> GenEvalEnv sym
bindVarDirect n val env = do
  env{ envVars = Map.insert n (ready val) (envVars env) }

-- | Lookup a variable in the environment.
{-# INLINE lookupVar #-}
lookupVar :: Name -> GenEvalEnv sym -> Maybe (Eval (GenValue sym))
lookupVar n env = Map.lookup n (envVars env)

-- | Bind a type variable of kind *.
{-# INLINE bindType #-}
bindType :: TVar -> Either Nat' TValue -> GenEvalEnv sym -> GenEvalEnv sym
bindType p ty env = env { envTypes = Map.insert p ty (envTypes env) }

-- | Lookup a type variable.
{-# INLINE lookupType #-}
lookupType :: TVar -> GenEvalEnv sym -> Maybe (Either Nat' TValue)
lookupType p env = Map.lookup p (envTypes env)

