-- |
-- Module      :  Cryptol.Eval.Env
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
module Cryptol.Eval.Env where

import Cryptol.Backend

import Cryptol.Eval.Prims
import Cryptol.Eval.Type
import Cryptol.Eval.Value
import Cryptol.ModuleSystem.Name
import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Solver.InfNat
import Cryptol.Utils.PP

import qualified Data.IntMap.Strict as IntMap
import Data.Semigroup

import GHC.Generics (Generic)

import Prelude ()
import Prelude.Compat

-- Evaluation Environment ------------------------------------------------------

data GenEvalEnv sym = EvalEnv
  { envVars       :: !(IntMap.IntMap (Either (Prim sym) (SEval sym (GenValue sym))))
  , envTypes      :: !TypeEnv
  } deriving Generic

instance Semigroup (GenEvalEnv sym) where
  l <> r = EvalEnv
    { envVars     = IntMap.union (envVars l) (envVars r)
    , envTypes    = envTypes l <> envTypes r
    }

instance Monoid (GenEvalEnv sym) where
  mempty = EvalEnv
    { envVars       = IntMap.empty
    , envTypes      = mempty
    }
  mappend = (<>)

ppEnv :: Backend sym => sym -> PPOpts -> GenEvalEnv sym -> SEval sym Doc
ppEnv sym opts env = brackets . fsep <$> mapM bind (IntMap.toList (envVars env))
  where
   bind (k,Left _) =
      do return (int k <+> text "<<prim>>")
   bind (k,Right v) =
      do vdoc <- ppValue sym opts =<< v
         return (int k <+> text "->" <+> vdoc)

-- | Evaluation environment with no bindings
emptyEnv :: GenEvalEnv sym
emptyEnv  = mempty

-- | Bind a variable in the evaluation environment.
bindVar ::
  Backend sym =>
  sym ->
  Name ->
  SEval sym (GenValue sym) ->
  GenEvalEnv sym ->
  SEval sym (GenEvalEnv sym)
bindVar sym n val env = do
  let nm = show $ ppLocName n
  val' <- sDelayFill sym val Nothing nm
  return $ env{ envVars = IntMap.insert (nameUnique n) (Right val') (envVars env) }

-- | Bind a variable to a value in the evaluation environment, without
--   creating a thunk.
bindVarDirect ::
  Backend sym =>
  Name ->
  Prim sym ->
  GenEvalEnv sym ->
  GenEvalEnv sym
bindVarDirect n val env = do
  env{ envVars = IntMap.insert (nameUnique n) (Left val) (envVars env) }

-- | Lookup a variable in the environment.
{-# INLINE lookupVar #-}
lookupVar :: Name -> GenEvalEnv sym -> Maybe (Either (Prim sym) (SEval sym (GenValue sym)))
lookupVar n env = IntMap.lookup (nameUnique n) (envVars env)

-- | Bind a type variable of kind *.
{-# INLINE bindType #-}
bindType :: TVar -> Either Nat' TValue -> GenEvalEnv sym -> GenEvalEnv sym
bindType p ty env = env{ envTypes = bindTypeVar p ty (envTypes env) }

-- | Lookup a type variable.
{-# INLINE lookupType #-}
lookupType :: TVar -> GenEvalEnv sym -> Maybe (Either Nat' TValue)
lookupType p env = lookupTypeVar p (envTypes env)

