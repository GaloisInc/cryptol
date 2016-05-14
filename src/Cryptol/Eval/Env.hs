-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE CPP #-}
module Cryptol.Eval.Env where

import Cryptol.Eval.Monad( Eval, delay )
import Cryptol.Eval.Value
import Cryptol.ModuleSystem.Name
import Cryptol.TypeCheck.AST
import Cryptol.Utils.PP

import qualified Data.Map.Strict as Map

import GHC.Generics (Generic)
import Control.DeepSeq
import Control.DeepSeq.Generics

import Prelude ()
import Prelude.Compat

-- Evaluation Environment ------------------------------------------------------

type ReadEnv = EvalEnv

data EvalEnv = EvalEnv
  { envVars       :: !(Map.Map Name (Eval Value))
  , envTypes      :: !(Map.Map TVar TValue)
  } deriving (Generic)

instance NFData EvalEnv where rnf = genericRnf

instance Monoid EvalEnv where
  mempty = EvalEnv
    { envVars       = Map.empty
    , envTypes      = Map.empty
    }

  mappend l r = EvalEnv
    { envVars     = Map.union (envVars     l) (envVars     r)
    , envTypes    = Map.union (envTypes    l) (envTypes    r)
    }

ppEnv :: PPOpts -> EvalEnv -> Eval Doc
ppEnv opts env = brackets . fsep <$> mapM bind (Map.toList (envVars env))
  where
   bind (k,v) = do vdoc <- ppValue opts =<< v
                   return (pp k <+> text "->" <+> vdoc)

--instance PP (WithBase EvalEnv) where
--  ppPrec _ (WithBase opts env) = brackets (fsep (map bind (Map.toList (envVars env))))
--    where
--    bind (k,v) = pp k <+> text "->" <+> ppValue opts v

emptyEnv :: EvalEnv
emptyEnv  = mempty

-- | Bind a variable in the evaluation environment.
bindVar :: Name -> Eval Value -> EvalEnv -> Eval EvalEnv
bindVar n val env = do
  let nm = show $ ppLocName n
  val' <- delay (Just nm) val
  return $ env { envVars = Map.insert n val' (envVars env) }

-- | Lookup a variable in the environment.
{-# INLINE lookupVar #-}
lookupVar :: Name -> EvalEnv -> Maybe (Eval Value)
lookupVar n env = Map.lookup n (envVars env)

-- | Bind a type variable of kind *.
{-# INLINE bindType #-}
bindType :: TVar -> TValue -> EvalEnv -> EvalEnv
bindType p ty env = env { envTypes = Map.insert p ty (envTypes env) }

-- | Lookup a type variable.
{-# INLINE lookupType #-}
lookupType :: TVar -> EvalEnv -> Maybe TValue
lookupType p env = Map.lookup p (envTypes env)
