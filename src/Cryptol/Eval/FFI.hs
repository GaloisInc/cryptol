{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE TupleSections       #-}

-- | Evaluation of foreign functions.
module Cryptol.Eval.FFI
  ( findForeignDecls
  , evalForeignDecls
  ) where

import Cryptol.Eval.FFI.ForeignSrc
    ( ForeignSrc)
#ifdef FFI_ENABLED
import Cryptol.Eval.FFI.ForeignSrc
    (ForeignImpl, loadForeignImpl )
#else
import Cryptol.Parser.AST (ForeignMode)
#endif
import Cryptol.Eval.FFI.Error ( FFILoadError )
import Cryptol.Eval (Eval, EvalEnv )
import Cryptol.TypeCheck.AST
    ( Name, FFI(..), TVar(TVBound), findForeignDecls )
import Cryptol.TypeCheck.FFI.FFIType ( FFIFunType(..) )

#ifdef FFI_ENABLED

import           Data.Either(partitionEithers)
import           Data.Traversable(for)
import           Cryptol.Backend.Concrete
import           Cryptol.Backend.Monad
import           Cryptol.Eval.Env
import           Cryptol.Eval.Prims
import           Cryptol.Eval.Type
import           Cryptol.Eval.Value
import           Cryptol.ModuleSystem.Name
import           Cryptol.Utils.Ident
import           Cryptol.Eval.FFI.C(callForeignC)
import           Cryptol.Eval.FFI.Abstract(callForeignAbstract)

#endif

#ifdef FFI_ENABLED

-- | Add the given foreign declarations to the environment, loading their
-- implementations from the given 'ForeignSrc'. If some implementations fail to
-- load then errors are reported for them but any successfully loaded
-- implementations are still added to the environment.
--
-- This is a separate pass from the main evaluation functions in "Cryptol.Eval"
-- since it only works for the Concrete backend.
evalForeignDecls :: ForeignSrc -> [(Name, FFI)] -> EvalEnv ->
  Eval ([FFILoadError], EvalEnv)
evalForeignDecls fsrc decls env = io do
  (errs, prims) <- partitionEithers <$> for decls \(name, cc) ->
    fmap ((name,) . foreignPrimPoly cc name) <$>
      loadForeignImpl fsrc (unpackIdent $ nameIdent name)
  pure (errs, foldr (uncurry bindVarDirect) env prims)

-- | Generate a 'Prim' value representing the given foreign function, containing
-- all the code necessary to marshal arguments and return values and do the
-- actual FFI call.
foreignPrimPoly :: FFI -> Name -> ForeignImpl -> Prim Concrete
foreignPrimPoly cc name impl =
  case cc of
    CallC t -> foreignPrim t (callForeignC name t impl)
    CallAbstract t -> foreignPrim t (callForeignAbstract name t impl)

-- | Generate a Prim for a foreign functions.
foreignPrim ::
  FFIFunType t ->
  (TypeEnv -> [(t,GenValue s)] -> SEval s (GenValue s)) ->
  Prim s 
foreignPrim ft k = buildNumPoly (ffiTParams ft) mempty
  where
  buildNumPoly (tp:tps) tenv = PNumPoly \n ->
    buildNumPoly tps (bindTypeVar (TVBound tp) (Left n) tenv)
  buildNumPoly [] tenv = buildArgs tenv (ffiArgTypes ft) []

  buildArgs tenv (argType:argTypes) typesAndVals = PStrict \val ->
    buildArgs tenv argTypes ((argType,val) : typesAndVals)
  buildArgs tenv [] typesAndVals = PPrim (k tenv (reverse typesAndVals))


#else

-- | Dummy implementation for when FFI is disabled. Does not add anything to
-- the environment or report any errors.
evalForeignDecls :: ForeignSrc -> [(Name, FFI)] -> EvalEnv ->
  Eval ([FFILoadError], EvalEnv)
evalForeignDecls _ _ env = pure ([], env)

#endif
