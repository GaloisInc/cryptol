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
    ( ForeignSrc, ForeignImpl, loadForeignImpl )
import Cryptol.Eval.FFI.Error ( FFILoadError )
import Cryptol.Eval ( EvalEnv )
import Cryptol.TypeCheck.AST
    ( ForeignMode(..), TVar(TVBound), findForeignDecls )
import Cryptol.TypeCheck.FFI.FFIType ( FFIFunType(..), FFIType )

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
import           Cryptol.Eval.FFI.C

#endif

#ifdef FFI_ENABLED

-- | Add the given foreign declarations to the environment, loading their
-- implementations from the given 'ForeignSrc'. If some implementations fail to
-- load then errors are reported for them but any successfully loaded
-- implementations are still added to the environment.
--
-- This is a separate pass from the main evaluation functions in "Cryptol.Eval"
-- since it only works for the Concrete backend.
evalForeignDecls :: ForeignSrc -> [(Name, ForeignMode, FFIFunType)] -> EvalEnv ->
  Eval ([FFILoadError], EvalEnv)
evalForeignDecls fsrc decls env = io do
  (errs, prims) <- partitionEithers <$> for decls \(name, cc, ffiFunType) ->
    fmap ((name,) . foreignPrimPoly cc name ffiFunType) <$>
      loadForeignImpl fsrc (unpackIdent $ nameIdent name)
  pure (errs, foldr (uncurry bindVarDirect) env prims)

-- | Generate a 'Prim' value representing the given foreign function, containing
-- all the code necessary to marshal arguments and return values and do the
-- actual FFI call.
foreignPrimPoly :: ForeignMode -> Name -> FFIFunType -> ForeignImpl -> Prim Concrete
foreignPrimPoly cc name fft impl = buildNumPoly (ffiTParams fft) mempty
  where -- Add type lambdas for the type parameters and build a type environment
        -- that we can look up later to compute e.g. array sizes.
        --
        -- Given [p1, p2, ..., pk] {}, returns
        -- PNumPoly \n1 -> PNumPoly \n2 -> ... PNumPoly \nk ->
        --   foreignPrim name fft impl {p1 = n1, p2 = n2, ..., pk = nk}
        buildNumPoly (tp:tps) tenv = PNumPoly \n ->
          buildNumPoly tps $ bindTypeVar (TVBound tp) (Left n) tenv
        buildNumPoly [] tenv = foreignPrim cc name fft impl tenv


-- | Generate the monomorphic part of the foreign 'Prim', given a 'TypeEnv'
-- containing all the type arguments we have already received.
foreignPrim :: ForeignMode -> Name -> FFIFunType -> ForeignImpl -> TypeEnv -> Prim Concrete
foreignPrim cc name ft@FFIFunType {..} impl tenv = buildFun ffiArgTypes []
  where

  -- Build up the 'Prim' function for the FFI call.
  --
  -- Given [t1, t2 ... tm] we return
  -- PStrict \v1 -> PStrict \v2 -> ... PStrict \vm -> PPrim $
  --   call foreign function

  buildFun :: [FFIType] -> [(FFIType, GenValue Concrete)] -> Prim Concrete
  buildFun (argType:argTypes) typesAndVals = PStrict \val ->
    buildFun argTypes $ typesAndVals ++ [(argType, val)]
  buildFun [] typesAndVals = PPrim $
    case cc of
      ForeignC -> callForeignC name ft impl tenv typesAndVals    
      ForeignAbstract ->
        error "buildFun" ["ForeignAbstract is not yet supported"]



#else

-- | Dummy implementation for when FFI is disabled. Does not add anything to
-- the environment or report any errors.
evalForeignDecls :: ForeignSrc -> [(Name, ForeignMode, FFIFunType)] -> EvalEnv ->
  Eval ([FFILoadError], EvalEnv)
evalForeignDecls _ _ env = pure ([], env)

#endif
