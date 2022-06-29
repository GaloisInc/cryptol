{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase     #-}

module Cryptol.Eval.FFI
  ( addForeignDecls
  ) where

import           Data.Foldable
import           Data.IORef

import           Cryptol.Backend.Concrete
import           Cryptol.Backend.FFI
import           Cryptol.Backend.Monad
import           Cryptol.Backend.WordValue
import           Cryptol.Eval
import           Cryptol.Eval.Env
import           Cryptol.Eval.Prims
import           Cryptol.Eval.Value
import           Cryptol.ModuleSystem.Env
import           Cryptol.ModuleSystem.Name
import           Cryptol.TypeCheck.AST
import           Cryptol.Utils.Ident
import           Cryptol.Utils.Panic

addForeignDecls :: ModulePath -> Module ->
  EvalEnv -> Eval (Maybe ForeignSrc, EvalEnv)
addForeignDecls path m env = io do
  foreignSrc <- newIORef Nothing
  let addForeignDeclGroup e (Recursive ds)   = foldlM addForeignDecl e ds
      addForeignDeclGroup e (NonRecursive d) = addForeignDecl e d
      addForeignDecl e d = case dDefinition d of
        DForeign -> do
          fsrc <- readIORef foreignSrc >>= \case
            Nothing -> case path of
              InFile p -> do
                fsrc <- loadForeignSrc p
                writeIORef foreignSrc $ Just fsrc
                pure fsrc
              InMem _ _ -> panic "addForeignDecl"
                ["Can't find foreign source of in-memory module"]
            Just fsrc -> pure fsrc
          impl <- loadForeignImpl fsrc $ unpackIdent $ nameIdent $ dName d
          pure $ bindVarDirect (dName d) (foreignPrim impl) e
        _ -> pure e
  env' <- foldlM addForeignDeclGroup env $ mDecls m
  fsrc <- readIORef foreignSrc
  pure (fsrc, env')

foreignPrim :: ForeignImpl -> Prim Concrete
foreignPrim impl = PStrict \case
  VWord 64 wv -> PPrim $ fmap (VWord 64 . wordVal) $
    asWordVal Concrete wv >>=
      io . fmap (mkBv 64 . toInteger) .
        callForeignImpl impl . fromInteger . bvVal
  _ -> evalPanic "foreignPrim" ["Argument is not a 64-bit word"]
