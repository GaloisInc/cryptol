{-# LANGUAGE BlockArguments   #-}
{-# LANGUAGE CPP              #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}

module Cryptol.Eval.FFI
  ( evalForeignDecls
  ) where

import           Cryptol.Backend.FFI.Error
import           Cryptol.Eval
import           Cryptol.ModuleSystem.Env
import           Cryptol.TypeCheck.AST

#ifdef FFI_ENABLED

import           Control.Monad.Except
import           Control.Monad.Writer.Strict
import           Data.Foldable
import           Data.IORef

import           Cryptol.Backend.Concrete
import           Cryptol.Backend.FFI
import           Cryptol.Backend.Monad
import           Cryptol.Backend.WordValue
import           Cryptol.Eval.Env
import           Cryptol.Eval.Prims
import           Cryptol.Eval.Value
import           Cryptol.ModuleSystem.Name
import           Cryptol.Utils.Ident
import           Cryptol.Utils.Panic

evalForeignDecls :: ModulePath -> Module -> EvalEnv ->
  Eval (Either [FFILoadError] EvalEnv)
evalForeignDecls path m env = do
  foreignSrc <- liftIO $ newIORef Nothing
  let evalForeignDeclGroup e (Recursive ds)   = foldlM evalForeignDecl e ds
      evalForeignDeclGroup e (NonRecursive d) = evalForeignDecl e d
      evalForeignDecl e d = case dDefinition d of
        DForeign -> do
          fsrc <- liftIO (readIORef foreignSrc) >>= \case
            Nothing -> case path of
              InFile p -> do
                fsrc <- liftIO (loadForeignSrc p) >>= liftEither
                liftIO $ writeIORef foreignSrc $ Just fsrc
                pure fsrc
              InMem _ _ -> panic "evalForeignDecls"
                ["Can't find foreign source of in-memory module"]
            Just fsrc -> pure fsrc
          liftIO (loadForeignImpl fsrc $ unpackIdent $ nameIdent $ dName d)
            >>= \case
              Left err   -> tell [err] >> pure e
              Right impl -> pure $ bindVarDirect (dName d) (foreignPrim impl) e
        _ -> pure e
      report (Left err)         = Left [err]
      report (Right (env', [])) = Right env'
      report (Right (_, errs))  = Left errs
  fmap report $ runExceptT $ runWriterT $
    foldlM evalForeignDeclGroup env $ mDecls m

foreignPrim :: ForeignImpl -> Prim Concrete
foreignPrim impl = PStrict \case
  VWord 64 wv -> PPrim $ fmap (VWord 64 . wordVal) $
    asWordVal Concrete wv >>=
      io . fmap (mkBv 64 . toInteger) .
        callForeignImpl impl . fromInteger . bvVal
  _ -> evalPanic "foreignPrim" ["Argument is not a 64-bit word"]

#else

evalForeignDecls :: ModulePath -> Module -> EvalEnv ->
  Eval (Either [FFILoadError] EvalEnv)
evalForeignDecls _ _ env = pure $ Right env

#endif
