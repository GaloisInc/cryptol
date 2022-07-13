{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

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
import           Data.Proxy
import           Data.Word
import           Foreign.Marshal.Utils

import           Cryptol.Backend.Concrete
import           Cryptol.Backend.FFI
import           Cryptol.Backend.Monad
import           Cryptol.Eval.Env
import           Cryptol.Eval.Prims
import           Cryptol.Eval.Value
import           Cryptol.ModuleSystem.Name
import           Cryptol.TypeCheck.FFI
import           Cryptol.Utils.Ident
import           Cryptol.Utils.Panic

evalForeignDecls :: ModulePath -> Module -> EvalEnv ->
  Eval (Either [FFILoadError] EvalEnv)
evalForeignDecls path m env = do
  foreignSrc <- liftIO $ newIORef Nothing
  let evalForeignDeclGroup e (Recursive ds)   = foldlM evalForeignDecl e ds
      evalForeignDeclGroup e (NonRecursive d) = evalForeignDecl e d
      evalForeignDecl e d = case dDefinition d of
        DForeign rep -> do
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
              Left err -> tell [err] >> pure e
              Right impl -> pure $
                bindVarDirect (dName d) (foreignPrim rep impl) e
        _ -> pure e
      report (Left err)         = Left [err]
      report (Right (env', [])) = Right env'
      report (Right (_, errs))  = Left errs
  fmap report $ runExceptT $ runWriterT $
    foldlM evalForeignDeclGroup env $ mDecls m

{- HLINT ignore foreignPrim "Avoid lambda" -}
foreignPrim :: FFIFunRep -> ForeignImpl -> Prim Concrete
foreignPrim FFIFunRep {..} impl = PStrict \val ->
  PPrim $ withArg ffiArgRep val \arg ->
    withRet ffiRetRep $ io $ callForeignImpl impl arg

withArg :: FFIRep -> GenValue Concrete ->
  (forall a. FFIType a => a -> Eval b) -> Eval b
withArg FFIBool x f = f @Word8 $ fromBool $ fromVBit x
withArg (FFIWord _ s) x f = withWordType s \(_ :: p t) ->
  fromVWord Concrete "withArg" x >>= f @t . fromInteger . bvVal

withRet :: FFIRep -> (forall a. FFIType a => Eval a) -> Eval (GenValue Concrete)
withRet FFIBool x = VBit . toBool <$> x @Word8
withRet (FFIWord n s) x = withWordType s \(_ :: p t) ->
  x @t >>= word Concrete n . toInteger

withWordType :: FFIWordSize ->
  (forall proxy a. (FFIType a, Integral a) => proxy a -> b) -> b
withWordType FFIWord8  = ($ Proxy @Word8)
withWordType FFIWord16 = ($ Proxy @Word16)
withWordType FFIWord32 = ($ Proxy @Word32)
withWordType FFIWord64 = ($ Proxy @Word64)

#else

evalForeignDecls :: ModulePath -> Module -> EvalEnv ->
  Eval (Either [FFILoadError] EvalEnv)
evalForeignDecls _ _ env = pure $ Right env

#endif
