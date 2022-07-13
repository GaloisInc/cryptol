{-# LANGUAGE BlockArguments   #-}
{-# LANGUAGE CPP              #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RecordWildCards  #-}

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
import           Data.Word

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
withArg FFIBool x f       = f @Word8 $ fromIntegral $ fromEnum $ fromVBit x
withArg (FFIWord8 _) x f  = withWordArg @Word8 x f
withArg (FFIWord16 _) x f = withWordArg @Word16 x f
withArg (FFIWord32 _) x f = withWordArg @Word32 x f
withArg (FFIWord64 _) x f = withWordArg @Word64 x f

withWordArg :: Integral a => GenValue Concrete -> (a -> Eval b) -> Eval b
withWordArg x f =
  fromVWord Concrete "withWordArg" x >>= f . fromInteger . bvVal

withRet :: FFIRep -> (forall a. FFIType a => Eval a) -> Eval (GenValue Concrete)
withRet FFIBool x       = VBit . toEnum . fromIntegral <$> x @Word8
withRet (FFIWord8 n) x  = wordToValue @Word8 n x
withRet (FFIWord16 n) x = wordToValue @Word16 n x
withRet (FFIWord32 n) x = wordToValue @Word32 n x
withRet (FFIWord64 n) x = wordToValue @Word64 n x

wordToValue :: Integral a => Integer -> Eval a -> Eval (GenValue Concrete)
wordToValue n = (>>= word Concrete n . toInteger)

#else

evalForeignDecls :: ModulePath -> Module -> EvalEnv ->
  Eval (Either [FFILoadError] EvalEnv)
evalForeignDecls _ _ env = pure $ Right env

#endif
