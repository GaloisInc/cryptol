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
import           Foreign
import           Foreign.C.Types
import           GHC.Float
import           LibBF

import           Cryptol.Backend.Concrete
import           Cryptol.Backend.FFI
import           Cryptol.Backend.FloatHelpers
import           Cryptol.Backend.Monad
import           Cryptol.Backend.SeqMap
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

foreignPrim :: FFIFunRep -> ForeignImpl -> Prim Concrete
foreignPrim FFIFunRep {..} impl = buildPrim ffiArgReps ($ [])
  where buildPrim [] withArgs = PPrim do
          withArgs \inArgs ->
            marshalRet ffiRetRep \outArgs ->
              callForeignImpl impl (inArgs ++ outArgs)
        buildPrim (argRep:argReps) withArgs = PStrict \val ->
          buildPrim argReps \f ->
            withArgs \prevArgs ->
              marshalArg argRep val \currArgs ->
                f $ prevArgs ++ currArgs

marshalArg :: FFIRep -> GenValue Concrete -> ([SomeFFIArg] -> Eval a) -> Eval a
marshalArg FFIBool x f = f [SomeFFIArg @Word8 $ fromBool $ fromVBit x]
marshalArg (FFIBasic r) x f = getMarshalBasicArg r \m ->
  m x >>= f . pure . SomeFFIArg
marshalArg (FFIArray n r) x f = getMarshalBasicArg r \m -> do
  args <- traverse (>>= m) $ enumerateSeqMap n $ fromVSeq x
  Eval \stk ->
    withArray args \ptr ->
      runEval stk $ f [SomeFFIArg ptr]

getMarshalBasicArg :: FFIBasicRep ->
  (forall a. FFIArg a => (GenValue Concrete -> Eval a) -> b) -> b
getMarshalBasicArg (FFIWord _ s) f = withWordType s \(_ :: p t) ->
  f @t $ fmap (fromInteger . bvVal) . fromVWord Concrete "getMarshalBasicArg"
getMarshalBasicArg (FFIFloat _ _ s) f = case s of
  FFIFloat32 -> f $ pure . CFloat . double2Float . toDouble
  FFIFloat64 -> f $ pure . CDouble . toDouble
  where toDouble = fst . bfToDouble NearEven . bfValue . fromVFloat

marshalRet :: FFIRep ->
  (forall a. FFIRet a => [SomeFFIArg] -> IO a) -> Eval (GenValue Concrete)
marshalRet FFIBool f = VBit . toBool <$> io (f @Word8 [])
marshalRet (FFIBasic r) f = getMarshalBasicRet r (io (f []) >>=)
marshalRet (FFIArray n r) f = getMarshalBasicRet r \m ->
  fmap (VSeq (toInteger n) . finiteSeqMap Concrete . map m) $
    io $ allocaArray n \ptr -> do
      f @() [SomeFFIArg ptr]
      peekArray n ptr

getMarshalBasicRet :: FFIBasicRep ->
  (forall a. FFIRet a => (a -> Eval (GenValue Concrete)) -> b) -> b
getMarshalBasicRet (FFIWord n s) f = withWordType s \(_ :: p t) ->
  f @t $ word Concrete n . toInteger
getMarshalBasicRet (FFIFloat e p s) f = case s of
  FFIFloat32 -> f $ toValue . \case CFloat x -> float2Double x
  FFIFloat64 -> f $ toValue . \case CDouble x -> x
  where toValue = pure . VFloat . BF e p . bfFromDouble

withWordType :: FFIWordSize ->
  (forall a. (FFIArg a, FFIRet a, Integral a) => Proxy a -> b) -> b
withWordType FFIWord8  f = f $ Proxy @Word8
withWordType FFIWord16 f = f $ Proxy @Word16
withWordType FFIWord32 f = f $ Proxy @Word32
withWordType FFIWord64 f = f $ Proxy @Word64

#else

evalForeignDecls :: ModulePath -> Module -> EvalEnv ->
  Eval (Either [FFILoadError] EvalEnv)
evalForeignDecls _ _ env = pure $ Right env

#endif
