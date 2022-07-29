{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ViewPatterns        #-}

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
import           LibBF                           (bfFromDouble, bfToDouble,
                                                  pattern NearEven)

import           Cryptol.Backend.Concrete
import           Cryptol.Backend.FFI
import           Cryptol.Backend.FloatHelpers
import           Cryptol.Backend.Monad
import           Cryptol.Backend.SeqMap
import           Cryptol.Eval.Env
import           Cryptol.Eval.Prims
import           Cryptol.Eval.Type
import           Cryptol.Eval.Value
import           Cryptol.ModuleSystem.Name
import           Cryptol.TypeCheck.FFI.FFIType
import           Cryptol.TypeCheck.Solver.InfNat
import           Cryptol.Utils.Ident
import           Cryptol.Utils.RecordMap

evalForeignDecls :: ModulePath -> Module -> EvalEnv ->
  Eval (Either [FFILoadError] EvalEnv)
evalForeignDecls path m env = do
  foreignSrc <- liftIO $ newIORef Nothing
  let evalForeignDeclGroup e (Recursive ds)   = foldlM evalForeignDecl e ds
      evalForeignDeclGroup e (NonRecursive d) = evalForeignDecl e d
      evalForeignDecl e d = case dDefinition d of
        DForeign ffiType -> do
          fsrc <- liftIO (readIORef foreignSrc) >>= \case
            Nothing -> case path of
              InFile p -> do
                fsrc <- liftIO (loadForeignSrc p) >>= liftEither
                liftIO $ writeIORef foreignSrc $ Just fsrc
                pure fsrc
              InMem _ _ -> evalPanic "evalForeignDecls"
                ["Can't find foreign source of in-memory module"]
            Just fsrc -> pure fsrc
          liftIO (loadForeignImpl fsrc $ unpackIdent $ nameIdent $ dName d)
            >>= \case
              Left err -> tell [err] >> pure e
              Right impl -> pure $ bindVarDirect (dName d)
                (foreignPrimPoly (dName d) ffiType impl) e
        _ -> pure e
      report (Left err)         = Left [err]
      report (Right (env', [])) = Right env'
      report (Right (_, errs))  = Left errs
  fmap report $ runExceptT $ runWriterT $
    foldlM evalForeignDeclGroup env $ mDecls m

foreignPrimPoly :: Name -> FFIFunType -> ForeignImpl -> Prim Concrete
foreignPrimPoly name fft impl = buildNumPoly (ffiTParams fft) mempty
  where buildNumPoly (tp:tps) tenv = PNumPoly \n ->
          buildNumPoly tps $ bindTypeVar (TVBound tp) (Left n) tenv
        buildNumPoly [] tenv = foreignPrim name fft impl tenv

data GetRet = GetRet
  { getRetAsValue   :: forall a. FFIRet a => IO a
  , getRetAsOutArgs :: [SomeFFIArg] -> IO () }

foreignPrim :: Name -> FFIFunType -> ForeignImpl -> TypeEnv -> Prim Concrete
foreignPrim name FFIFunType {..} impl tenv = buildFun ffiArgTypes ($ [])
  where

  buildFun :: [FFIType] ->
    (([SomeFFIArg] -> Eval (GenValue Concrete)) -> Eval (GenValue Concrete)) ->
    Prim Concrete
  buildFun (argType:argTypes) withArgs = PStrict \val ->
    buildFun argTypes \f ->
      withArgs \prevArgs ->
        marshalArg argType val \currArgs ->
          f $ prevArgs ++ currArgs
  buildFun [] withArgs = PPrim do
    withArgs \inArgs -> do
      tyArgs <- traverse marshalTyArg ffiTParams
      let tyInArgs = tyArgs ++ inArgs
      marshalRet ffiRetType GetRet
        { getRetAsValue = callForeignImpl impl tyInArgs
        , getRetAsOutArgs = callForeignImpl impl . (tyInArgs ++) }

  marshalTyArg :: TParam -> Eval SomeFFIArg
  marshalTyArg tp = case lookupTypeVar (TVBound tp) tenv of
    Just (Left (Nat n))
      | n <= toInteger (maxBound :: CSize) ->
        pure $ SomeFFIArg @CSize $ fromInteger n
      | otherwise -> raiseError Concrete $ FFITypeNumTooBig name tp n
    x -> evalPanic "marshalTyArg"
      ["Bad type env lookup", show name, show tp, show x]

  marshalArg :: FFIType -> GenValue Concrete ->
    ([SomeFFIArg] -> Eval a) -> Eval a
  marshalArg FFIBool val f = f [SomeFFIArg @Word8 $ fromBool $ fromVBit val]
  marshalArg (FFIBasic t) val f = getMarshalBasicArg t \m -> do
    arg <- m val
    f [SomeFFIArg arg]
  marshalArg (FFIArray (evalFinType -> n) t) val f =
    getMarshalBasicArg t \m -> do
      args <- traverse (>>= m) $ enumerateSeqMap n $ fromVSeq val
      Eval \stk ->
        withArray args \ptr ->
          runEval stk $ f [SomeFFIArg ptr]
  marshalArg (FFITuple types) val f = marshalArgs (zip types (fromVTuple val)) f
  marshalArg (FFIRecord typeMap) val f = marshalArgs (zip types evals) f
    where types = displayElements typeMap
          evals = map (`lookupRecord` val) $ displayOrder typeMap

  marshalArgs :: [(FFIType, Eval (GenValue Concrete))] ->
    ([SomeFFIArg] -> Eval a) -> Eval a
  marshalArgs typesAndEvals f = go typesAndEvals []
    where go [] args = f args
          go ((t, ev):tevs) prevArgs = do
            v <- ev
            marshalArg t v \currArgs ->
              go tevs (prevArgs ++ currArgs)

  marshalRet :: FFIType -> GetRet -> Eval (GenValue Concrete)
  marshalRet FFIBool gr = VBit . toBool <$> io (getRetAsValue gr @Word8)
  marshalRet (FFIBasic t) gr = getMarshalBasicRet t (io (getRetAsValue gr) >>=)
  marshalRet (FFIArray (evalFinType -> n) t) gr = getMarshalBasicRet t \m ->
    fmap (VSeq n . finiteSeqMap Concrete . map m) $
      io $ allocaArray (fromInteger n) \ptr -> do
        getRetAsOutArgs gr [SomeFFIArg ptr]
        peekArray (fromInteger n) ptr
  marshalRet (FFITuple types) gr = VTuple <$> marshalMultiRet types gr
  marshalRet (FFIRecord typeMap) gr =
    VRecord . recordFromFields . zip (displayOrder typeMap) <$>
      marshalMultiRet (displayElements typeMap) gr

  marshalMultiRet :: [FFIType] -> GetRet -> Eval [Eval (GenValue Concrete)]
  marshalMultiRet types gr = Eval \stk -> do
    vals <- newIORef []
    let go [] args = getRetAsOutArgs gr args
        go (t:ts) prevArgs = do
          val <- runEval stk $ marshalRet t $ getRetFromAsOutArgs \currArgs ->
            go ts (prevArgs ++ currArgs)
          modifyIORef' vals (val :)
    go types []
    map pure <$> readIORef vals

  evalFinType :: Type -> Integer
  evalFinType = finNat' . evalNumType tenv

getRetFromAsOutArgs :: ([SomeFFIArg] -> IO ()) -> GetRet
getRetFromAsOutArgs f = GetRet
  { getRetAsValue = alloca \ptr -> do
      f [SomeFFIArg ptr]
      peek ptr
  , getRetAsOutArgs = f }

getMarshalBasicArg :: FFIBasicType ->
  (forall a. FFIArg a => (GenValue Concrete -> Eval a) -> b) -> b
getMarshalBasicArg (FFIWord _ s) f = withWordType s \(_ :: p t) ->
  f @t $ fmap (fromInteger . bvVal) . fromVWord Concrete "getMarshalBasicArg"
getMarshalBasicArg (FFIFloat _ _ s) f = case s of
  FFIFloat32 -> f $ pure . CFloat . double2Float . toDouble
  FFIFloat64 -> f $ pure . CDouble . toDouble
  where toDouble = fst . bfToDouble NearEven . bfValue . fromVFloat

getMarshalBasicRet :: FFIBasicType ->
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
