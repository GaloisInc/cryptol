{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ViewPatterns        #-}

-- | Evaluation of foreign functions.
module Cryptol.Eval.FFI
  ( evalForeignDecls
  ) where

import           Cryptol.Backend.FFI.Error
import           Cryptol.Eval
import           Cryptol.ModuleSystem.Env
import           Cryptol.TypeCheck.AST

#ifdef FFI_ENABLED

import           Data.Either
import           Data.IORef
import           Data.Maybe
import           Data.Proxy
import           Data.Traversable
import           Data.Word
import           Foreign
import           Foreign.C.Types
import           GHC.Float
import           LibBF                           (bfFromDouble, bfToDouble,
                                                  pattern NearEven)
import           System.Directory

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

-- | Find all the foreign declarations in the module and add them to the
-- environment. This is a separate pass from the main evaluation functions in
-- "Cryptol.Eval" since it only works for the Concrete backend.
--
-- Note: 'Right' is only returned if we successfully loaded some foreign
-- functions and the environment was modified. If there were no foreign
-- declarations at all then @Left []@ is returned, so 'Left' does not
-- necessarily indicate an error.
evalForeignDecls :: ModulePath -> Module -> EvalEnv ->
  Eval (Either [FFILoadError] (ForeignSrc, EvalEnv))
evalForeignDecls path m env = io
  case mapMaybe getForeign $ mDecls m of
    [] -> pure $ Left []
    foreigns ->
      case path of
        InFile p -> canonicalizePath p >>= loadForeignSrc >>=
          \case
            Right fsrc -> collect <$> for foreigns \(name, ffiType) ->
              fmap ((name,) . foreignPrimPoly name ffiType) <$>
                loadForeignImpl fsrc (unpackIdent $ nameIdent name)
              where collect (partitionEithers -> (errs, primMap))
                      | null errs = Right
                        (fsrc, foldr (uncurry bindVarDirect) env primMap)
                      | otherwise = Left errs
            Left err -> pure $ Left [err]
        -- We don't handle in-memory modules for now
        InMem _ _ -> evalPanic "evalForeignDecls"
          ["Can't find foreign source of in-memory module"]
  where getForeign (NonRecursive Decl { dName, dDefinition = DForeign ffiType })
          = Just (dName, ffiType)
        getForeign _ = Nothing

-- | Generate a 'Prim' value representing the given foreign function, containing
-- all the code necessary to marshal arguments and return values and do the
-- actual FFI call.
foreignPrimPoly :: Name -> FFIFunType -> ForeignImpl -> Prim Concrete
foreignPrimPoly name fft impl = buildNumPoly (ffiTParams fft) mempty
  where -- Add type lambdas for the type parameters and build a type environment
        -- that we can look up later to compute e.g. array sizes.
        --
        -- Given [p1, p2, ..., pk] {}, returns
        -- PNumPoly \n1 -> PNumPoly \n2 -> ... PNumPoly \nk ->
        --   foreignPrim name fft impl {p1 = n1, p2 = n2, ..., pk = nk}
        buildNumPoly (tp:tps) tenv = PNumPoly \n ->
          buildNumPoly tps $ bindTypeVar (TVBound tp) (Left n) tenv
        buildNumPoly [] tenv = foreignPrim name fft impl tenv

-- | Methods for obtaining a return value. The producer of this type must supply
-- both 1) a polymorphic IO object directly containing a return value that the
-- consumer can instantiate at any 'FFIRet' type, and 2) an effectful function
-- that takes some output arguments and modifies what they are pointing at to
-- store a return value. The consumer can choose which one to use.
data GetRet = GetRet
  { getRetAsValue   :: forall a. FFIRet a => IO a
  , getRetAsOutArgs :: [SomeFFIArg] -> IO () }

-- | Generate the monomorphic part of the foreign 'Prim', given a 'TypeEnv'
-- containing all the type arguments we have already received.
foreignPrim :: Name -> FFIFunType -> ForeignImpl -> TypeEnv -> Prim Concrete
foreignPrim name FFIFunType {..} impl tenv = buildFun ffiArgTypes []
  where

  -- Build up the 'Prim' function for the FFI call.
  --
  -- Given [t1, t2 ... tm] we return
  -- PStrict \v1 -> PStrict \v2 -> ... PStrict \vm -> PPrim $
  --   marshalArg t1 v1 \a1 ->
  --     marshalArg t2 v2 \a2 -> ... marshalArg tm vm \am ->
  --       marshalRet ffiRetType GetRet
  --         { getRetAsValue = callForeignImpl impl [n1, ..., nk, a1, ..., am]
  --         , getRetAsOutArgs = \[o1, ..., ol] ->
  --             callForeignImpl impl [n1, ..., nk, a1, ..., am, o1, ..., ol] }
  buildFun :: [FFIType] -> [(FFIType, GenValue Concrete)] -> Prim Concrete
  buildFun (argType:argTypes) typesAndVals = PStrict \val ->
    buildFun argTypes $ typesAndVals ++ [(argType, val)]
  buildFun [] typesAndVals = PPrim $
    marshalArgs typesAndVals \inArgs -> do
      tyArgs <- traverse marshalTyArg ffiTParams
      let tyInArgs = tyArgs ++ inArgs
      marshalRet ffiRetType GetRet
        { getRetAsValue = callForeignImpl impl tyInArgs
        , getRetAsOutArgs = callForeignImpl impl . (tyInArgs ++) }

  -- Look up the value of a type parameter in the type environment and marshal
  -- it.
  marshalTyArg :: TParam -> Eval SomeFFIArg
  marshalTyArg tp = case lookupTypeVar (TVBound tp) tenv of
    Just (Left (Nat n))
      | n <= toInteger (maxBound :: CSize) ->
        pure $ SomeFFIArg @CSize $ fromInteger n
      | otherwise -> raiseError Concrete $ FFITypeNumTooBig name tp n
    x -> evalPanic "marshalTyArg"
      ["Bad type env lookup", show name, show tp, show x]

  -- Marshal the given value as the given FFIType and call the given function
  -- with the results. A single Cryptol argument may correspond to any number of
  -- C arguments, so the callback takes a list.
  --
  -- NOTE: the result must be used only in the callback since it may have a
  -- limited lifetime (e.g. pointer returned by alloca).
  marshalArg :: FFIType -> GenValue Concrete ->
    ([SomeFFIArg] -> Eval a) -> Eval a
  marshalArg FFIBool val f = f [SomeFFIArg @Word8 $ fromBool $ fromVBit val]
  marshalArg (FFIBasic t) val f = getMarshalBasicArg t \m -> do
    arg <- m val
    f [SomeFFIArg arg]
  marshalArg (FFIArray (evalFinType -> n) t) val f =
    getMarshalBasicArg t \m -> do
      args <- traverse (>>= m) $ enumerateSeqMap n $ fromVSeq val
      -- Since we need to do an Eval action in an IO callback, we need to
      -- manually unwrap and wrap the Eval datatype
      Eval \stk ->
        withArray args \ptr ->
          runEval stk $ f [SomeFFIArg ptr]
  marshalArg (FFITuple types) val f = do
    vals <- sequence $ fromVTuple val
    marshalArgs (zip types vals) f
  marshalArg (FFIRecord typeMap) val f = do
    vals <- traverse (`lookupRecord` val) $ displayOrder typeMap
    marshalArgs (zip (displayElements typeMap) vals) f

  -- Call marshalArg on a bunch of arguments and collect the results together
  -- (in the order of the arguments).
  marshalArgs :: [(FFIType, GenValue Concrete)] ->
    ([SomeFFIArg] -> Eval a) -> Eval a
  marshalArgs typesAndVals f = go typesAndVals []
    where go [] args = f args
          go ((t, v):tvs) prevArgs = marshalArg t v \currArgs ->
            go tvs (prevArgs ++ currArgs)

  -- Given a FFIType and a GetRet, obtain a return value and convert it to a
  -- Cryptol value. The return value is obtained differently depending on the
  -- FFIType.
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

  -- Obtain multiple return values as output arguments for a composite return
  -- type. Each return value is fully evaluated but put back in an Eval since
  -- VTuple and VRecord expect it.
  marshalMultiRet :: [FFIType] -> GetRet -> Eval [Eval (GenValue Concrete)]
  -- Since IO callbacks are involved we just do the whole thing in IO and wrap
  -- it in an Eval at the end. This should be fine since we are not changing
  -- the (Cryptol) call stack.
  marshalMultiRet types gr = Eval \stk -> do
    -- We use this IORef hack here since we are calling marshalRet recursively
    -- but marshalRet doesn't let us return any extra information from the
    -- callback through to the result of the function. So we remember the result
    -- as a side effect.
    vals <- newIORef []
    let go [] args = getRetAsOutArgs gr args
        go (t:ts) prevArgs = do
          val <- runEval stk $ marshalRet t $ getRetFromAsOutArgs \currArgs ->
            go ts (prevArgs ++ currArgs)
          modifyIORef' vals (val :)
    go types []
    map pure <$> readIORef vals

  -- Evaluate a finite numeric type expression.
  evalFinType :: Type -> Integer
  evalFinType = finNat' . evalNumType tenv

-- | Given a way to 'getRetAsOutArgs', create a 'GetRet', where the
-- 'getRetAsValue' simply allocates a temporary space to call 'getRetAsOutArgs'
-- on. This is useful for return types that we know how to obtain directly as a
-- value but need to obtain as an output argument when multiple return values
-- are involved.
getRetFromAsOutArgs :: ([SomeFFIArg] -> IO ()) -> GetRet
getRetFromAsOutArgs f = GetRet
  { getRetAsValue = alloca \ptr -> do
      f [SomeFFIArg ptr]
      peek ptr
  , getRetAsOutArgs = f }

-- | Given a 'FFIBasicType', call the callback with a marshalling function that
-- marshals values to the 'FFIArg' type corresponding to the 'FFIBasicType'.
-- The callback must be able to handle marshalling functions that marshal to any
-- 'FFIArg' type.
getMarshalBasicArg :: FFIBasicType ->
  (forall a. FFIArg a => (GenValue Concrete -> Eval a) -> b) -> b
getMarshalBasicArg (FFIWord _ s) f = withWordType s \(_ :: p t) ->
  f @t $ fmap (fromInteger . bvVal) . fromVWord Concrete "getMarshalBasicArg"
getMarshalBasicArg (FFIFloat _ _ s) f = case s of
  -- LibBF can only convert to 'Double' directly, so we do that first then
  -- convert to 'Float', which should not result in any loss of precision if
  -- the original data was 32-bit anyways.
  FFIFloat32 -> f $ pure . CFloat . double2Float . toDouble
  FFIFloat64 -> f $ pure . CDouble . toDouble
  where toDouble = fst . bfToDouble NearEven . bfValue . fromVFloat

-- | Given a 'FFIBasicType', call the callback with an unmarshalling function
-- from the 'FFIRet' type corresponding to the 'FFIBasicType' to Cryptol values.
-- The callback must be able to handle unmarshalling functions from any 'FFIRet'
-- type.
getMarshalBasicRet :: FFIBasicType ->
  (forall a. FFIRet a => (a -> Eval (GenValue Concrete)) -> b) -> b
getMarshalBasicRet (FFIWord n s) f = withWordType s \(_ :: p t) ->
  f @t $ word Concrete n . toInteger
getMarshalBasicRet (FFIFloat e p s) f = case s of
  FFIFloat32 -> f $ toValue . \case CFloat x -> float2Double x
  FFIFloat64 -> f $ toValue . \case CDouble x -> x
  where toValue = pure . VFloat . BF e p . bfFromDouble

-- | Call the callback with the Word type corresponding to the given
-- 'FFIWordSize'.
withWordType :: FFIWordSize ->
  (forall a. (FFIArg a, FFIRet a, Integral a) => Proxy a -> b) -> b
withWordType FFIWord8  f = f $ Proxy @Word8
withWordType FFIWord16 f = f $ Proxy @Word16
withWordType FFIWord32 f = f $ Proxy @Word32
withWordType FFIWord64 f = f $ Proxy @Word64

#else

-- | Dummy implementation for when FFI is disabled. Does not add anything to
-- the environment.
evalForeignDecls :: ModulePath -> Module -> EvalEnv ->
  Eval (Either [FFILoadError] EvalEnv)
evalForeignDecls _ _ env = pure $ Right env

#endif
