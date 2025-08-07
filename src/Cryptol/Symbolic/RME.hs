{-# Language LambdaCase, GADTs, PatternSynonyms, KindSignatures, ViewPatterns, ImportQualifiedPost, BlockArguments, GeneralisedNewtypeDeriving, TypeFamilies, RankNTypes #-}
module Cryptol.Symbolic.RME (rmeAdapter) where

import Control.Monad (replicateM, ap)
import Data.BitVector.Sized qualified as BV
import Data.Parameterized.Map qualified as MapF
import Data.Parameterized.NatRepr
import Data.Parameterized.Nonce qualified as Nonce
import Data.RME
import Data.Vector qualified as V
import What4.Expr.App qualified as W4
import What4.Expr.BoolMap qualified as W4
import What4.Expr.Builder qualified as W4
import What4.Expr.GroundEval qualified as W4
import What4.Expr.WeightedSum qualified as Sum
import What4.Interface qualified as W4
import What4.SatResult qualified as W4
import What4.SemiRing qualified as W4
import What4.Solver
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet

rmeAdapter :: SolverAdapter st
rmeAdapter =
  SolverAdapter
  { solver_adapter_name = "RME"
  , solver_adapter_config_options = []
  , solver_adapter_check_sat = rmeAdapterCheckSat
  , solver_adapter_write_smt2 = \_ _ _ -> pure ()
  }

rmeAdapterCheckSat ::
  W4.ExprBuilder t st fs ->
  LogData ->
  [W4.BoolExpr t] ->
  (SatResult (W4.GroundEvalFn t, Maybe (ExprRangeBindings t)) () -> IO a) ->
  IO a
rmeAdapterCheckSat _ _ asserts k =
 do putStrLn ("Checking " ++ show (length asserts) ++ " asserts")
    let m = foldl conj true <$> traverse toRME asserts
    let a = runM m emptyS Left (\x s -> Right (sat x, nonceCache s))
    case a of
      Left e ->
        do putStrLn e
           k W4.Unknown
      Right (Nothing, _) -> k (W4.Unsat ())
      Right (Just model, s) ->
        let trueVars = IntSet.fromList [i | (i, True) <- model]
        in k (W4.Sat (W4.GroundEvalFn (groundEval trueVars s), Nothing))

groundEval :: IntSet -> MapF.MapF (Nonce.Nonce t) SomeR -> W4.Expr t tp -> IO (W4.GroundValue tp)
groundEval trueVars nonces e =
  let t = W4.exprType e
      ev x = eval x (`IntSet.member` trueVars)
  in
  case flip MapF.lookup nonces =<< W4.exprMaybeId e of
    Just (SomeR n)
      | W4.BaseBoolRepr <- t -> pure $! ev n
      | W4.BaseBVRepr w <- t -> pure $! bitsToBV w (fmap ev n)
    _ -> W4.evalGroundExpr (groundEval trueVars nonces) e

bitsToBV :: Foldable f => NatRepr w -> f Bool -> BV.BV w
bitsToBV w bs = BV.mkBV w (foldl (\acc x -> if x then 1 + acc*2 else acc*2) 0 bs)

newtype M t a = M { runM :: forall k. S t -> (String -> k) -> (a -> S t -> k) -> k }

instance Functor (M t) where
  fmap f (M m) = M (\s e k -> m s e (k . f))

instance Applicative (M t) where
  pure x = M (\s _ k -> k x s)
  (<*>) = ap

instance Monad (M t) where
  M m1 >>= f = M (\s0 e t -> m1 s0 e (\a s1 -> runM (f a) s1 e t))

instance MonadFail (M t) where
  fail str = M (\_ e _ -> e str)

get :: M t (S t)
get = M (\s _ t -> t s s)

set :: S t -> M t ()
set s = M (\_ _ t -> t () s)

data S t = S
  { nextVar :: !Int
  , nonceCache :: !(MapF.MapF (Nonce.Nonce t) SomeR)
  }

emptyS :: S t
emptyS = S
  { nextVar = 0
  , nonceCache = MapF.empty
  }

fresh :: M t RME
fresh =
 do s <- get
    set $! s{ nextVar = nextVar s + 1 }
    pure (lit (nextVar s))

type family R (t :: W4.BaseType) where
  R W4.BaseBoolType = RME
  R (W4.BaseBVType n) = RMEV

-- | Newtype wrapper for 'R' type for use with 'MapF'
newtype SomeR tp = SomeR (R tp)

data RMERepr (t :: W4.BaseType) where
  BitRepr :: RMERepr W4.BaseBoolType
  BVRepr  :: !Int -> RMERepr (W4.BaseBVType w)

baseRepr :: W4.BaseTypeRepr tp -> M t (RMERepr tp)
baseRepr W4.BaseBoolRepr = pure BitRepr
baseRepr (W4.BaseBVRepr w) = pure $! BVRepr (fromIntegral (intValue w))
baseRepr r = fail ("RME does not support " ++ show r)

toRME :: W4.Expr t tp -> M t (R tp)
toRME = \case
  W4.BoolExpr x _ -> pure (constant x)
  W4.AppExpr x -> cached (W4.appExprId x) (appToRME (W4.appExprApp x))
  W4.BoundVarExpr x -> cached (W4.bvarId x) (varToRME =<< baseRepr (W4.bvarType x))
  W4.SemiRingLiteral rpr c _ ->
    case rpr of
      W4.SemiRingIntegerRepr -> fail "RME does not support integers"
      W4.SemiRingRealRepr -> fail "RME does not support real numbers"
      W4.SemiRingBVRepr _ w ->
        case c of
          BV.BV ci -> pure $! integer (fromIntegral (natValue w)) ci
  W4.FloatExpr{} -> fail "RME does not support floating point numbers"
  W4.StringExpr{} -> fail "RME does not support string literals"
  W4.NonceAppExpr{} -> fail "RME does not support quantifiers"

cached :: Nonce.Nonce t tp -> M t (R tp) -> M t (R tp)
cached nonce gen =
 do mb <- fmap (MapF.lookup nonce . nonceCache) get
    case mb of
      Just (SomeR r) -> pure r
      Nothing ->
       do r <- gen
          s <- get
          set s{ nonceCache = MapF.insert nonce (SomeR r) (nonceCache s) }
          pure r

varToRME :: RMERepr tp -> M t (R tp)
varToRME = \case
  BitRepr -> fresh
  BVRepr w -> V.fromList <$> replicateM w fresh

appToRME :: W4.App (W4.Expr t) tp -> M t (R tp)
appToRME = \case
  W4.BaseEq rpr x y ->
   do x1 <- toRME x
      y1 <- toRME y
      r <- baseRepr rpr
      case r of
        BitRepr -> pure $! iff x1 y1
        BVRepr{} -> pure $! eq x1 y1
  W4.BaseIte rpr _ b t e ->
   do b1 <- toRME b
      t1 <- toRME t
      e1 <- toRME e
      r <- baseRepr rpr
      case r of
        BitRepr -> pure $! mux b1 t1 e1
        BVRepr{} -> pure $! V.zipWith (mux b1) t1 e1
  W4.NotPred x ->
   do x1 <- toRME x
      pure $! compl x1
  W4.ConjPred x ->
    case W4.viewConjMap x of
      W4.ConjTrue -> pure true
      W4.ConjFalse -> pure false
      W4.Conjuncts y ->
        do xs <- traverse polRME y
           pure $! foldl1 conj xs
  W4.BVTestBit i ve ->
   do v <- toRME ve
      pure $! v V.! fromIntegral i
  W4.BVSlt x y ->
   do x' <- toRME x
      y' <- toRME y
      pure $! slt x' y'
  W4.BVUlt x y ->
   do x' <- toRME x
      y' <- toRME y
      pure $! ult x' y'
  W4.BVConcat _ x y ->
   do x' <- toRME x
      y' <- toRME y
      pure $! x' <> y'
  W4.BVShl _ x y ->
    do x' <- toRME x
       y' <- toRME y
       pure $! shl x' y'
  W4.BVCountTrailingZeros _ v ->
   do v1 <- toRME v
      pure $! countTrailingZeros v1
  W4.BVCountLeadingZeros _ v ->
   do v1 <- toRME v
      pure $! countLeadingZeros v1

  W4.BVOrBits{} -> fail "or not implemented"
  W4.BVUnaryTerm{} -> fail "unary term not implemented"
  W4.BVSelect{} -> fail "bvselect not implemented"
  W4.BVFill{} -> fail "bvfill not implemented"
  W4.BVLshr{} -> fail "LShr not implemented"
  W4.BVAshr{} -> fail "AShr not implemented"
  W4.BVRol{} -> fail "rol not implemented"
  W4.BVRor{} -> fail "ror not implemented"
  W4.BVZext{} -> fail "zext not implemented"
  W4.BVSext{} -> fail "zext not implemented"
  W4.BVPopcount{} -> fail "popcount not implemented"
  W4.IntegerToBV{} -> fail "integer to bv not implemented"
  W4.SemiRingSum s ->
    case Sum.sumRepr s of
      W4.SemiRingBVRepr W4.BVArithRepr w ->
        Sum.evalM
          (\x y -> pure (add x y))
          (\(BV.BV c) r ->
           do v <- toRME r
              pure (mul (integer (fromIntegral (natValue w)) c) v))
          (\(BV.BV c) -> pure (integer (fromIntegral (natValue w)) c))
          s
      W4.SemiRingBVRepr W4.BVBitsRepr w ->
        Sum.evalM
          (\x y -> pure (V.zipWith xor x y))
          (\(BV.BV c) r ->
           do v <- toRME r
              pure (V.zipWith conj (integer (fromIntegral (natValue w)) c) v))
          (\(BV.BV c) -> pure (integer (fromIntegral (natValue w)) c))
          s
      _ -> fail "Unsupported semiring add type"
  W4.SemiRingProd {} -> fail "semiring prod not implemented"
  W4.SemiRingLe {} -> fail "semiring le not implemented"
  e -> fail ("app not implemented: " ++ show e)

polRME :: (W4.BoolExpr t, W4.Polarity) -> M t RME
polRME (x, W4.Positive) = toRME x
polRME (x, W4.Negative) =
 do x1 <- toRME x
    pure $! compl x1
