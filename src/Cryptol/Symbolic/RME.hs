{-# Language LambdaCase, GADTs, PatternSynonyms, KindSignatures, ImportQualifiedPost, BlockArguments, TypeFamilies, RankNTypes #-}
module Cryptol.Symbolic.RME (rmeAdapter) where

import Control.Monad (replicateM, ap, (<$!>))
import Data.BitVector.Sized qualified as BV
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.Parameterized.Map qualified as MapF
import Data.Parameterized.NatRepr ( NatRepr(..) )
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
rmeAdapterCheckSat _ logger asserts k =
 do logCallback logger "Starting RME"
    let m = foldl conj true <$> traverse evalExpr asserts
    let a = runM m emptyS Left (\x s -> Right (sat x, nonceCache s))
    case a of
      Left e ->
        do logCallback logger e
           k W4.Unknown
      Right (Nothing, _) -> k (W4.Unsat ())
      Right (Just model, s) ->
        let trueVars = IntSet.fromList [i | (i, True) <- model]
        in k (W4.Sat (W4.GroundEvalFn (groundEval trueVars s), Nothing))

-- | Ground evaluation function. Given a satisfying assignment (set of true variables)
-- this function will used the cached results to evaluate an expression.
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

-- | Get the current evaluation state
get :: M t (S t)
get = M (\s _ t -> t s s)

-- | Set the current evaluation state
set :: S t -> M t ()
set s = M (\_ _ t -> t () s)

-- | The state of evaluating an Expr into an RME term
data S t = S
  { nextVar :: !Int -- ^ next fresh variable to be used with RME lit
  , nonceCache :: !(MapF.MapF (Nonce.Nonce t) SomeR) -- ^ previously translated w4 expressions
  }

-- | The initial evaluation state
emptyS :: S t
emptyS = S
  { nextVar = 0
  , nonceCache = MapF.empty
  }

-- | Produce a fresh RME term
freshRME :: M t RME
freshRME =
 do s <- get
    set $! s{ nextVar = nextVar s + 1 }
    pure (lit (nextVar s))

-- | Map what4 base types to RME representations
type family R (t :: W4.BaseType) where
  R W4.BaseBoolType = RME
  R (W4.BaseBVType n) = RMEV

-- | Newtype wrapper for 'R' type for use with 'MapF'
newtype SomeR tp = SomeR (R tp)

-- | Representation type use to determine which RME representation is being used
data RMERepr (t :: W4.BaseType) where
  -- | A single RME bit
  BitRepr :: RMERepr W4.BaseBoolType
  -- | A vector of w RME bits
  BVRepr  :: !Int -> RMERepr (W4.BaseBVType w)

-- | Helper for memoizing evaluation. Given a nonced and a way to evaluation
-- action this will either return the cached value for that nonce or
-- evaluate the given action and store it in the cache before returning it.
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

-- | Converts a BV width into the Int type used by Vector.
-- In the extreme case that the NatRepr is out of range of
-- Int, this operation will fail.
evalWidth :: NatRepr w -> M t Int
evalWidth w =
  let n = natValue w in
  if n > fromIntegral (maxBound :: Int)
    then fail "RME: width to wide!"
    else pure (fromIntegral n)

evalTypeRepr :: W4.BaseTypeRepr tp -> M t (RMERepr tp)
evalTypeRepr W4.BaseBoolRepr = pure BitRepr
evalTypeRepr (W4.BaseBVRepr w) =
 do w' <- evalWidth w
    pure $! BVRepr w'
evalTypeRepr r = fail ("RME does not support " ++ show r)

-- | Evaluate an expression, if possible, into an RME term.
evalExpr :: W4.Expr t tp -> M t (R tp)
evalExpr = \case
  W4.BoolExpr x _ -> pure (constant x)
  W4.AppExpr x -> cached (W4.appExprId x) (evalApp (W4.appExprApp x))
  W4.BoundVarExpr x -> cached (W4.bvarId x) (allocateVar =<< evalTypeRepr (W4.bvarType x))
  W4.SemiRingLiteral rpr c _ ->
    case rpr of
      W4.SemiRingIntegerRepr -> fail "RME does not support integers"
      W4.SemiRingRealRepr -> fail "RME does not support real numbers"
      W4.SemiRingBVRepr _ w ->
        case c of
          BV.BV ci ->
           do w' <- evalWidth w
              pure $! integer w' ci
  W4.FloatExpr{} -> fail "RME does not support floating point numbers"
  W4.StringExpr{} -> fail "RME does not support string literals"
  W4.NonceAppExpr{} -> fail "RME does not support quantifiers"

allocateVar :: RMERepr tp -> M t (R tp)
allocateVar = \case
  BitRepr -> freshRME
  BVRepr w -> V.fromList <$> replicateM w freshRME

evalApp :: W4.App (W4.Expr t) tp -> M t (R tp)
evalApp = \case

  W4.BaseEq rpr x y ->
   do x1 <- evalExpr x
      y1 <- evalExpr y
      r <- evalTypeRepr rpr
      case r of
        BitRepr -> pure $! iff x1 y1
        BVRepr{} -> pure $! eq x1 y1

  W4.BaseIte rpr _ b t e ->
   do b1 <- evalExpr b
      t1 <- evalExpr t
      e1 <- evalExpr e
      r <- evalTypeRepr rpr
      case r of
        BitRepr -> pure $! mux b1 t1 e1
        BVRepr{} -> pure $! V.zipWith (mux b1) t1 e1

  W4.NotPred x ->
   do x1 <- evalExpr x
      pure $! compl x1

  W4.ConjPred c ->
    case W4.viewConjMap c of
      W4.ConjTrue -> pure true
      W4.ConjFalse -> pure false
      W4.Conjuncts y ->
       do let f (x, W4.Positive) = evalExpr x
              f (x, W4.Negative) = compl <$!> evalExpr x
          foldl1 conj <$!> traverse f y

  W4.BVTestBit i ve ->
   do v <- evalExpr ve
      pure $! v V.! (length v - fromIntegral i - 1)

  W4.BVSlt x y ->
   do x' <- evalExpr x
      y' <- evalExpr y
      pure $! slt x' y'

  W4.BVUlt x y ->
   do x' <- evalExpr x
      y' <- evalExpr y
      pure $! ult x' y'

  W4.BVConcat _ x y ->
   do x' <- evalExpr x
      y' <- evalExpr y
      pure $! x' <> y'

  W4.BVShl _ x y ->
    do x' <- evalExpr x
       y' <- evalExpr y
       pure $! shl x' y'

  W4.BVCountTrailingZeros _ v -> countTrailingZeros <$!> evalExpr v

  W4.BVCountLeadingZeros _ v -> countLeadingZeros <$!> evalExpr v

  W4.BVPopcount _ v -> popcount <$!> evalExpr v

  W4.BVOrBits w s ->
   do vs <- traverse evalExpr (W4.bvOrToList s)
      w' <- evalWidth w
      pure $! foldl (V.zipWith disj) (V.replicate w' false) vs

  W4.BVSelect i n v ->
   do v' <- evalExpr v
      i' <- evalWidth i
      n' <- evalWidth n
      let start = length v' - n' - i' -- i is given as a little endian index
      pure $! V.take n' (V.drop start v')

  W4.BVFill w b ->
   do b' <- evalExpr b
      w' <- evalWidth w
      pure (V.replicate w' b')

  W4.BVLshr _ x i ->
   do x' <- evalExpr x
      i' <- evalExpr i
      pure $! lshr x' i'

  W4.BVAshr _ x i ->
   do x' <- evalExpr x
      i' <- evalExpr i
      pure $! ashr x' i'

  W4.BVRol _ x i ->
   do x' <- evalExpr x
      i' <- evalExpr i
      pure $! rol x' i'

  W4.BVRor _ x i ->
   do x' <- evalExpr x
      i' <- evalExpr i
      pure $! ror x' i'

  W4.BVZext w v ->
   do v' <- evalExpr v
      w' <- evalWidth w
      let l = w' - length v'
      pure (V.replicate l false <> v')

  W4.BVSext w v ->
   do v' <- evalExpr v
      w' <- evalWidth w
      let l = w' - length v'
      pure (V.replicate l (V.head v') <> v')

  W4.SemiRingSum s ->
    case Sum.sumRepr s of

      -- modular addition
      W4.SemiRingBVRepr W4.BVArithRepr w ->
       do w' <- evalWidth w
          Sum.evalM
            (\x y -> pure $! add x y)
            (\(BV.BV c) r ->
             do v <- evalExpr r
                pure $! mul (integer w' c) v)
            (\(BV.BV c) -> pure $! integer w' c)
            s

      -- bitwise xor
      W4.SemiRingBVRepr W4.BVBitsRepr w ->
       do w' <- evalWidth w
          Sum.evalM
            (\x y -> pure $! V.zipWith xor x y)
            (\(BV.BV c) r ->
             do v <- evalExpr r
                pure $! V.zipWith conj (integer w' c) v)
            (\(BV.BV c) -> pure $! integer w' c)
            s

      _ -> fail "RME does not support this semiring representation"

  W4.SemiRingProd p ->
    case Sum.prodRepr p of

      -- arithmetic multiplication
      W4.SemiRingBVRepr W4.BVArithRepr w ->
       do w' <- evalWidth w
          mb <- Sum.prodEvalM
                 (\x y -> pure $! mul x y)
                 evalExpr
                 p
          pure $! case mb of
            Nothing ->
              if w' > 0
                then V.replicate (w' - 1) false <> V.singleton true
                else V.empty
            Just r -> r

      -- bitwise conjunction
      W4.SemiRingBVRepr W4.BVBitsRepr w ->
       do w' <- evalWidth w
          mb <- Sum.prodEvalM
                 (\x y -> pure $! V.zipWith conj x y)
                 evalExpr
                 p
          pure $! case mb of
            Nothing -> V.replicate w' true
            Just r -> r

      _ -> fail "RME does not support this semiring representation"

  e -> fail ("RME does not support: " ++ show e)
