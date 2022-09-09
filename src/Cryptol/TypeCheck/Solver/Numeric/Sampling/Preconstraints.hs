{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Cryptol.TypeCheck.Solver.Numeric.Sampling.Preconstraints where

import Control.Monad
import Control.Monad.State (StateT (runStateT), gets, modify)
import Control.Monad.Writer (MonadWriter (tell), WriterT (runWriterT))
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Base
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Exp (Var (..))
import Cryptol.TypeCheck.TCon
import Cryptol.TypeCheck.Type
import Cryptol.Utils.PP (pp, ppList, pretty)
import Cryptol.Utils.Panic (panic)
import Data.List (elemIndex)
import Data.Vector (Vector)
import qualified Data.Vector as V
import Control.Monad.Except (MonadError(throwError))

-- | Preconstraints
data Preconstraints = Preconstraints
  { preprops :: [PProp],
    tparams :: Vector TParam,
    nVars :: Int
  }

instance Show Preconstraints where
  show Preconstraints {..} =
    unlines
      [ "Preconstraints:",
        "  preprops = " ++ show preprops,
        "  tparams  = " ++ show (ppList (V.toList (pp <$> tparams))),
        "  nVars    = " ++ show nVars
      ]

emptyPreconstraints :: Vector TParam -> Preconstraints
emptyPreconstraints tps =
  Preconstraints
    { preprops = [],
      tparams = tps,
      nVars = V.length tps
    }

addPProps :: [PProp] -> Preconstraints -> Preconstraints
addPProps preprops_ precons = precons {preprops = preprops_ <> preprops precons}

-- | Subset of PProps that are handled by literal sampler.
data PProp
  = PPEqual PExp PExp
  | PPNeq PExp PExp
  | PPGeq PExp PExp
  | PPFin PExp

instance Show PProp where
  show = \case
    PPEqual pe1 pe2 -> "(" ++ show pe1 ++ " == " ++ show pe2 ++ ")"
    PPNeq pe1 pe2 -> "(" ++ show pe1 ++ " /= " ++ show pe2 ++ ")"
    PPGeq pe1 pe2 -> "(" ++ show pe1 ++ " >= " ++ show pe2 ++ ")"
    PPFin pe -> "fin " ++ show pe

data PExp
  = PEConst Rational
  | PETerm Rational Var
  | PEOp2 POp2 PExp PExp

instance Show PExp where
  show = \case
    PEConst c -> "(" ++ show c ++ ")"
    PETerm a x -> "(" ++ show a ++ ")" ++ "*" ++ show x
    PEOp2 po pe1 pe2 -> "(" ++ show pe1 ++ " " ++ show po ++ " " ++ show pe2 ++ ")"

data POp2 = PAdd | PSub | PMul | PDiv | PMod | PPow

instance Show POp2 where
  show = \case
    PAdd -> "+"
    PSub -> "-"
    PMul -> "*"
    PDiv -> "/"
    PMod -> "%"
    PPow -> "^"

-- | fromProps
-- Expects that all available substitions have been applied to the props.
-- Preserves order of `[TParam]`.
fromProps ::
  [TParam] ->
  [Prop] ->
  SamplingM Preconstraints
fromProps tps props = do
  precons <- foldM fold (emptyPreconstraints $ V.fromList tps) props
  debug' 0 $ "precons = " ++ show precons
  precons <- normalizePreconstraints precons
  debug' 0 $ "precons <- normalizePreconstraints precons"
  debug' 0 $ "precons = " ++ show precons
  pure precons
  where
    fold :: Preconstraints -> Prop -> SamplingM Preconstraints
    fold precons prop = do
      debug' 0 $ "fromProps.fold: prop = " ++ pretty prop
      case prop of
        -- type predicates
        TCon (PC pc) ts -> case pc of
          PEqual -> proc2 PPEqual ts
          PNeq -> proc2 PPNeq ts
          PGeq -> proc2 PPGeq ts
          PFin -> proc1 PPFin ts
          PTrue -> pure precons -- trivial
          _pc -> throwError $ InvalidTypeConstraints $ "The following type predicate is not supported: " <> pretty prop
        TUser _ _ prop' -> fold precons prop'
        _ -> throwError . InvalidTypeConstraints $ "The following type constraint is not supported: " ++ pretty prop
      where
        proc2 con ts =
          toPExp `traverse` ts >>= \case
            [e1, e2] -> do
              let pprop = con e1 e2
              pure $ addPProps [pprop] precons
            _ -> panic "fromProps" ["for `proc2`, bad number of args: " ++ show (pp <$> ts)]
        proc1 con ts =
          toPExp `traverse` ts >>= \case
            [e] -> pure $ addPProps [con e] precons
            _ -> panic "fromProps" ["for `proc1`, bad number of args: " ++ show (pp <$> ts)]
    toPExp :: Type -> SamplingM PExp
    toPExp typ = do
      case typ of
        TCon tcon ts -> case tcon of
          -- type constants
          TC tc -> case tc of
            TCNum n -> pure . PEConst $ toRational n
            _ -> unsupported
          -- type functions
          TF tf -> case tf of
            TCAdd -> proc2 (PEOp2 PAdd) ts
            TCSub -> proc2 (PEOp2 PSub) ts
            TCMul -> proc2 (PEOp2 PMul) ts
            TCDiv -> proc2 (PEOp2 PDiv) ts
            TCMod -> proc2 (PEOp2 PMod) ts
            TCExp -> proc2 (PEOp2 PPow) ts
            _ -> unsupported
            where
              proc2 con [t1, t2] = con <$> toPExp t1 <*> toPExp t2
              proc2 _ _ = throwError $ InternalError "toPExp" "impossible"
          _ -> unsupported
        TVar tv -> pure $ PETerm 1 (iTVar tv)
        TUser _ _ prop -> toPExp prop
        TNewtype _new _tys -> unsupported
        _ -> unsupported
      where
        unsupported = throwError . InvalidTypeConstraints $ "The following numeric type is not supported: " ++ pretty typ

        iTVar :: TVar -> Var
        iTVar = \case
          tv@TVFree {} -> panic "iTVar" ["shouldn't have a `TVFree` here: " <> pretty tv]
          TVBound tparam ->
            maybe
              (panic "iTVar" ["expected `TVBound` to be in the vector: " ++ pretty tparam])
              Var
              (elemIndex tparam tps)

{-
- Check that all `a mod n` have `n` a constant
- Check that all `m^n` have `m` and `n` constant
- Check that all `n*a` has at most one of `n`, `a` a variable
- Replace `a mod n` with `b` and add equality `b = c*n + a`, where
  `n` is a constant.
- Replace `a - b` with `a + (-b)`
- Apply distributivity
- Apply commutativity of addition to combine constant terms at the end a sum
- Apply commutativity of addition to combine terms in a sum of products
- Evaluate operations over constants
-}
normalizePreconstraints :: Preconstraints -> SamplingM Preconstraints
normalizePreconstraints precons = do
  ((preprops', preprops''), nVars) <-
    flip runStateT (nVars precons) . runWriterT $
      normPProp `traverse` preprops precons
  pure
    precons
      { preprops = preprops' <> preprops'',
        nVars = nVars
      }
  where
    normPProp :: PProp -> WriterT [PProp] (StateT Int SamplingM) PProp
    normPProp = \case
      PPEqual pe1 pe2 -> PPEqual <$> normPExp' pe1 <*> normPExp' pe2
      PPNeq _a _b -> do
        throwError $ InternalError "normPProp" "PPNeq is not yet supported"
      PPGeq a b -> do
        -- a >= b ~~> a = b + c, where c is fresh
        c <- freshVar
        normPProp $ PPEqual a (PEOp2 PAdd b (PETerm 1 c))
      PPFin pe -> pure $ PPFin pe -- don't need to normalize this
    normPExp' :: PExp -> WriterT [PProp] (StateT Int SamplingM) PExp
    normPExp' pe__ = case pe__ of
      -- PEConst
      PEConst _ -> pure pe__
      -- PETerm
      PETerm 0 _ -> pure $ PEConst 0
      PETerm _ _ -> pure pe__
      -- PEOp2
      PEOp2 po pe1 pe2 -> do
        pe1' <- normPExp' pe1
        pe2' <- normPExp' pe2
        let pe_ = PEOp2 po pe1' pe2'
        let abnormal = throwError . InvalidTypeConstraints $ "literal sampling only handles linear constraints, but the following non-linear expression appeared while normalizing a constraint: " <> show pe_
        case po of
          -- associativity (to the left)
          PMul | PEOp2 PMul pe2'A pe2'B <- pe2' -> normPExp' $ PEOp2 PMul (PEOp2 PMul pe1' pe2'A) pe2'B
          PAdd | PEOp2 PAdd pe2'A pe2'B <- pe2' -> normPExp' $ PEOp2 PAdd (PEOp2 PAdd pe1' pe2'A) pe2'B
          -- distributivity
          PMul | PEOp2 PAdd pe2'A pe2'B <- pe2' -> normPExp' $ PEOp2 PAdd (PEOp2 PMul pe1' pe2'A) (PEOp2 PMul pe1' pe2'B)
          -- a*x * b*y [abnormal]
          PMul | PETerm _ _ <- pe1', PETerm _ _ <- pe2' -> abnormal
          -- a*x / b*y [abnormal]
          PDiv | PETerm _ _ <- pe1', PETerm _ _ <- pe2' -> abnormal
          -- a*x % b*y [abnormal]
          PMod | PETerm _ _ <- pe1', PETerm _ _ <- pe2' -> abnormal
          -- a*x ^ b*y [abnormal]
          PPow | PETerm _ _ <- pe1', PETerm _ _ <- pe2' -> abnormal
          -- commutativity -- move PEConst left, move PETerm right
          PAdd | PETerm _ _ <- pe1', PEConst _ <- pe2' -> normPExp' $ PEOp2 PAdd pe2' pe1'
          PMul | PETerm _ _ <- pe1', PEConst _ <- pe2' -> normPExp' $ PEOp2 PMul pe2' pe1'
          -- combine constants
          PAdd | PEConst n1 <- pe1', PEConst n2 <- pe2' -> normPExp' $ PEConst (n1 + n2)
          PMul | PEConst n1 <- pe1', PEConst n2 <- pe2' -> normPExp' $ PEConst (n1 * n2)
          PDiv | PEConst n1 <- pe1', PEConst n2 <- pe2' -> normPExp' $ PEConst (n1 / n2)
          -- a*x + b*x = (a + b)*x
          PAdd | PETerm a x <- pe1', PETerm b y <- pe2', x == y -> normPExp' $ PETerm (a + b) x
          -- n * a*x = (a * n)*x
          PMul | PEConst n <- pe1', PETerm a x <- pe2' -> normPExp' $ PETerm (n * a) x
          -- e / n = (1/n) * e
          PDiv | PEConst 0 <- pe2' -> abnormal
          PDiv | PEConst n <- pe2' -> normPExp' $ PEOp2 PMul (PEConst (recip n)) pe1'
          -- `m % n` where both `m`, `n` are constant
          PMod
            | PEConst n1 <- pe1',
              PEConst n2 <- pe2',
              Just z1 <- fromRationalToInt n1,
              Just z2 <- fromRationalToInt n2 ->
              pure . PEConst . toRational $ z1 `mod` z2
          -- `m ^^ n` requires that `m`, `n` are constant
          PPow
            | PEConst n1 <- pe1',
              PEConst n2 <- pe2',
              Just z2 <- (fromRationalToInt n2 :: Maybe Int) ->
              pure . PEConst $ n1 ^^ z2
          -- `a % n` where only `n` is constant
          PMod | PEConst n <- pe2' -> do
            -- `a % n` is replaced by `b` such that `b = a - n*c`
            -- where `b` and `c` are fresh
            let a = pe2'
            b <- freshVar
            c <- freshVar
            let pprop = PPEqual (PETerm 1 b) (PEOp2 PAdd a (PETerm n c))
            pprop <- normPProp pprop
            tell [pprop]
            normPExp' $ PETerm 1 b

          -- a - b ~~> a + (-b)
          PSub -> normPExp' $ PEOp2 PAdd pe1' (PEOp2 PMul (PEConst (-1)) pe2')
          -- normal
          _ -> pure $ PEOp2 po pe1' pe2'

    freshVar :: WriterT [PProp] (StateT Int SamplingM) Var
    freshVar = do
      var <- gets Var
      modify (+ 1)
      pure var
