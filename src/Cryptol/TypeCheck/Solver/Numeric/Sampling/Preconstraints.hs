{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Cryptol.TypeCheck.Solver.Numeric.Sampling.Preconstraints where

import Control.Monad
import Control.Monad.State (MonadState (get, put), StateT (StateT, runStateT))
import Control.Monad.Writer (MonadTrans (lift), MonadWriter (tell), WriterT (WriterT, runWriterT))
import Cryptol.TypeCheck.Solver.InfNat
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Base
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Exp
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Q
import Cryptol.TypeCheck.TCon
import Cryptol.TypeCheck.Type
import Data.Maybe (fromMaybe)
import Data.Vector (Vector)
import qualified Data.Vector as V
import GHC.TypeNats

-- | Preconstraints
data Preconstraints = Preconstraints
  { preprops :: [PProp],
    -- the first ``Left tparam`s correspond to the vars intro'ed by the user,
    -- and the rest are `Right i`s which correspond to vars introduced during
    -- processing, such as expanding modulus
    tparams :: Vector (Either TParam Int) -- Var => TParam
  }

emptyPreconstraints :: Vector TParam -> Preconstraints
emptyPreconstraints tparams_ =
  Preconstraints
    { preprops = [],
      tparams = Left <$> tparams_
    }

addPProps :: [PProp] -> Preconstraints -> Preconstraints
addPProps preprops_ precons = precons {preprops = preprops_ <> preprops precons}

-- | Subset of PProps that are handled by literal sampler.
data PProp
  = PPEqual PExp PExp
  | PPNeq PExp PExp
  | PPGeq PExp PExp
  | PPFin PExp

data PExp
  = PEConst Q
  | PETerm Q PVar
  | PEOp2 POp2 PExp PExp

data PVar = PTVar TVar | PFresh Int

data POp2 = PAdd | PSub | PMul | PDiv | PMod | PPow

-- | fromProps
-- Expects that all available substitions have been applied to the props.
-- Preserves order of `[TParam]`.
fromProps ::
  forall m.
  Monad m =>
  [TParam] ->
  [Prop] ->
  SamplingM m Preconstraints
fromProps tparams_ = foldM fold (emptyPreconstraints $ V.fromList tparams_)
  where
    fold :: Preconstraints -> Prop -> SamplingM m Preconstraints
    fold precons = \case
      -- type predicates
      TCon (PC pc) ts -> case pc of
        PEqual -> proc2 PPEqual ts
        PNeq -> proc2 PPNeq ts
        PGeq -> proc2 PPGeq ts
        PFin -> proc1 PPFin ts
        PTrue -> pure precons -- trivial
        _ -> undefined -- bad
      _ -> undefined -- invalid prop since not a type predicate
      where
        proc2 con ts =
          toPExp `traverse` ts >>= \case
            [e1, e2] -> pure $ addPProps [con e1 e2] precons
            _ -> undefined -- bad number of args
        proc1 con ts =
          toPExp `traverse` ts >>= \case
            [e] -> pure $ addPProps [con e] precons
            _ -> undefined -- bad number of args

toPExp :: Monad m => Type -> SamplingM m PExp
toPExp = \case
  TCon tcon ts -> case tcon of
    -- type constants
    TC tc -> case tc of
      TCNum n -> pure . PEConst $ toRational n
      -- TCInf -> pure . PEConst $ Inf -- TODO: how to handle constant inf?
      TCAbstract _ut -> undefined -- TODO: support user-defined type constraints
      _ -> undefined -- unsupported type function
      -- type functions
    TF tf -> case tf of
      TCAdd -> proc2 (PEOp2 PAdd) ts
      TCSub -> proc2 (PEOp2 PSub) ts
      TCMul -> proc2 (PEOp2 PMul) ts
      TCDiv -> proc2 (PEOp2 PDiv) ts
      TCMod -> proc2 (PEOp2 PMod) ts
      TCExp -> proc2 (PEOp2 PPow) ts
      _ -> undefined -- unsupported type function
      where
        proc2 con = \case
          [t1, t2] -> con <$> toPExp t1 <*> toPExp t2
          _ -> undefined -- bad num of args
    _ -> undefined -- unsupported type
  TVar tv -> pure $ PETerm 1 (PTVar tv)
  TUser _na _tys _ty -> undefined -- TODO: support user-defined types
  TNewtype _new _tys -> undefined -- TODO: support user-defined newtypes
  _ -> undefined -- unsupported type function

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
normalizePreconstraints :: forall m. Monad m => Preconstraints -> SamplingM m Preconstraints
normalizePreconstraints precons = do
  -- TODO: the state's final value is the number of fresh variables introduced
  -- via `mod` and perhaps other kinds of expansions
  ((preprops', preprops''), i) <-
    flip runStateT 0 . runWriterT $
      normPProp `traverse` preprops precons
  pure precons { preprops = preprops' <> preprops'' }
  where
    normPProp :: PProp -> WriterT [PProp] (StateT Int (SamplingM m)) PProp
    normPProp = \case
      PPEqual pe1 pe2 -> PPEqual <$> normPExp pe1 <*> normPExp pe2
      PPNeq pe1 pe2 -> PPNeq <$> normPExp pe1 <*> normPExp pe2
      PPGeq pe1 pe2 -> PPGeq <$> normPExp pe1 <*> normPExp pe2
      PPFin pe -> pure $ PPFin pe -- don't need to normalize this
    normPExp :: PExp -> WriterT [PProp] (StateT Int (SamplingM m)) PExp
    normPExp pe =
      step pe >>= \case
        Just pe' -> normPExp pe'
        Nothing -> pure pe
      where
        -- writes the new equations generated from expanding mod
        step :: PExp -> WriterT [PProp] (StateT Int (SamplingM m)) (Maybe PExp)
        step = \case
          -- PEConst
          PEConst _ -> pure Nothing
          -- PETerm
          PETerm 0 _ -> pure . Just $ PEConst 0
          PETerm _ _ -> pure Nothing
          -- PEOp2
          PEOp2 po pe1 pe2 -> do
            pe1' <- normPExp pe1
            pe2' <- normPExp pe2
            case po of
              -- combine constants
              PAdd | PEConst n1 <- pe1', PEConst n2 <- pe2' -> pure . Just . PEConst $ n1 + n2
              PMul | PEConst n1 <- pe1', PEConst n2 <- pe2' -> pure . Just . PEConst $ n1 * n2
              PDiv | PEConst n1 <- pe1', PEConst n2 <- pe2' -> pure . Just . PEConst $ n1 / n2
              -- `m mod n` where both `m`, `n` are constant
              PMod
                | PEConst n1 <- pe1',
                  PEConst n2 <- pe2',
                  Just z1 <- (fromQ n1 :: Maybe Int),
                  Just z2 <- (fromQ n2 :: Maybe Int) ->
                  pure . Just . PEConst . toRational $ z1 `mod` z2
              -- `m ^^ n` requires that `m`, `n` are constant
              PPow
                | PEConst n1 <- pe1',
                  PEConst n2 <- pe2',
                  Just z2 <- (fromQ n2 :: Maybe Int) ->
                  pure . Just . PEConst . toRational $ n1 ^^ z2
              -- `a mod n` where only `n` is constant
              PMod | PEConst n <- pe2' -> do
                -- `a mod n` is replaced by `b` such that `b = a - n*c`
                -- where `b` and `c` are fresh
                let a = pe2'
                b <- freshPVar
                c <- freshPVar
                tell [PPEqual (PETerm 1 b) (PEOp2 PAdd a (PETerm n c))]
                pure . Just $ PETerm 1 b
              -- a - b ~~> a + (-b)
              PSub -> pure . Just $ PEOp2 PAdd pe1' (PEOp2 PMul (PEConst (-1)) pe2')
              -- 
              -- TODO: specify exception cases
              --
              -- only expressions that are already normalized should get here
              _ -> pure Nothing

    freshPVar :: WriterT [PProp] (StateT Int (SamplingM m)) PVar
    freshPVar = do
      i <- get
      let pv = PFresh i
      put (i + 1)
      pure pv

{-
data PProp
  = PPEqual PExp PExp
  | PPNeq PExp PExp
  | PPGeq PExp PExp
  | PPFin PExp

data PExp
  = PEConst Nat'
  | PETerm Q TVar
  | PEOp2 POp2 PExp PExp

data POp2 = PAdd | PSub | PMul | PDiv | PMod | PExp
-}