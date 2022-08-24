{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards #-}

module Cryptol.TypeCheck.Solver.Numeric.Sampling.Preconstraints where

import Control.Monad
import Control.Monad.Except (MonadError (throwError))
import Control.Monad.State (StateT (runStateT), evalStateT, gets, modify)
import Control.Monad.Writer (MonadWriter (tell), WriterT (runWriterT))
import Cryptol.TypeCheck.PP (PP (ppPrec), pp, pretty, text, ppList)
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Base
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Exp (Exp (..), Var (..))
import qualified Cryptol.TypeCheck.Solver.Numeric.Sampling.Exp as Exp
import Cryptol.TypeCheck.Solver.Numeric.Sampling.Q
import Cryptol.TypeCheck.TCon
import Cryptol.TypeCheck.Type
import Data.List (elemIndex)
import Data.Vector (Vector)
import qualified Data.Vector as V

-- | Preconstraints
data Preconstraints = Preconstraints
  { preprops :: [PProp],
    tparams :: Vector TParam,
    nVars :: Int
  }

instance Show Preconstraints where
  show Preconstraints{..} =
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
  deriving (Show)

data PExp
  = PEConst Q
  | PETerm Q Var
  | PEOp2 POp2 PExp PExp
  deriving (Show)

data POp2 = PAdd | PSub | PMul | PDiv | PMod | PPow
  deriving (Show)

-- | fromProps
-- Expects that all available substitions have been applied to the props.
-- Preserves order of `[TParam]`.
fromProps ::
  [TParam] ->
  [Prop] ->
  SamplingM Preconstraints
fromProps tps props = do
  pprops <- foldM fold (emptyPreconstraints $ V.fromList tps) props
  debug' 0 $ ""
  debug' 0 $ "pprops = " ++ show pprops 
  pprops <- normalizePreconstraints pprops
  debug' 0 $ "pprops <- normalizePreconstraints pprops"
  debug' 0 $ "pprops = " ++ show pprops
  pure pprops
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
          _ -> undefined -- bad
        TUser _ _ prop -> fold precons prop
        prop ->
          throwError $
            SamplingError "fromProps" $
              "cannot handle prop of the form: `" ++ show prop ++ "`"
      where
        proc2 con ts =
          toPExp `traverse` ts >>= \case
            [e1, e2] -> do
              let pprop = con e1 e2
              debug' 0 $ "fromProps.fold.proc2 (" ++ pretty prop ++ ") = (" ++ show pprop ++ ")"
              pure $ addPProps [pprop] precons
            _ -> undefined -- bad number of args
        proc1 con ts =
          toPExp `traverse` ts >>= \case
            [e] -> pure $ addPProps [con e] precons
            _ -> undefined -- bad number of args
    toPExp :: Type -> SamplingM PExp
    toPExp typ = do
      pe <- case typ of
        TCon tcon ts -> case tcon of
          -- type constants
          TC tc -> case tc of
            TCNum n -> pure . PEConst $ toQ n
            -- TCInf -> pure . PEConst $ Inf -- TODO: how to handle constant inf? need to use Q' everywhere rather than Q
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
        TVar tv -> pure $ PETerm 1 (iTVar tv)
        TUser _ _ prop -> toPExp prop
        TNewtype _new _tys -> undefined -- TODO: support user-defined newtypes
        _ -> undefined -- unsupported type function
      debug' 0 $ "fromProps.toPExp (" ++ pretty typ ++ ") = (" ++ show pe ++ ")"
      pure pe
      where
        iTVar :: TVar -> Var
        iTVar = \case
          TVFree {} -> undefined -- shouldn't be dealing with free vars here
          TVBound tparam ->
            maybe undefined Var (elemIndex tparam tps)

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
      PPEqual pe1 pe2 -> PPEqual <$> normPExp pe1 <*> normPExp pe2
      PPNeq _a _b -> do
        error "not sure how to handle Neq"
      PPGeq a b -> do
        -- a >= b ~~> a = b + c, where c is fresh
        c <- freshVar
        normPProp $ PPEqual a (PEOp2 PAdd b (PETerm 1 c))
      PPFin pe -> pure $ PPFin pe -- don't need to normalize this
    normPExp :: PExp -> WriterT [PProp] (StateT Int SamplingM) PExp
    normPExp pe =
      step pe >>= \case
        Just pe' -> normPExp pe'
        Nothing -> pure pe
      where
        -- writes the new equations generated from expanding mod
        step :: PExp -> WriterT [PProp] (StateT Int SamplingM) (Maybe PExp)
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
            let pe_ = PEOp2 po pe1' pe2'
            let abnormal = throwError . SamplingError "normPExp" $ "liteal sampling only handles linear constraints, but the following non-linear expression appeared while normalizing a constraint: " <> show pe_
            case po of
              -- a*x * b*y [abnormal]
              PMul | PETerm _ _ <- pe1', PETerm _ _ <- pe2' -> abnormal
              -- a*x / b*y [abnormal]
              PDiv | PETerm _ _ <- pe1', PETerm _ _ <- pe2' -> abnormal
              -- a*x % b*y [abnormal]
              PMod | PETerm _ _ <- pe1', PETerm _ _ <- pe2' -> abnormal
              -- a*x ^ b*y [abnormal]
              PPow | PETerm _ _ <- pe1', PETerm _ _ <- pe2' -> abnormal

              -- commutativity -- move PEConst left, move PETerm right
              PAdd | PETerm a x <- pe1', PEConst n <- pe2' -> pure . Just $ PEOp2 PAdd (PEConst n) (PETerm a x)
              PMul | PETerm a x <- pe1', PEConst n <- pe2' -> pure . Just $ PEOp2 PMul (PEConst n) (PETerm a x)
              
              -- combine constants
              PAdd | PEConst n1 <- pe1', PEConst n2 <- pe2' -> pure . Just $ PEConst (n1 + n2)
              PMul | PEConst n1 <- pe1', PEConst n2 <- pe2' -> pure . Just $ PEConst (n1 * n2)
              PDiv | PEConst n1 <- pe1', PEConst n2 <- pe2' -> pure . Just $ PEConst (n1 / n2)
              
              -- a*x + b*x = (a + b)*x
              PAdd | PETerm a x <- pe1', PETerm b y <- pe2', x == y -> pure . Just $ PETerm (a + b) x
              -- a*x * n = (a * n)*x
              PMul | PEConst n <- pe1', PETerm a x <- pe2' -> pure . Just $ PETerm (a * n) x
              
              -- `m % n` where both `m`, `n` are constant
              PMod
                | PEConst n1 <- pe1',
                  PEConst n2 <- pe2',
                  Just z1 <- (fromQ n1 :: Maybe Int),
                  Just z2 <- (fromQ n2 :: Maybe Int) ->
                    pure . Just . PEConst . toQ $ z1 `mod` z2
              
              -- `m ^^ n` requires that `m`, `n` are constant
              PPow
                | PEConst n1 <- pe1',
                  PEConst n2 <- pe2',
                  Just z2 <- (fromQ n2 :: Maybe Int) ->
                    pure . Just . PEConst $ n1 ^^ z2
              
              -- `a % n` where only `n` is constant
              PMod | PEConst n <- pe2' -> do
                -- `a % n` is replaced by `b` such that `b = a - n*c`
                -- where `b` and `c` are fresh
                let a = pe2'
                b <- freshVar
                c <- freshVar
                tell [PPEqual (PETerm 1 b) (PEOp2 PAdd a (PETerm n c))]
                pure . Just $ PETerm 1 b
              
              -- a - b ~~> a + (-b)
              PSub -> pure . Just $ PEOp2 PAdd pe1' (PEOp2 PMul (PEConst (-1)) pe2')
              
              -- normal
              _ -> pure Nothing

    freshVar :: WriterT [PProp] (StateT Int SamplingM) Var
    freshVar = do
      var <- gets Var
      modify (+ 1)
      pure var
