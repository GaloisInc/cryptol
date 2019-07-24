-- |
-- Module      :  Cryptol.Eval
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE PatternGuards #-}

module Cryptol.Eval (
    moduleEnv
  , runEval
  , EvalOpts(..)
  , PPOpts(..)
  , defaultPPOpts
  , Eval
  , EvalEnv
  , emptyEnv
  , evalExpr
  , evalDecls
  , evalSel
  , evalSetSel
  , EvalError(..)
  , forceValue
  ) where

import Cryptol.Eval.Env
import Cryptol.Eval.Monad
import Cryptol.Eval.Type
import Cryptol.Eval.Value
import Cryptol.Parser.Selector(ppSelector)
import Cryptol.ModuleSystem.Name
import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Solver.InfNat(Nat'(..))
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.PP

import           Control.Monad
import qualified Data.Sequence as Seq
import           Data.List
import           Data.Maybe
import qualified Data.Map.Strict as Map
import           Data.Semigroup

import Prelude ()
import Prelude.Compat

type EvalEnv = GenEvalEnv Bool BV Integer

-- Expression Evaluation -------------------------------------------------------

-- | Extend the given evaluation environment with all the declarations
--   contained in the given module.
moduleEnv :: EvalPrims b w i
          => Module           -- ^ Module containing declarations to evaluate
          -> GenEvalEnv b w i -- ^ Environment to extend
          -> Eval (GenEvalEnv b w i)
moduleEnv m env = evalDecls (mDecls m) =<< evalNewtypes (mNewtypes m) env

-- | Evaluate a Cryptol expression to a value.  This evaluator is parameterized
--   by the `EvalPrims` class, which defines the behavior of bits and words, in
--   addition to providing implementations for all the primitives.
evalExpr :: EvalPrims b w i
         => GenEvalEnv b w i   -- ^ Evaluation environment
         -> Expr               -- ^ Expression to evaluate
         -> Eval (GenValue b w i)
evalExpr env expr = case expr of

  -- Try to detect when the user has directly written a finite sequence of
  -- literal bit values and pack these into a word.
  EList es ty
    -- NB, even if the list cannot be packed, we must use `VWord`
    -- when the element type is `Bit`.
    | isTBit tyv -> {-# SCC "evalExpr->Elist/bit" #-}
        return $ VWord len $
          case tryFromBits vs of
            Just w  -> return $ WordVal w
            Nothing -> do xs <- mapM (delay Nothing) vs
                          return $ BitsVal $ Seq.fromList $ map (fromVBit <$>) xs
    | otherwise -> {-# SCC "evalExpr->EList" #-} do
        xs <- mapM (delay Nothing) vs
        return $ VSeq len $ finiteSeqMap xs
   where
    tyv = evalValType (envTypes env) ty
    vs  = map (evalExpr env) es
    len = genericLength es

  ETuple es -> {-# SCC "evalExpr->ETuple" #-} do
     xs <- mapM (delay Nothing . eval) es
     return $ VTuple xs

  ERec fields -> {-# SCC "evalExpr->ERec" #-} do
     xs <- sequence [ do thk <- delay Nothing (eval e)
                         return (f, thk)
                    | (f, e) <- fields
                    ]
     return $ VRecord xs

  ESel e sel -> {-# SCC "evalExpr->ESel" #-} do
     x <- eval e
     evalSel x sel

  ESet e sel v -> {-# SCC "evalExpr->ESet" #-}
    do x <- eval e
       evalSetSel x sel (eval v)

  EIf c t f -> {-# SCC "evalExpr->EIf" #-} do
     b <- fromVBit <$> eval c
     iteValue b (eval t) (eval f)

  EComp n t h gs -> {-# SCC "evalExpr->EComp" #-} do
      let len  = evalNumType (envTypes env) n
      let elty = evalValType (envTypes env) t
      evalComp env len elty h gs

  EVar n -> {-# SCC "evalExpr->EVar" #-} do
    case lookupVar n env of
      Just val -> val
      Nothing  -> do
        envdoc <- ppEnv defaultPPOpts env
        panic "[Eval] evalExpr"
                     ["var `" ++ show (pp n) ++ "` is not defined"
                     , show envdoc
                     ]

  ETAbs tv b -> {-# SCC "evalExpr->ETAbs" #-}
    case tpKind tv of
      KType -> return $ VPoly    $ \ty -> evalExpr (bindType (tpVar tv) (Right ty) env) b
      KNum  -> return $ VNumPoly $ \n  -> evalExpr (bindType (tpVar tv) (Left n) env) b
      k     -> panic "[Eval] evalExpr" ["invalid kind on type abstraction", show k]

  ETApp e ty -> {-# SCC "evalExpr->ETApp" #-} do
    eval e >>= \case
      VPoly f     -> f $! (evalValType (envTypes env) ty)
      VNumPoly f  -> f $! (evalNumType (envTypes env) ty)
      val     -> do vdoc <- ppV val
                    panic "[Eval] evalExpr"
                      ["expected a polymorphic value"
                      , show vdoc, show (pp e), show (pp ty)
                      ]

  EApp f x -> {-# SCC "evalExpr->EApp" #-} do
    eval f >>= \case
      VFun f' -> f' (eval x)
      it      -> do itdoc <- ppV it
                    panic "[Eval] evalExpr" ["not a function", show itdoc ]

  EAbs n _ty b -> {-# SCC "evalExpr->EAbs" #-}
    return $ VFun (\v -> do env' <- bindVar n v env
                            evalExpr env' b)

  -- XXX these will likely change once there is an evidence value
  EProofAbs _ e -> evalExpr env e
  EProofApp e   -> evalExpr env e

  EWhere e ds -> {-# SCC "evalExpr->EWhere" #-} do
     env' <- evalDecls ds env
     evalExpr env' e

  where

  {-# INLINE eval #-}
  eval = evalExpr env
  ppV = ppValue defaultPPOpts


-- Newtypes --------------------------------------------------------------------

evalNewtypes :: EvalPrims b w i
             => Map.Map Name Newtype
             -> GenEvalEnv b w i
             -> Eval (GenEvalEnv b w i)
evalNewtypes nts env = foldM (flip evalNewtype) env $ Map.elems nts

-- | Introduce the constructor function for a newtype.
evalNewtype :: EvalPrims b w i
            => Newtype
            -> GenEvalEnv b w i
            -> Eval (GenEvalEnv b w i)
evalNewtype nt = bindVar (ntName nt) (return (foldr tabs con (ntParams nt)))
  where
  tabs _tp body = tlam (\ _ -> body)
  con           = VFun id


-- Declarations ----------------------------------------------------------------

-- | Extend the given evaluation environment with the result of evaluating the
--   given collection of declaration groups.
evalDecls :: EvalPrims b w i
          => [DeclGroup]         -- ^ Declaration groups to evaluate
          -> GenEvalEnv b w i    -- ^ Environment to extend
          -> Eval (GenEvalEnv b w i)
evalDecls dgs env = foldM evalDeclGroup env dgs

evalDeclGroup :: EvalPrims b w i
              => GenEvalEnv b w i
              -> DeclGroup
              -> Eval (GenEvalEnv b w i)
evalDeclGroup env dg = do
  case dg of
    Recursive ds -> do
      -- declare a "hole" for each declaration
      -- and extend the evaluation environment
      holes <- mapM declHole ds
      let holeEnv = Map.fromList $ [ (nm,h) | (nm,_,h,_) <- holes ]
      let env' = env `mappend` emptyEnv{ envVars = holeEnv }

      -- evaluate the declaration bodies, building a new evaluation environment
      env'' <- foldM (evalDecl env') env ds

      -- now backfill the holes we declared earlier using the definitions
      -- calculated in the previous step
      mapM_ (fillHole env'') holes

      -- return the map containing the holes
      return env'

    NonRecursive d -> do
      evalDecl env env d


-- | This operation is used to complete the process of setting up recursive declaration
--   groups.  It 'backfills' previously-allocated thunk values with the actual evaluation
--   procedure for the body of recursive definitions.
--
--   In order to faithfully evaluate the nonstrict semantics of Cryptol, we have to take some
--   care in this process.  In particular, we need to ensure that every recursive definition
--   binding is indistinguishable from its eta-expanded form.  The straightforward solution
--   to this is to force an eta-expansion procedure on all recursive definitions.
--   However, for the so-called 'Value' types we can instead optimistically use the 'delayFill'
--   operation and only fall back on full eta expansion if the thunk is double-forced.
fillHole :: BitWord b w i
         => GenEvalEnv b w i
         -> (Name, Schema, Eval (GenValue b w i), Eval (GenValue b w i) -> Eval ())
         -> Eval ()
fillHole env (nm, sch, _, fill) = do
  case lookupVar nm env of
    Nothing -> evalPanic "fillHole" ["Recursive definition not completed", show (ppLocName nm)]
    Just x
     | isValueType env sch -> fill =<< delayFill x (etaDelay (show (ppLocName nm)) env sch x)
     | otherwise           -> fill (etaDelay (show (ppLocName nm)) env sch x)


-- | 'Value' types are non-polymorphic types recursive constructed from
--   bits, finite sequences, tuples and records.  Types of this form can
--   be implemented rather more efficently than general types because we can
--   rely on the 'delayFill' operation to build a thunk that falls back on performing
--   eta-expansion rather than doing it eagerly.
isValueType :: GenEvalEnv b w i -> Schema -> Bool
isValueType env Forall{ sVars = [], sProps = [], sType = t0 }
   = go (evalValType (envTypes env) t0)
 where
  go TVBit = True
  go (TVSeq _ x)  = go x
  go (TVTuple xs) = and (map go xs)
  go (TVRec xs)   = and (map (go . snd) xs)
  go _            = False

isValueType _ _ = False


-- | Eta-expand a word value.  This forces an unpacked word representation.
etaWord  :: BitWord b w i
         => Integer
         -> Eval (GenValue b w i)
         -> Eval (WordValue b w i)
etaWord n x = do
  w <- delay Nothing (fromWordVal "during eta-expansion" =<< x)
  return $ BitsVal $ Seq.fromFunction (fromInteger n) $ \i ->
    do w' <- w; indexWordValue w' (toInteger i)


-- | Given a simulator value and its type, fully eta-expand the value.  This
--   is a type-directed pass that always produces a canonical value of the
--   expected shape.  Eta expansion of values is sometimes necessary to ensure
--   the correct evaluation semantics of recursive definitions.  Otherwise,
--   expressions that should be expected to produce well-defined values in the
--   denotational semantics will fail to terminate instead.
etaDelay :: BitWord b w i
         => String
         -> GenEvalEnv b w i
         -> Schema
         -> Eval (GenValue b w i)
         -> Eval (GenValue b w i)
etaDelay msg env0 Forall{ sVars = vs0, sType = tp0 } = goTpVars env0 vs0
  where
  goTpVars env []     x = go (evalValType (envTypes env) tp0) x
  goTpVars env (v:vs) x =
    case tpKind v of
      KType -> return $ VPoly $ \t ->
                  goTpVars (bindType (tpVar v) (Right t) env) vs ( ($t) . fromVPoly =<< x )
      KNum  -> return $ VNumPoly $ \n ->
                  goTpVars (bindType (tpVar v) (Left n) env) vs ( ($n) . fromVNumPoly =<< x )
      k     -> panic "[Eval] etaDelay" ["invalid kind on type abstraction", show k]

  go tp (Ready x) =
    case x of
      VBit _     -> return x
      VInteger _ -> return x
      VWord _ _  -> return x
      VSeq n xs
        | TVSeq _nt el <- tp
        -> return $ VSeq n $ IndexSeqMap $ \i -> go el (lookupSeqMap xs i)

      VStream xs
        | TVStream el <- tp
        -> return $ VStream $ IndexSeqMap $ \i -> go el (lookupSeqMap xs i)

      VTuple xs
        | TVTuple ts <- tp
        -> return $ VTuple (zipWith go ts xs)

      VRecord fs
        | TVRec fts <- tp
        -> return $ VRecord $
             let err f = evalPanic "expected record value with field" [show f] in
             [ (f, go (fromMaybe (err f) (lookup f fts)) y)
             | (f, y) <- fs
             ]

      VFun f
        | TVFun _t1 t2 <- tp
        -> return $ VFun $ \a -> go t2 (f a)

      _ -> evalPanic "type mismatch during eta-expansion" []

  go tp x =
    case tp of
      TVBit -> x
      TVInteger -> x
      TVIntMod _ -> x

      TVSeq n TVBit ->
          do w <- delayFill (fromWordVal "during eta-expansion" =<< x) (etaWord n x)
             return $ VWord n w

      TVSeq n el ->
          do x' <- delay (Just msg) (fromSeq "during eta-expansion" =<< x)
             return $ VSeq n $ IndexSeqMap $ \i -> do
               go el (flip lookupSeqMap i =<< x')

      TVStream el ->
          do x' <- delay (Just msg) (fromSeq "during eta-expansion" =<< x)
             return $ VStream $ IndexSeqMap $ \i ->
               go el (flip lookupSeqMap i =<< x')

      TVFun _t1 t2 ->
          do x' <- delay (Just msg) (fromVFun <$> x)
             return $ VFun $ \a -> go t2 ( ($a) =<< x' )

      TVTuple ts ->
          do let n = length ts
             x' <- delay (Just msg) (fromVTuple <$> x)
             return $ VTuple $
                [ go t =<< (flip genericIndex i <$> x')
                | i <- [0..(n-1)]
                | t <- ts
                ]

      TVRec fs ->
          do x' <- delay (Just msg) (fromVRecord <$> x)
             let err f = evalPanic "expected record value with field" [show f]
             return $ VRecord $
                [ (f, go t =<< (fromMaybe (err f) . lookup f <$> x'))
                | (f,t) <- fs
                ]

      TVAbstract {} -> x


declHole :: Decl
         -> Eval (Name, Schema, Eval (GenValue b w i), Eval (GenValue b w i) -> Eval ())
declHole d =
  case dDefinition d of
    DPrim   -> evalPanic "Unexpected primitive declaration in recursive group"
                         [show (ppLocName nm)]
    DExpr _ -> do
      (hole, fill) <- blackhole msg
      return (nm, sch, hole, fill)
  where
  nm = dName d
  sch = dSignature d
  msg = unwords ["<<loop>> while evaluating", show (pp nm)]


-- | Evaluate a declaration, extending the evaluation environment.
--   Two input environments are given: the first is an environment
--   to use when evaluating the body of the declaration; the second
--   is the environment to extend.  There are two environments to
--   handle the subtle name-binding issues that arise from recursive
--   definitions.  The 'read only' environment is used to bring recursive
--   names into scope while we are still defining them.
evalDecl :: EvalPrims b w i
         => GenEvalEnv b w i  -- ^ A 'read only' environment for use in declaration bodies
         -> GenEvalEnv b w i  -- ^ An evaluation environment to extend with the given declaration
         -> Decl              -- ^ The declaration to evaluate
         -> Eval (GenEvalEnv b w i)
evalDecl renv env d =
  case dDefinition d of
    DPrim   -> case evalPrim d of
                 Just v  -> pure (bindVarDirect (dName d) v env)
                 Nothing -> bindVar (dName d) (cryNoPrimError (dName d)) env

    DExpr e -> bindVar (dName d) (evalExpr renv e) env


-- Selectors -------------------------------------------------------------------

-- | Apply the the given "selector" form to the given value.  This function pushes
--   tuple and record selections pointwise down into other value constructs
--   (e.g., streams and functions).
evalSel :: forall b w i
         . EvalPrims b w i
        => GenValue b w i
        -> Selector
        -> Eval (GenValue b w i)
evalSel val sel = case sel of

  TupleSel n _  -> tupleSel n val
  RecordSel n _ -> recordSel n val
  ListSel ix _  -> listSel ix val
  where

  tupleSel n v =
    case v of
      VTuple vs       -> vs !! n
      _               -> do vdoc <- ppValue defaultPPOpts v
                            evalPanic "Cryptol.Eval.evalSel"
                              [ "Unexpected value in tuple selection"
                              , show vdoc ]

  recordSel n v =
    case v of
      VRecord {}      -> lookupRecord n v
      _               -> do vdoc <- ppValue defaultPPOpts v
                            evalPanic "Cryptol.Eval.evalSel"
                              [ "Unexpected value in record selection"
                              , show vdoc ]

  listSel n v =
    case v of
      VSeq _ vs       -> lookupSeqMap vs (toInteger n)
      VStream vs      -> lookupSeqMap vs (toInteger n)
      VWord _ wv      -> VBit <$> (flip indexWordValue (toInteger n) =<< wv)
      _               -> do vdoc <- ppValue defaultPPOpts val
                            evalPanic "Cryptol.Eval.evalSel"
                              [ "Unexpected value in list selection"
                              , show vdoc ]

evalSetSel :: forall b w i. EvalPrims b w i =>
  GenValue b w i -> Selector -> Eval (GenValue b w i) -> Eval (GenValue b w i)
evalSetSel e x v =
  case x of
    TupleSel n _  -> setTuple n
    RecordSel n _ -> setRecord n
    ListSel ix _  -> setList (toInteger ix)

  where
  bad msg =
    do ed <- ppValue defaultPPOpts e
       evalPanic "Cryptol.Eval.evalSetSel"
          [ msg
          , "Selector: " ++ show (ppSelector x)
          , "Value: " ++ show ed
          ]

  setTuple n =
    case e of
      VTuple xs ->
        case splitAt n xs of
          (as, _: bs) -> pure (VTuple (as ++ v : bs))
          _ -> bad "Tuple update out of bounds."
      _ -> bad "Tuple update on a non-tuple."

  setRecord n =
    case e of
      VRecord xs ->
        case break ((n ==) . fst) xs of
          (as, (i,_) : bs) -> pure (VRecord (as ++ (i,v) : bs))
          _ -> bad "Missing field in record update."
      _ -> bad "Record update on a non-record."

  setList n =
    case e of
      VSeq i mp  -> pure $ VSeq i  $ updateSeqMap mp n v
      VStream mp -> pure $ VStream $ updateSeqMap mp n v
      VWord i m  -> pure $ VWord i $ do m1 <- m
                                        updateWordValue m1 n asBit
      _ -> bad "Sequence update on a non-sequence."

  asBit = do res <- v
             case res of
               VBit b -> pure b
               _      -> bad "Expected a bit, but got something else"

-- List Comprehension Environments ---------------------------------------------

-- | Evaluation environments for list comprehensions: Each variable
-- name is bound to a list of values, one for each element in the list
-- comprehension.
data ListEnv b w i = ListEnv
  { leVars   :: !(Map.Map Name (Integer -> Eval (GenValue b w i)))
      -- ^ Bindings whose values vary by position
  , leStatic :: !(Map.Map Name (Eval (GenValue b w i)))
      -- ^ Bindings whose values are constant
  , leTypes  :: !TypeEnv
  }

instance Semigroup (ListEnv b w i) where
  l <> r = ListEnv
    { leVars   = Map.union (leVars  l)  (leVars  r)
    , leStatic = Map.union (leStatic l) (leStatic r)
    , leTypes  = Map.union (leTypes l)  (leTypes r)
    }

instance Monoid (ListEnv b w i) where
  mempty = ListEnv
    { leVars   = Map.empty
    , leStatic = Map.empty
    , leTypes  = Map.empty
    }

  mappend l r = l <> r

toListEnv :: GenEvalEnv b w i -> ListEnv b w i
toListEnv e =
  ListEnv
  { leVars   = mempty
  , leStatic = envVars e
  , leTypes  = envTypes e
  }

-- | Evaluate a list environment at a position.
--   This choses a particular value for the varying
--   locations.
evalListEnv :: ListEnv b w i -> Integer -> GenEvalEnv b w i
evalListEnv (ListEnv vm st tm) i =
    let v = fmap ($i) vm
     in EvalEnv{ envVars = Map.union v st
               , envTypes = tm
               }

bindVarList :: Name
            -> (Integer -> Eval (GenValue b w i))
            -> ListEnv b w i
            -> ListEnv b w i
bindVarList n vs lenv = lenv { leVars = Map.insert n vs (leVars lenv) }

-- List Comprehensions ---------------------------------------------------------

-- | Evaluate a comprehension.
evalComp :: EvalPrims b w i
         => GenEvalEnv b w i -- ^ Starting evaluation environment
         -> Nat'             -- ^ Length of the comprehension
         -> TValue           -- ^ Type of the comprehension elements
         -> Expr             -- ^ Head expression of the comprehension
         -> [[Match]]        -- ^ List of parallel comprehension branches
         -> Eval (GenValue b w i)
evalComp env len elty body ms =
       do lenv <- mconcat <$> mapM (branchEnvs (toListEnv env)) ms
          mkSeq len elty <$> memoMap (IndexSeqMap $ \i -> do
              evalExpr (evalListEnv lenv i) body)

-- | Turn a list of matches into the final environments for each iteration of
-- the branch.
branchEnvs :: EvalPrims b w i
           => ListEnv b w i
           -> [Match]
           -> Eval (ListEnv b w i)
branchEnvs env matches = foldM evalMatch env matches

-- | Turn a match into the list of environments it represents.
evalMatch :: EvalPrims b w i
          => ListEnv b w i
          -> Match
          -> Eval (ListEnv b w i)
evalMatch lenv m = case m of

  -- many envs
  From n l _ty expr ->
    case len of
      -- Select from a sequence of finite length.  This causes us to 'stutter'
      -- through our previous choices `nLen` times.
      Nat nLen -> do
        vss <- memoMap $ IndexSeqMap $ \i -> evalExpr (evalListEnv lenv i) expr
        let stutter xs = \i -> xs (i `div` nLen)
        let lenv' = lenv { leVars = fmap stutter (leVars lenv) }
        let vs i = do let (q, r) = i `divMod` nLen
                      lookupSeqMap vss q >>= \case
                        VWord _ w   -> VBit <$> (flip indexWordValue r =<< w)
                        VSeq _ xs'  -> lookupSeqMap xs' r
                        VStream xs' -> lookupSeqMap xs' r
                        _           -> evalPanic "evalMatch" ["Not a list value"]
        return $ bindVarList n vs lenv'

      -- Select from a sequence of infinite length.  Note that this means we
      -- will never need to backtrack into previous branches.  Thus, we can convert
      -- `leVars` elements of the comprehension environment into `leStatic` elements
      -- by selecting out the 0th element.
      Inf -> do
        let allvars = Map.union (fmap ($0) (leVars lenv)) (leStatic lenv)
        let lenv' = lenv { leVars   = Map.empty
                         , leStatic = allvars
                         }
        let env   = EvalEnv allvars (leTypes lenv)
        xs <- evalExpr env expr
        let vs i = case xs of
                     VWord _ w   -> VBit <$> (flip indexWordValue i =<< w)
                     VSeq _ xs'  -> lookupSeqMap xs' i
                     VStream xs' -> lookupSeqMap xs' i
                     _           -> evalPanic "evalMatch" ["Not a list value"]
        return $ bindVarList n vs lenv'

    where
      len  = evalNumType (leTypes lenv) l

  -- XXX we don't currently evaluate these as though they could be recursive, as
  -- they are typechecked that way; the read environment to evalExpr is the same
  -- as the environment to bind a new name in.
  Let d -> return $ bindVarList (dName d) (\i -> f (evalListEnv lenv i)) lenv
    where
      f env =
          case dDefinition d of
            DPrim   -> evalPanic "evalMatch" ["Unexpected local primitive"]
            DExpr e -> evalExpr env e
