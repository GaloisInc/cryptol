-- |
-- Module      :  Cryptol.Backend.Monad
-- Copyright   :  (c) 2013-2020 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Cryptol.Backend.Monad
( -- * Evaluation monad
  Eval(..)
, runEval
, io
, delayFill
, ready
, blackhole
, evalSpark
, maybeReady
  -- * Call stacks
, CallStack
, getCallStack
, withCallStack
, modifyCallStack
, combineCallStacks
, pushCallFrame
, displayCallStack
  -- * Error reporting
, Unsupported(..)
, EvalError(..)
, EvalErrorEx(..)
, ImportErrorMessage(..)
, ImportThing(..)
, evalPanic
, wordTooWide
, WordTooWide(..)
) where

import           Data.Text(Text)
import           Control.Concurrent
import           Control.Concurrent.STM

import           Control.Monad
import           Control.Monad.IO.Class
import           Data.Foldable (toList)
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Typeable (Typeable)
import qualified Control.Exception as X


import Cryptol.Parser.Position
import Cryptol.Utils.Panic
import Cryptol.Utils.PP
import Cryptol.TypeCheck.AST(Name, TParam)

-- | A computation that returns an already-evaluated value.
ready :: a -> Eval a
ready a = Ready a


-- | The type of dynamic call stacks for the interpreter.
--   New frames are pushed onto the right side of the sequence.
data CallStack
  = EmptyCallStack
  | CombineCallStacks !CallStack !CallStack
  | PushCallFrame !Name !Range !CallStack

instance Semigroup CallStack where
  (<>) = CombineCallStacks

instance Monoid CallStack where
  mempty = EmptyCallStack

type CallStack' = Seq (Name, Range)

evalCallStack :: CallStack -> CallStack'
evalCallStack stk =
  case stk of
    EmptyCallStack -> mempty
    CombineCallStacks appstk fnstk -> combineCallStacks' (evalCallStack appstk) (evalCallStack fnstk)
    PushCallFrame n r stk1 -> pushCallFrame' n r (evalCallStack stk1)

-- | Pretty print a call stack with each call frame on a separate
--   line, with most recent call frames at the top.
displayCallStack :: CallStack -> Doc
displayCallStack = displayCallStack' . evalCallStack

displayCallStack' :: CallStack' -> Doc
displayCallStack' = vcat . map f . toList . Seq.reverse
  where
  f (nm,rng)
    | rng == emptyRange = pp nm
    | otherwise = pp nm <+> text "called at" <+> pp rng


-- | Combine the call stack of a function value with the call
--   stack of the current calling context.  This algorithm is
--   the same one GHC uses to compute profiling calling contexts.
--
--   The algorithm is as follows.
--
--        ccs ++> ccsfn  =  ccs ++ dropCommonPrefix ccs ccsfn
--
--      where
--
--        dropCommonPrefix A B
--           -- returns the suffix of B after removing any prefix common
--           -- to both A and B.
combineCallStacks ::
  CallStack {- ^ call stack of the application context -} ->
  CallStack {- ^ call stack of the function being applied -} ->
  CallStack
combineCallStacks appstk EmptyCallStack = appstk
combineCallStacks EmptyCallStack fnstk = fnstk
combineCallStacks appstk fnstk = CombineCallStacks appstk fnstk

combineCallStacks' ::
  CallStack' {- ^ call stack of the application context -} ->
  CallStack' {- ^ call stack of the function being applied -} ->
  CallStack'
combineCallStacks' appstk fnstk = appstk <> dropCommonPrefix appstk fnstk
  where
  dropCommonPrefix _  Seq.Empty = Seq.Empty
  dropCommonPrefix Seq.Empty fs = fs
  dropCommonPrefix (a Seq.:<| as) xs@(f Seq.:<| fs)
    | a == f    = dropCommonPrefix as fs
    | otherwise = xs

-- | Add a call frame to the top of a call stack
pushCallFrame :: Name -> Range -> CallStack -> CallStack
pushCallFrame nm rng stk = PushCallFrame nm rng stk

pushCallFrame' :: Name -> Range -> CallStack' -> CallStack'
pushCallFrame' nm rng stk@( _ Seq.:|> (nm',rng'))
  | nm == nm', rng == rng' = stk
pushCallFrame' nm rng stk = stk Seq.:|> (nm,rng)


-- | The monad for Cryptol evaluation.
--   A computation is either "ready", which means it represents
--   only trivial computation, or is an "eval" action which must
--   be computed to get the answer, or it is a "thunk", which
--   represents a delayed, shared computation.
data Eval a
   = Ready !a
   | Eval !(CallStack -> IO a)
   | Thunk !(TVar (ThunkState a))

-- | This datastructure tracks the lifecycle of a thunk.
--
--   Thunks are used for basically three use cases.  First,
--   we use thunks to preserve sharing.  Basically every
--   cryptol expression that is bound to a name, and is not
--   already obviously a value (and in a few other places as
--   well) will get turned into a thunk in order to avoid
--   recomputation.  These thunks will start in the `Unforced`
--   state, and have a backup computation that just raises
--   the `LoopError` exception.
--
--   Secondly, thunks are used to cut cycles when evaluating
--   recursive definition groups.  Every named clause in a
--   recursive definition is thunked so that the value can appear
--   in its definition.  Such thunks start in the `Void` state,
--   as they must exist before we have a definition to assign them.
--   Forcing a thunk in the `Void` state is a programmer error (panic).
--   Once the body of a definition is ready, we replace the
--   thunk with the relevant computation, going to the `Unforced` state.
--
--   In the third case, we are using thunks to provide an optimistic
--   shortcut for evaluation.  In these cases we first try to run a
--   computation that is stricter than the semantics actually allows.
--   If it succeeds, all is well an we continue.  However, if it tight
--   loops, we fall back on a lazier (and generally more expensive)
--   version, which is the "backup" computation referred to above.
data ThunkState a
  = Void !String
       -- ^ This thunk has not yet been initialized
  | Unforced !(IO a) !(Maybe (IO a)) !String !CallStack
       -- ^ This thunk has not yet been forced.  We keep track of the "main"
       --   computation to run and an optional "backup" computation to run if we
       --   detect a tight loop when evaluating the first one.
       --   The final two arguments are used to throw a loop exception
       --   if the backup computation also causes a tight loop.
  | UnderEvaluation !ThreadId !(Maybe (IO a)) !String !CallStack
       -- ^ This thunk is currently being evaluated by the thread with the given
       --   thread ID.  We track an optional "backup" computation to run if we detect
       --   a tight loop evaluating this thunk.  If the thunk is being evaluated
       --   by some other thread, the current thread will await its completion.
       --   The final two arguments are used to throw a loop exception
       --   if the backup computation also causes a tight loop.
  | ForcedErr !EvalErrorEx
       -- ^ This thunk has been forced, and its evaluation results in an exception
  | Forced !a
       -- ^ This thunk has been forced to the given value


-- | Test if a value is "ready", which means that
--   it requires no computation to return.
maybeReady :: Eval a -> Eval (Maybe a)
maybeReady (Ready a) = pure (Just a)
maybeReady (Thunk tv) = Eval $ \_ ->
  readTVarIO tv >>= \case
     Forced a -> pure (Just a)
     _ -> pure Nothing
maybeReady (Eval _) = pure Nothing


{-# INLINE delayFill #-}

-- | Delay the given evaluation computation, returning a thunk
--   which will run the computation when forced.  Run the 'retry'
--   computation instead if the resulting thunk is forced during
--   its own evaluation.
delayFill ::
  Eval a {- ^ Computation to delay -} ->
  Maybe (Eval a) {- ^ Optional backup computation to run if a tight loop is detected -} ->
  String {- ^ message for the <<loop>> exception if a tight loop is detected -} ->
  Eval (Eval a)
delayFill e@(Ready _) _ _ = return e
delayFill e@(Thunk _) _ _ = return e
delayFill (Eval x) backup msg =
  Eval (\stk -> Thunk <$> newTVarIO (Unforced (x stk) (runEval stk <$> backup) msg stk))

-- | Begin executing the given operation in a separate thread,
--   returning a thunk which will await the completion of
--   the computation when forced.
evalSpark ::
  Eval a ->
  Eval (Eval a)

-- Ready computations need no additional evaluation.
evalSpark e@(Ready _) = return e

-- A thunked computation might already have
-- been forced.  If so, return the result.  Otherwise,
-- fork a thread to force this computation and return
-- the thunk.
evalSpark (Thunk tv)  = Eval $ \_stk ->
  readTVarIO tv >>= \case
    Forced x     -> return (Ready x)
    ForcedErr ex -> return (Eval $ \_ -> (X.throwIO ex))
    _ ->
       do _ <- forkIO (sparkThunk tv)
          return (Thunk tv)

-- If the computation is nontrivial but not already a thunk,
-- create a thunk and fork a thread to force it.
evalSpark (Eval x) = Eval $ \stk ->
  do tv <- newTVarIO (Unforced (x stk) Nothing "" stk)
     _ <- forkIO (sparkThunk tv)
     return (Thunk tv)


-- | To the work of forcing a thunk. This is the worker computation
--   that is forked off via @evalSpark@.
sparkThunk :: TVar (ThunkState a) -> IO ()
sparkThunk tv =
  do tid <- myThreadId
     -- Try to claim the thunk.  If it is still in the @Void@ state, wait
     -- until it is in some other state.  If it is @Unforced@ claim the thunk.
     -- Otherwise, it is already evaluated or under evaluation by another thread,
     -- and we have no work to do.
     st <- atomically $
              do st <- readTVar tv
                 case st of
                   Void _ -> retry
                   Unforced _ backup msg stk -> writeTVar tv (UnderEvaluation tid backup msg stk)
                   _ -> return ()
                 return st
     -- If we successfully claimed the thunk to work on, run the computation and
     -- update the thunk state with the result.
     case st of
       Unforced work _ _ _ ->
         X.try work >>= \case
           Left err -> atomically (writeTVar tv (ForcedErr err))
           Right a  -> atomically (writeTVar tv (Forced a))
       _ -> return ()


-- | Produce a thunk value which can be filled with its associated computation
--   after the fact.  A preallocated thunk is returned, along with an operation to
--   fill the thunk with the associated computation.
--   This is used to implement recursive declaration groups.
blackhole ::
  String {- ^ A name to associate with this thunk. -} ->
  Eval (Eval a, Eval a -> Eval ())
blackhole msg = Eval $ \stk ->
  do tv <- newTVarIO (Void msg)
     let set (Ready x)  = io $ atomically (writeTVar tv (Forced x))
         set m          = io $ atomically (writeTVar tv (Unforced (runEval stk m) Nothing msg stk))
     return (Thunk tv, set)

-- | Force a thunk to get the result.
unDelay :: TVar (ThunkState a) -> IO a
unDelay tv =
  -- First, check if the thunk is in an evaluated state,
  -- and return the value if so.
  readTVarIO tv >>= \case
    Forced x -> pure x
    ForcedErr e -> X.throwIO e
    _ ->
      -- Otherwise, try to claim the thunk to work on.
      do tid <- myThreadId
         res <- atomically $ do
                  res <- readTVar tv
                  case res of
                    -- In this case, we claim the thunk.  Update the state to indicate
                    -- that we are working on it.
                    Unforced _ backup msg stk -> writeTVar tv (UnderEvaluation tid backup msg stk)

                    -- In this case, the thunk is already being evaluated.  If it is
                    -- under evaluation by this thread, we have to run the backup computation,
                    -- and "consume" it by updating the backup computation to one that throws
                    -- a loop error.  If some other thread is evaluating, reset the
                    -- transaction to await completion of the thunk.
                    UnderEvaluation t backup msg stk
                      | tid == t  ->
                          case backup of
                            Just _  -> writeTVar tv (UnderEvaluation tid Nothing msg stk)
                            Nothing -> writeTVar tv (ForcedErr (EvalErrorEx stk (LoopError msg)))
                      | otherwise -> retry -- wait, if some other thread is evaluating
                    _ -> return ()

                  -- Return the original thunk state so we can decide what work to do
                  -- after the transaction completes.
                  return res

         -- helper for actually doing the work
         let doWork work =
               X.try work >>= \case
                 Left ex -> do atomically (writeTVar tv (ForcedErr ex))
                               X.throwIO ex
                 Right a -> do atomically (writeTVar tv (Forced a))
                               return a

         -- Now, examine the thunk state and decide what to do.
         case res of
           Void msg -> evalPanic "unDelay" ["Thunk forced before it was initialized", msg]
           Forced x -> pure x
           ForcedErr e -> X.throwIO e
           -- this thread was already evaluating this thunk
           UnderEvaluation _ (Just backup) _ _ -> doWork backup
           UnderEvaluation _ Nothing msg stk -> X.throwIO (EvalErrorEx stk (LoopError msg))
           Unforced work _ _ _ -> doWork work

-- | Get the current call stack
getCallStack :: Eval CallStack
getCallStack = Eval (\stk -> pure stk)

-- | Execute the action with the given call stack
withCallStack :: CallStack -> Eval a -> Eval a
withCallStack stk m = Eval (\_ -> runEval stk m)

-- | Run the given action with a modify call stack
modifyCallStack :: (CallStack -> CallStack) -> Eval a -> Eval a
modifyCallStack f m =
  Eval $ \stk ->
    do let stk' = f stk
       -- putStrLn $ unwords ["Pushing call stack", show (displayCallStack stk')]
       seq stk' (runEval stk' m)
{-# INLINE modifyCallStack #-}

-- | Execute the given evaluation action.
runEval :: CallStack -> Eval a -> IO a
runEval _   (Ready a)  = return a
runEval stk (Eval x)   = x stk
runEval _   (Thunk tv) = unDelay tv
{-# INLINE runEval #-}

{-# INLINE evalBind #-}
evalBind :: Eval a -> (a -> Eval b) -> Eval b
evalBind (Ready a) f  = f a
evalBind (Eval x)  f  = Eval (\stk -> x stk >>= runEval stk . f)
evalBind (Thunk x) f  = Eval (\stk -> unDelay x >>= runEval stk . f)

instance Functor Eval where
  fmap f (Ready x)   = Ready (f x)
  fmap f (Eval m)    = Eval (\stk -> f <$> m stk)
  fmap f (Thunk tv)  = Eval (\_   -> f <$> unDelay tv)
  {-# INLINE fmap #-}

instance Applicative Eval where
  pure  = Ready
  (<*>) = ap
  {-# INLINE pure #-}
  {-# INLINE (<*>) #-}

instance Monad Eval where
  return = pure
  (>>=)  = evalBind
  {-# INLINE return #-}
  {-# INLINE (>>=) #-}

instance MonadIO Eval where
  liftIO = io

-- | Lift an 'IO' computation into the 'Eval' monad.
io :: IO a -> Eval a
io m = Eval (\_stk -> m)
{-# INLINE io #-}


-- Errors ----------------------------------------------------------------------

-- | Panic from an @Eval@ context.
evalPanic :: HasCallStack => String -> [String] -> a
evalPanic cxt = panic ("[Eval] " ++ cxt)


-- | Data type describing errors that can occur during evaluation.
data EvalError
  = InvalidIndex (Maybe Integer)         -- ^ Out-of-bounds index
  | DivideByZero                         -- ^ Division or modulus by 0
  | NegativeExponent                     -- ^ Exponentiation by negative integer
  | LogNegative                          -- ^ Logarithm of a negative integer
  | UserError String                     -- ^ Call to the Cryptol @error@ primitive
  | LoopError String                     -- ^ Detectable nontermination
  | NoPrim Name                          -- ^ Primitive with no implementation
  | BadRoundingMode Integer              -- ^ Invalid rounding mode
  | BadValue String                      -- ^ Value outside the domain of a partial function.
  | NoMatchingPropGuardCase String    -- ^ No prop guard holds for the given type variables.
  | NoMatchingConstructor (Maybe String) -- ^ Missing `case` alternative
  | FFINotSupported Name                 -- ^ Foreign function cannot be called
  | FFITypeNumTooBig Name TParam Integer -- ^ Number passed to foreign function
                                         --   as a type argument is too large
  | FFIImportError ImportErrorMessage    -- ^ a problem with the result of an FFI call
  deriving Typeable

data ImportErrorMessage =
    ProtocolMismatch ImportThing ImportThing  -- ^ Expected, got
  | PartialValue
  | UnexpectedData
  | TagOutOfBounds Int
  | Unsupported Text
  | BadWordValue
  | BadRationalValue
  | FFINotEnabled
    deriving Typeable

data ImportThing = AValue | ATag | ASign
  deriving Typeable




instance PP EvalError where
  ppPrec _ e = case e of
    InvalidIndex (Just i) -> text "invalid sequence index:" <+> integer i
    InvalidIndex Nothing  -> text "invalid sequence index"
    DivideByZero -> text "division by 0"
    NegativeExponent -> text "negative exponent"
    LogNegative -> text "logarithm of negative"
    UserError x -> text "Run-time error:" <+> text x
    LoopError x -> vcat [ text "<<loop>>" <+> text x
                        , text "This usually occurs due to an improper recursive definition,"
                        , text "but may also result from retrying a previously interrupted"
                        , text "computation (e.g., after CTRL^C). In that case, you may need to"
                        , text "`:reload` the current module to reset to a good state."
                        ]
    BadRoundingMode r -> "invalid rounding mode" <+> integer r
    BadValue x -> "invalid input for" <+> backticks (text x)
    NoPrim x -> text "unimplemented primitive:" <+> pp x
    NoMatchingPropGuardCase msg -> text $ "No matching constraint guard; " ++ msg
    FFINotSupported x -> vcat
      [ text "cannot call foreign function" <+> pp x
      , text "No foreign implementation is loaded,"
      , text "  or FFI calls are not supported in this context."
      ]
    FFITypeNumTooBig f p n -> vcat
      [ text "numeric type argument to foreign function is too large:"
        <+> integer n
      , text "in type parameter" <+> pp p <+> "of function" <+> pp f
      , text "type arguments must fit in a C `size_t`" ]
    NoMatchingConstructor mbCon -> vcat
      [ "Missing `case` alternative" <+> con <.> "."
      ]
      where con = case mbCon of
                    Just c -> "for constructor" <+> backticks (text c)
                    Nothing -> mempty
    FFIImportError msg -> pp msg

instance PP ImportErrorMessage where
  ppPrec _ e =
    case e of
      ProtocolMismatch a b -> vcat
         [ "Value mismatch:"
         , " * Expected:" <+> pp a
         , " * Got:" <+> pp b
         ]
      PartialValue -> "Partial value"
      UnexpectedData -> "Unexpected data"
      TagOutOfBounds n -> "Tag out of bounds:" <+> int n
      Unsupported n -> "Unsupported" <+> pp n
      BadWordValue -> "Bad word value"
      BadRationalValue -> "Bad rational value"
      FFINotEnabled -> "FFI is not enabled"

instance PP ImportThing where
  ppPrec _ e =
    case e of
      AValue -> "a value"
      ATag -> "a tag"
      ASign -> "a sign"
      



instance Show EvalError where
  show = show . pp

data EvalErrorEx =
  EvalErrorEx CallStack EvalError
 deriving Typeable

instance PP EvalErrorEx where
  ppPrec _ (EvalErrorEx stk0 ex) = vcat ([ pp ex ] ++ callStk)

   where
    stk = evalCallStack stk0
    callStk | Seq.null stk = []
            | otherwise = [ text "-- Backtrace --", displayCallStack' stk ]

instance Show EvalErrorEx where
  show = show . pp

instance X.Exception EvalErrorEx

data Unsupported
  = UnsupportedSymbolicOp String  -- ^ Operation cannot be supported in the symbolic simulator
    deriving (Typeable,Show)

instance PP Unsupported where
  ppPrec _ e = case e of
    UnsupportedSymbolicOp nm -> text "operation can not be supported on symbolic values:" <+> text nm

instance X.Exception Unsupported

-- | For when we know that a word is too wide and will exceed gmp's
-- limits (though words approaching this size will probably cause the
-- system to crash anyway due to lack of memory).
wordTooWide :: Integer -> a
wordTooWide w = X.throw (WordTooWide w)

data WordTooWide = WordTooWide Integer -- ^ Bitvector too large
 deriving Typeable

instance PP WordTooWide where
  ppPrec _ (WordTooWide w) =
      text "word too wide for memory:" <+> integer w <+> text "bits"

instance Show WordTooWide where
  show = show . pp

instance X.Exception WordTooWide
