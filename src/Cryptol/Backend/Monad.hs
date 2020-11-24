-- |
-- Module      :  Cryptol.Eval.Monad
-- Copyright   :  (c) 2013-2016 Galois, Inc.
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
, EvalOpts(..)
, PPOpts(..)
, asciiMode
, PPFloatFormat(..)
, PPFloatExp(..)
, defaultPPOpts
, io
, delayFill
, ready
, blackhole
, evalSpark
, maybeReady
  -- * Error reporting
, Unsupported(..)
, EvalError(..)
, EvalErrorEx(..)
, evalPanic
, wordTooWide
, WordTooWide(..)
) where

import           Control.Concurrent
import           Control.Concurrent.STM

import           Control.Monad
import qualified Control.Monad.Fail as Fail
import           Control.Monad.Fix
import           Control.Monad.IO.Class
import           Data.Typeable (Typeable)
import qualified Control.Exception as X


import Cryptol.Parser.Position
import Cryptol.Utils.Panic
import Cryptol.Utils.PP
import Cryptol.Utils.Logger(Logger)
import Cryptol.TypeCheck.AST(Name)

-- | A computation that returns an already-evaluated value.
ready :: a -> Eval a
ready a = Ready a

-- | How to pretty print things when evaluating
data PPOpts = PPOpts
  { useAscii     :: Bool
  , useBase      :: Int
  , useInfLength :: Int
  , useFPBase    :: Int
  , useFPFormat  :: PPFloatFormat
  }

asciiMode :: PPOpts -> Integer -> Bool
asciiMode opts width = useAscii opts && (width == 7 || width == 8)

data PPFloatFormat =
    FloatFixed Int PPFloatExp -- ^ Use this many significant digis
  | FloatFrac Int             -- ^ Show this many digits after floating point
  | FloatFree PPFloatExp      -- ^ Use the correct number of digits

data PPFloatExp = ForceExponent -- ^ Always show an exponent
                | AutoExponent  -- ^ Only show exponent when needed


defaultPPOpts :: PPOpts
defaultPPOpts = PPOpts { useAscii = False, useBase = 10, useInfLength = 5
                       , useFPBase = 16
                       , useFPFormat = FloatFree AutoExponent
                       }


-- | Some options for evalutaion
data EvalOpts = EvalOpts
  { evalLogger :: Logger    -- ^ Where to print stuff (e.g., for @trace@)
  , evalPPOpts :: PPOpts    -- ^ How to pretty print things.
  }

-- | The monad for Cryptol evaluation.
--   A computation is either "ready", which means it represents
--   only trivial computation, or is an "eval" action which must
--   be computed to get the answer, or it is a "thunk", which
--   represents a delayed, shared computation.
data Eval a
   = Ready !a
   | Eval !(IO a)
   | Thunk !(TVar (ThunkState a))

-- | This datastructure tracks the lifecycle of a thunk.
--
--   Thunks are used for basically three use cases.  First,
--   we use thunks to preserve sharing.  Basically every
--   cryptol expression that is bound to a name, and is not
--   already obviously a value (and in a few other places as
--   well) will get turned into a thunk in order to avoid
--   recomputations.  These thunks will start in the `Unforced`
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
  | Unforced !(IO a) !(IO a)
       -- ^ This thunk has not yet been forced.  We keep track of the "main"
       --   computation to run and a "backup" computation to run if we
       --   detect a tight loop when evaluating the first one.
  | UnderEvaluation !ThreadId !(IO a)
       -- ^ This thunk is currently being evaluated by the thread with the given
       --   thread ID.  We track the "backup" computation to run if we detect
       --   a tight loop evaluating this thunk.  If the thunk is being evaluated
       --   by some other thread, the current thread will await its completion.
  | ForcedErr !EvalErrorEx
       -- ^ This thunk has been forced, and its evaluation results in an exception
  | Forced !a
       -- ^ This thunk has been forced to the given value


-- | Test if a value is "ready", which means that
--   it requires no computation to return.
maybeReady :: Eval a -> Eval (Maybe a)
maybeReady (Ready a) = pure (Just a)
maybeReady (Thunk tv) = Eval $
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
  Eval a {- ^ Backup computation to run if a tight loop is detected -} ->
  Eval (Eval a)
delayFill e@(Ready _) _  = return e
delayFill e@(Thunk _) _  = return e
delayFill (Eval x) backup = Eval (Thunk <$> newTVarIO (Unforced x (runEval backup)))

-- | Begin executing the given operation in a separate thread,
--   returning a thunk which will await the completion of
--   the computation when forced.
evalSpark ::
  Range ->
  Eval a ->
  Eval (Eval a)

-- Ready computations need no additional evaluation.
evalSpark _ e@(Ready _) = return e

-- A thunked computation might already have
-- been forced.  If so, return the result.  Otherwise,
-- fork a thread to force this computation and return
-- the thunk.
evalSpark _ (Thunk tv)  = Eval $
  readTVarIO tv >>= \case
    Forced x     -> return (Ready x)
    ForcedErr ex -> return (Eval (X.throwIO ex))
    _ ->
       do _ <- forkIO (sparkThunk tv)
          return (Thunk tv)

-- If the computation is nontrivial but not already a thunk,
-- create a thunk and fork a thread to force it.
evalSpark rng (Eval x) = Eval $
  do tv <- newTVarIO (Unforced x (X.throwIO (EvalErrorEx rng (LoopError ""))))
     _ <- forkIO (sparkThunk tv)
     return (Thunk tv)


-- | To the work of forcing a thunk. This is the worker computation
--   that is foked off via @evalSpark@.
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
                   Unforced _ backup -> writeTVar tv (UnderEvaluation tid backup)
                   _ -> return ()
                 return st
     -- If we successfully claimed the thunk to work on, run the computation and
     -- update the thunk state with the result.
     case st of
       Unforced work _ ->
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
  Range ->
  Eval (Eval a, Eval a -> Eval ())
blackhole msg rng = Eval $
  do tv <- newTVarIO (Void msg)
     let ex = EvalErrorEx rng (LoopError msg)
     let set (Ready x)  = io $ atomically (writeTVar tv (Forced x))
         set m          = io $ atomically (writeTVar tv (Unforced (runEval m) (X.throwIO ex)))
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
                    Unforced _ backup -> writeTVar tv (UnderEvaluation tid backup)

                    -- In this case, the thunk is already being evaluated.  If it is
                    -- under evaluation by this thread, we have to run the backup computation,
                    -- and "consume" it by updating the backup computation to one that throws
                    -- a loop error.  If some other thread is evaluating, reset the
                    -- transaction to await completion of the thunk.
                    UnderEvaluation t _
                      | tid == t  -> writeTVar tv (UnderEvaluation tid (X.throwIO (EvalErrorEx emptyRange (LoopError "")))) -- TODO? better range info
                      | otherwise -> retry -- wait, if some other thread is evaualting
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
           UnderEvaluation _ backup -> doWork backup -- this thread was already evaluating this thunk
           Unforced work _ -> doWork work

-- | Execute the given evaluation action.
runEval :: Eval a -> IO a
runEval (Ready a)  = return a
runEval (Eval x)   = x
runEval (Thunk tv) = unDelay tv

{-# INLINE evalBind #-}
evalBind :: Eval a -> (a -> Eval b) -> Eval b
evalBind (Ready a) f  = f a
evalBind (Eval x) f   = Eval (x >>= runEval . f)
evalBind (Thunk x) f  = Eval (unDelay x >>= runEval . f)

instance Functor Eval where
  fmap f (Ready x)   = Ready (f x)
  fmap f (Eval m)    = Eval (f <$> m)
  fmap f (Thunk tv)  = Eval (f <$> unDelay tv)
  {-# INLINE fmap #-}

instance Applicative Eval where
  pure  = return
  (<*>) = ap
  {-# INLINE pure #-}
  {-# INLINE (<*>) #-}

instance Monad Eval where
  return = Ready
  (>>=)  = evalBind
  {-# INLINE return #-}
  {-# INLINE (>>=) #-}

instance Fail.MonadFail Eval where
  fail x = Eval (fail x)

instance MonadIO Eval where
  liftIO = io

instance MonadFix Eval where
  mfix f = Eval $ mfix (\x -> runEval (f x))

-- | Lift an 'IO' computation into the 'Eval' monad.
io :: IO a -> Eval a
io m = Eval m
{-# INLINE io #-}


-- Errors ----------------------------------------------------------------------

-- | Panic from an @Eval@ context.
evalPanic :: HasCallStack => String -> [String] -> a
evalPanic cxt = panic ("[Eval] " ++ cxt)


-- | Data type describing errors that can occur during evaluation.
data EvalError
  = InvalidIndex (Maybe Integer)  -- ^ Out-of-bounds index
  | DivideByZero                  -- ^ Division or modulus by 0
  | NegativeExponent              -- ^ Exponentiation by negative integer
  | LogNegative                   -- ^ Logarithm of a negative integer
  | UserError String              -- ^ Call to the Cryptol @error@ primitive
  | LoopError String              -- ^ Detectable nontermination
  | NoPrim Name                   -- ^ Primitive with no implementation
  | BadRoundingMode Integer       -- ^ Invalid rounding mode
  | BadValue String               -- ^ Value outside the domain of a partial function.
    deriving Typeable

instance PP EvalError where
  ppPrec _ e = case e of
    InvalidIndex (Just i) -> text "invalid sequence index:" <+> integer i
    InvalidIndex Nothing  -> text "invalid sequence index"
--    TypeCannotBeDemoted t -> text "type cannot be demoted:" <+> pp t
    DivideByZero -> text "division by 0"
    NegativeExponent -> text "negative exponent"
    LogNegative -> text "logarithm of negative"
    UserError x -> text "Run-time error:" <+> text x
    LoopError x -> text "<<loop>>" <+> text x
    BadRoundingMode r -> "invalid rounding mode" <+> integer r
    BadValue x -> "invalid input for" <+> backticks (text x)
    NoPrim x -> text "unimplemented primitive:" <+> pp x

instance Show EvalError where
  show = show . pp

data EvalErrorEx =
  EvalErrorEx Range EvalError
 deriving Typeable

instance PP EvalErrorEx where
  ppPrec _ (EvalErrorEx rng ex)
    | rng == emptyRange = pp ex
    | otherwise = vcat [ pp ex, text "at" <+> pp rng ]

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


-- | For things like @`(inf)@ or @`(0-1)@.
--typeCannotBeDemoted :: Type -> a
--typeCannotBeDemoted t = X.throw (TypeCannotBeDemoted t)

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
