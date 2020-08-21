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

module Cryptol.Eval.Monad
( -- * Evaluation monad
  Eval(..)
, runEval
, EvalOpts(..)
, getEvalOpts
, PPOpts(..)
, PPFloatFormat(..)
, PPFloatExp(..)
, defaultPPOpts
, io
, delayFill
, ready
, blackhole
, evalSpark
  -- * Error reporting
, Unsupported(..)
, EvalError(..)
, evalPanic
, wordTooWide
, typeCannotBeDemoted
) where

import           Control.Concurrent
import           Control.Concurrent.Async
import           Control.Concurrent.STM

import           Control.Monad
import qualified Control.Monad.Fail as Fail
import           Control.Monad.Fix
import           Control.Monad.IO.Class
import           Data.Typeable (Typeable)
import qualified Control.Exception as X


import Cryptol.Utils.Panic
import Cryptol.Utils.PP
import Cryptol.Utils.Logger(Logger)
import Cryptol.TypeCheck.AST(Type,Name)

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
data Eval a
   = Ready !a
   | Thunk !(EvalOpts -> IO a)

data ThunkState a
  = Void !String             -- ^ This thunk has not yet been initialized
  | Unforced !(IO a) !(IO a) -- ^ This thunk has not yet been forced
  | UnderEvaluation !ThreadId !(IO a) -- ^ This thunk is currently being evaluated
  | ForcedErr !EvalError
  | Forced !a

-- | Access the evaluation options.
getEvalOpts :: Eval EvalOpts
getEvalOpts = Thunk pure

{-# INLINE delayFill #-}

-- | Delay the given evaluation computation, returning a thunk
--   which will run the computation when forced.  Run the 'retry'
--   computation instead if the resulting thunk is forced during
--   its own evaluation.
delayFill ::
  Eval a {- ^ Computation to delay -} ->
  Eval a {- ^ Backup computation to run if a tight loop is detected -} ->
  Eval (Eval a)
delayFill (Ready x) _ = Ready (Ready x)
delayFill (Thunk x) backup = Thunk $ \opts -> do
  r <- newTVarIO (Unforced (x opts) (runEval opts backup))
  return $ unDelay r


-- | Begin executing the given operation in a separate thread,
--   returning a thunk which will await the completion of
--   the computation when forced.
evalSpark ::
  Eval a ->
  Eval (Eval a)
evalSpark (Ready x) = Ready (Ready x)
evalSpark (Thunk x) = Thunk $ \opts ->
  do a <- async (x opts)
     return (Thunk $ \_ -> wait a)


-- | Produce a thunk value which can be filled with its associated computation
--   after the fact.  A preallocated thunk is returned, along with an operation to
--   fill the thunk with the associated computation.
--   This is used to implement recursive declaration groups.
blackhole ::
  String {- ^ A name to associate with this thunk. -} ->
  Eval (Eval a, Eval a -> Eval ())
blackhole msg = Thunk $ \opts ->
  do tv <- newTVarIO (Void msg)
     let set (Ready x) = io $ atomically (writeTVar tv (Forced x))
         set (Thunk m) = io $ atomically (writeTVar tv (Unforced (m opts) (fail msg)))
     return (unDelay tv, set)

unDelay :: TVar (ThunkState a) -> Eval a
unDelay tv = io $
  readTVarIO tv >>= \case
    Forced x -> pure x
    ForcedErr e -> X.throwIO e
    _ ->
      do tid <- myThreadId
         res <- atomically $ do
                  res <- readTVar tv
                  case res of
                    Unforced _ backup -> writeTVar tv (UnderEvaluation tid backup)
                    UnderEvaluation t _
                      | tid == t  -> writeTVar tv (UnderEvaluation t (fail "<<loop>>"))
                      | otherwise -> retry -- wait, if some other thread is evaualting
                    _ -> return ()
                  return res
         let doWork work =
               X.try work >>= \case
                 Left ex -> do atomically (writeTVar tv (ForcedErr ex))
                               X.throwIO ex
                 Right a -> do atomically (writeTVar tv (Forced a))
                               return a
         case res of
           Void msg -> evalPanic "unDelay" ["Thunk forced before it was initialized", msg]
           Forced x -> pure x
           ForcedErr e -> X.throwIO e
           UnderEvaluation _ backup -> doWork backup -- this thread was already evaluating this thunk
           Unforced work _ -> doWork work

-- | Execute the given evaluation action.
runEval :: EvalOpts -> Eval a -> IO a
runEval _ (Ready a) = return a
runEval opts (Thunk x) = x opts

{-# INLINE evalBind #-}
evalBind :: Eval a -> (a -> Eval b) -> Eval b
evalBind (Ready a) f  = f a
evalBind (Thunk x) f  = Thunk $ \opts -> x opts >>= runEval opts . f

instance Functor Eval where
  fmap f (Ready x) = Ready (f x)
  fmap f (Thunk m) = Thunk $ \opts -> f <$> m opts
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
  fail x = Thunk (\_ -> fail x)

instance MonadIO Eval where
  liftIO = io

instance MonadFix Eval where
  mfix f = Thunk $ \opts -> mfix (\x -> runEval opts (f x))

-- | Lift an 'IO' computation into the 'Eval' monad.
io :: IO a -> Eval a
io m = Thunk (\_ -> m)
{-# INLINE io #-}


-- Errors ----------------------------------------------------------------------

-- | Panic from an @Eval@ context.
evalPanic :: HasCallStack => String -> [String] -> a
evalPanic cxt = panic ("[Eval] " ++ cxt)


-- | Data type describing errors that can occur during evaluation.
data EvalError
  = InvalidIndex (Maybe Integer)  -- ^ Out-of-bounds index
  | TypeCannotBeDemoted Type      -- ^ Non-numeric type passed to @number@ function
  | DivideByZero                  -- ^ Division or modulus by 0
  | NegativeExponent              -- ^ Exponentiation by negative integer
  | LogNegative                   -- ^ Logarithm of a negative integer
  | WordTooWide Integer           -- ^ Bitvector too large
  | UserError String              -- ^ Call to the Cryptol @error@ primitive
  | LoopError String              -- ^ Detectable nontermination
  | NoPrim Name                   -- ^ Primitive with no implementation
  | BadRoundingMode Integer       -- ^ Invalid rounding mode
  | BadValue String               -- ^ Value outside the domain of a partial function.
    deriving (Typeable,Show)

instance PP EvalError where
  ppPrec _ e = case e of
    InvalidIndex (Just i) -> text "invalid sequence index:" <+> integer i
    InvalidIndex Nothing  -> text "invalid sequence index"
    TypeCannotBeDemoted t -> text "type cannot be demoted:" <+> pp t
    DivideByZero -> text "division by 0"
    NegativeExponent -> text "negative exponent"
    LogNegative -> text "logarithm of negative"
    WordTooWide w ->
      text "word too wide for memory:" <+> integer w <+> text "bits"
    UserError x -> text "Run-time error:" <+> text x
    LoopError x -> text "<<loop>>" <+> text x
    BadRoundingMode r -> "invalid rounding mode" <+> integer r
    BadValue x -> "invalid input for" <+> backticks (text x)
    NoPrim x -> text "unimplemented primitive:" <+> pp x

instance X.Exception EvalError


data Unsupported
  = UnsupportedSymbolicOp String  -- ^ Operation cannot be supported in the symbolic simulator
    deriving (Typeable,Show)

instance PP Unsupported where
  ppPrec _ e = case e of
    UnsupportedSymbolicOp nm -> text "operation can not be supported on symbolic values:" <+> text nm

instance X.Exception Unsupported


-- | For things like @`(inf)@ or @`(0-1)@.
typeCannotBeDemoted :: Type -> a
typeCannotBeDemoted t = X.throw (TypeCannotBeDemoted t)

-- | For when we know that a word is too wide and will exceed gmp's
-- limits (though words approaching this size will probably cause the
-- system to crash anyway due to lack of memory).
wordTooWide :: Integer -> a
wordTooWide w = X.throw (WordTooWide w)
