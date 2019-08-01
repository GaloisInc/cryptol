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

module Cryptol.Eval.Monad
( -- * Evaluation monad
  Eval(..)
, runEval
, EvalOpts(..)
, getEvalOpts
, PPOpts(..)
, io
, delay
, delayFill
, ready
, blackhole
  -- ** Avoiding infinite loops
, later
, cutoff
  -- * Error reporting
, EvalError(..)
, evalPanic
, typeCannotBeDemoted
, divideByZero
, negativeExponent
, logNegative
, wordTooWide
, cryUserError
, cryLoopError
, cryNoPrimError
, invalidIndex
) where

import           Control.DeepSeq
import           Control.Monad
import           Control.Monad.Fix
import           Control.Monad.IO.Class
import           Data.IORef
import           Data.Typeable (Typeable)
import qualified Control.Exception as X
import           Numeric.Natural

import Cryptol.ModuleSystem.Name (Supply)
import Cryptol.Parser.Position (Range)
import Cryptol.Utils.Panic
import Cryptol.Utils.PP
import Cryptol.Utils.Logger (Logger)
import Cryptol.TypeCheck.AST (Type,Name)

-- | A computation that returns an already-evaluated value.
ready :: a -> Eval a
ready a = Ready a

-- | How to pretty print things when evaluating
data PPOpts = PPOpts
  { useAscii     :: Bool
  , useBase      :: Int
  , useInfLength :: Int
  }

-- | Some options for evaluation
data EvalOpts = EvalOpts
  { evalLogger :: Logger    -- ^ Where to print stuff (e.g., for @trace@)
  , evalPPOpts :: PPOpts    -- ^ How to pretty print things.
  }


-- | The monad for Cryptol evaluation.
data Eval a
   = Ready !a
   | Thunk !(EvalOpts -> EvalStep a)

data ThunkState a
  = Unforced        -- ^ This thunk has not yet been forced
  | BlackHole       -- ^ This thunk is currently being evaluated
  | Forced !(Either EvalError a)
    -- ^ This thunk has previously been forced,
    -- and has the given value, or evaluation resulted in an error.


-- | Access the evaluation options.
getEvalOpts :: Eval EvalOpts
getEvalOpts = Thunk return

{-# INLINE delay #-}
-- | Delay the given evaluation computation, returning a thunk
--   which will run the computation when forced.  Raise a loop
--   error if the resulting thunk is forced during its own evaluation.
delay :: Maybe String     -- ^ Optional name to print if a loop is detected
      -> Eval a           -- ^ Computation to delay
      -> Eval (Eval a)
delay _ (Ready a) = Ready (Ready a)
delay msg (Thunk x) = Thunk $ \opts -> do
  let msg' = maybe "" ("while evaluating "++) msg
  let retry = cryLoopError msg'
  r <- ioStep $ newIORef Unforced
  return $ unDelay retry r (x opts)

{-# INLINE delayFill #-}

-- | Delay the given evaluation computation, returning a thunk
--   which will run the computation when forced.  Run the 'retry'
--   computation instead if the resulting thunk is forced during
--   its own evaluation.
delayFill :: Eval a        -- ^ Computation to delay
          -> Eval a        -- ^ Backup computation to run if a tight loop is detected
          -> Eval (Eval a)
delayFill (Ready x) _ = Ready (Ready x)
delayFill (Thunk x) retry = Thunk $ \opts -> do
  r <- ioStep $ newIORef Unforced
  return $ unDelay retry r (x opts)

-- | Produce a thunk value which can be filled with its associated computation
--   after the fact.  A preallocated thunk is returned, along with an operation to
--   fill the thunk with the associated computation.
--   This is used to implement recursive declaration groups.
blackhole :: String -- ^ A name to associate with this thunk.
          -> Eval (Eval a, Eval a -> Eval ())
blackhole msg = do
  r <- io $ newIORef (fail msg)
  let get = join (io $ readIORef r)
  let set = io . writeIORef r
  return (get, set)

unDelay :: Eval a -> IORef (ThunkState a) -> EvalStep a -> Eval a
unDelay retry r x = do
  rval <- io $ readIORef r
  case rval of
    Forced val -> toVal val
    BlackHole  ->
      retry
    Unforced -> do
      io $ writeIORef r BlackHole
      val <- try x
      io $ writeIORef r (Forced val)
      toVal val

  where
  toVal mbV = case mbV of
                Right a -> pure a
                Left e  -> throwEval e

-- | Steps of evaluation can be interrupted
data EvalStep a = Later (IO (EvalStep a)) | Now !a
  deriving Functor

-- | Run forever, if necessary
runSteps :: EvalStep a -> IO a
runSteps (Now x) = return x
runSteps (Later act) = act >>= runSteps

step :: EvalStep a -> EvalStep a
step x = Later (return x)

later :: Eval a -> Eval a
later (Ready x) = Ready x
later (Thunk f) = Thunk $ \opts -> step (f opts)

cutoff :: Natural -> Eval a -> Eval (Maybe a)
cutoff _ (Ready x) = return (Just x)
cutoff i (Thunk f) = Thunk $ \opts -> Later $ Now <$> cutoffSteps i (f opts)

cutoffSteps :: Natural -> EvalStep a -> IO (Maybe a)
cutoffSteps i act
  | i < 1 = return Nothing
  | otherwise =
    case act of
      Now x -> return (Just x)
      Later act' -> act' >>= cutoffSteps (i - 1)

ioStep :: IO a -> EvalStep a
ioStep act = Later (Now <$> act)

throwEval :: X.Exception e => e -> Eval a
throwEval exn = io (X.throwIO exn)

try :: EvalStep a -> Eval (Either EvalError a)
try (Later act) =
  Thunk $ \opts -> Later $ do
    res <- X.try act
    case res of
      Left err -> return (return (Left err))
      Right v -> return (Right <$> v)
try (Now v) = return (Right v)


instance Applicative EvalStep where
  pure = Now
  Later fun <*> x =
    Later $ fun >>= return . (<*> x)
  Now fun <*> Later x =
    Later $ x >>= return . fmap fun
  Now fun <*> Now x = Now (fun x)

instance Monad EvalStep where
  return = pure
  Later x >>= f =
    Later $ x >>= return . (>>= f)
  Now v >>= f = f v

-- | Execute the given evaluation action.
runEval :: EvalOpts -> Eval a -> IO a
runEval _ (Ready a) = return a
runEval opts (Thunk x) = runSteps (x opts)

{-# INLINE evalBind #-}
evalBind :: Eval a -> (a -> Eval b) -> Eval b
evalBind (Ready a) f = f a
evalBind (Thunk x) f =
  Thunk $ \opts -> do
    res <- x opts
    case f res of
      Ready a -> return a
      Thunk y -> y opts

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
  fail x = Thunk (\_ -> fail x)
  (>>=)  = evalBind
  {-# INLINE return #-}
  {-# INLINE (>>=) #-}

instance MonadIO Eval where
  liftIO = io

instance NFData a => NFData (Eval a) where
  rnf (Ready a) = rnf a
  rnf (Thunk _) = ()

instance MonadFix Eval where
  mfix f = Thunk $ \opts -> Later $
    mfix $ \x ->
      let foo = Thunk (\ _ -> x) >>= f
      in case foo of
           Thunk m -> return (m opts)
           Ready v -> return (return v)

-- | Lift an 'IO' computation into the 'Eval' monad.
io :: IO a -> Eval a
io m = Thunk (\_ -> Later (Now <$> m))
{-# INLINE io #-}


-- Errors ----------------------------------------------------------------------

-- | Panic from an @Eval@ context.
evalPanic :: HasCallStack => String -> [String] -> a
evalPanic cxt = panic ("[Eval] " ++ cxt)


-- | Data type describing errors that can occur during evaluation.
data EvalError
  = InvalidIndex Integer          -- ^ Out-of-bounds index
  | TypeCannotBeDemoted Type      -- ^ Non-numeric type passed to @number@ function
  | DivideByZero                  -- ^ Division or modulus by 0
  | NegativeExponent              -- ^ Exponentiation by negative integer
  | LogNegative                   -- ^ Logarithm of a negative integer
  | WordTooWide Integer           -- ^ Bitvector too large
  | UserError String              -- ^ Call to the Cryptol @error@ primitive
  | LoopError String              -- ^ Detectable nontermination
  | NoPrim Name                   -- ^ Primitive with no implementation
    deriving (Typeable,Show)

instance PP EvalError where
  ppPrec _ e = case e of
    InvalidIndex i -> text "invalid sequence index:" <+> integer i
    TypeCannotBeDemoted t -> text "type cannot be demoted:" <+> pp t
    DivideByZero -> text "division by 0"
    NegativeExponent -> text "negative exponent"
    LogNegative -> text "logarithm of negative"
    WordTooWide w ->
      text "word too wide for memory:" <+> integer w <+> text "bits"
    UserError x -> text "Run-time error:" <+> text x
    LoopError x -> text "<<loop>>" <+> text x
    NoPrim x -> text "unimplemented primitive:" <+> pp x

instance X.Exception EvalError

-- | For things like @`(inf)@ or @`(0-1)@.
typeCannotBeDemoted :: Type -> a
typeCannotBeDemoted t = X.throw (TypeCannotBeDemoted t)

-- | For division by 0.
divideByZero :: Eval a
divideByZero = io (X.throwIO DivideByZero)

-- | For exponentiation by a negative integer.
negativeExponent :: Eval a
negativeExponent = io (X.throwIO NegativeExponent)

-- | For logarithm of a negative integer.
logNegative :: Eval a
logNegative = io (X.throwIO LogNegative)

-- | For when we know that a word is too wide and will exceed gmp's
-- limits (though words approaching this size will probably cause the
-- system to crash anyway due to lack of memory).
wordTooWide :: Integer -> a
wordTooWide w = X.throw (WordTooWide w)

-- | For the Cryptol @error@ function.
cryUserError :: String -> Eval a
cryUserError msg = io (X.throwIO (UserError msg))

cryNoPrimError :: Name -> Eval a
cryNoPrimError x = io (X.throwIO (NoPrim x))

-- | For cases where we can detect tight loops.
cryLoopError :: String -> Eval a
cryLoopError msg = io (X.throwIO (LoopError msg))

-- | A sequencing operation has gotten an invalid index.
invalidIndex :: Integer -> Eval a
invalidIndex i = io (X.throwIO (InvalidIndex i))
