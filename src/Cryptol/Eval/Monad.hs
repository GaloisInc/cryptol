-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}

module Cryptol.Eval.Monad where

  --   Eval(..)
  -- , runEval
  -- , io
  -- , delay
  -- , ready
  -- , blackhole
  -- ) where


import           Control.DeepSeq
import           Control.Monad
import           Control.Monad.Fix
import           Control.Monad.IO.Class
import           Data.IORef
import           Data.Typeable (Typeable)
import qualified Control.Exception as X


import Cryptol.Utils.Panic
import Cryptol.Utils.PP
import Cryptol.TypeCheck.AST(Type)


ready :: a -> Eval a
ready a = Ready a

data Eval a
   = Ready a
   | Thunk !(IO a)
 deriving (Functor)

data ThunkState a
  = Unforced
  | BlackHole
  | Forced a

delay :: Maybe String -> Eval a -> Eval (Eval a)
delay _ (Ready a) = Ready (Ready a)
delay msg (Thunk x) = Thunk $ do
  r <- newIORef Unforced
  return $ unDelay msg r x

blackhole :: String -> Eval (Eval a, Eval a -> Eval ())
blackhole msg = do
  r <- io $ newIORef (fail msg)
  let get = join (io $ readIORef r)
  let set = io . writeIORef r
  return (get, set)

unDelay :: Maybe String -> IORef (ThunkState a) -> IO a -> Eval a
unDelay msg r x = do
  rval <- io $ readIORef r
  case rval of
    Forced val -> return val
    BlackHole  -> do
      let msg' = maybe "" ("while evaluating "++) msg
      cryLoopError msg'
    Unforced -> io $ do
      writeIORef r BlackHole
      val <- x
      writeIORef r (Forced val)
      return val

runEval :: Eval a -> IO a
runEval (Ready a) = return a
runEval (Thunk x) = x

evalBind :: Eval a -> (a -> Eval b) -> Eval b
evalBind (Ready a) f  = f a
evalBind (Thunk x) f  = Thunk (x >>= runEval . f)

instance Applicative Eval where
  pure  = return
  (<*>) = ap

instance Monad Eval where
  return = Ready
  fail   = Thunk . fail
  (>>=)  = evalBind

instance MonadIO Eval where
  liftIO = io

instance NFData a => NFData (Eval a) where
  rnf (Ready a) = rnf a
  rnf (Thunk _) = ()

instance MonadFix Eval where
  mfix f = Thunk $ mfix (\x -> runEval (f x))

io :: IO a -> Eval a
io = Thunk


-- Errors ----------------------------------------------------------------------

-- | Panic from an Eval context.
evalPanic :: String -> [String] -> a
evalPanic cxt = panic ("[Eval] " ++ cxt)


data EvalError
  = InvalidIndex Integer
  | TypeCannotBeDemoted Type
  | DivideByZero
  | WordTooWide Integer
  | UserError String
  | LoopError String
    deriving (Typeable,Show)

instance PP EvalError where
  ppPrec _ e = case e of
    InvalidIndex i -> text "invalid sequence index:" <+> integer i
    TypeCannotBeDemoted t -> text "type cannot be demoted:" <+> pp t
    DivideByZero -> text "division by 0"
    WordTooWide w ->
      text "word too wide for memory:" <+> integer w <+> text "bits"
    UserError x -> text "Run-time error:" <+> text x
    LoopError x -> text "<<loop>>" <+> text x

instance X.Exception EvalError

-- | For things like `(inf) or `(0-1)
typeCannotBeDemoted :: Type -> a
typeCannotBeDemoted t = X.throw (TypeCannotBeDemoted t)

-- | For division by 0.
divideByZero :: a
divideByZero = X.throw DivideByZero

-- | For when we know that a word is too wide and will exceed gmp's
-- limits (though words approaching this size will probably cause the
-- system to crash anyway due to lack of memory)
wordTooWide :: Integer -> a
wordTooWide w = X.throw (WordTooWide w)

-- | For `error`
cryUserError :: String -> Eval a
cryUserError msg = Thunk (X.throwIO (UserError msg))

-- | For cases where we can detect tight loops
cryLoopError :: String -> Eval a
cryLoopError msg = Thunk (X.throwIO (LoopError msg))

-- | A sequencing operation has gotten an invalid index.
invalidIndex :: Integer -> Eval a
invalidIndex i = Thunk (X.throwIO (InvalidIndex i))
