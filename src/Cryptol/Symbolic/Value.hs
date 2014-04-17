-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Cryptol.Symbolic.Value where

import Control.Applicative
import Control.Monad.Fix (MonadFix)
import Control.Monad.IO.Class
import Control.Monad.Reader (MonadReader, ReaderT, runReaderT)
import Control.Monad.Trans (lift)
import Data.Bits (bitSize)
import Data.IORef
import Data.Traversable

import Cryptol.Eval.Value (TValue)
import Cryptol.Symbolic.BitVector
import Cryptol.TypeCheck.AST
import Cryptol.Utils.Panic (panic)

import Data.SBV (Symbolic, SBool, SMTConfig, fromBitsBE, sbvTestBit)

-- Symbolic Simulator Monad ----------------------------------------------------

data SimEnv = SimEnv
  { simConfig    :: SMTConfig
  , simPath      :: SBool
  , simIteSolver :: Bool
  , simVerbose   :: Bool
  }

newtype TheMonad a = TheMonad (ReaderT SimEnv Symbolic a)
  deriving (Functor, Applicative, Monad, MonadFix, MonadIO, MonadReader SimEnv)

-- ^ The SBool environment parameter models the path condition, i.e.
-- an assertion derived from the context of surrounding if-then-else
-- statements. It is used to determine whether new if-then-else
-- branches are reachable. It is important to include this within the
-- monad so that a conditional in a function body will be evaluated
-- relative to the path condition where the function is applied,
-- rather than with the path condition where the function was defined.

runTheMonad :: TheMonad a -> SimEnv -> Symbolic a
runTheMonad (TheMonad r) = runReaderT r

liftSymbolic :: Symbolic a -> TheMonad a
liftSymbolic s = TheMonad (lift s)

-- Values and Thunks -----------------------------------------------------------

data Value
  = VRecord [(Name, Thunk)]   -- @ { .. } @
  | VTuple [Thunk]            -- @ ( .. ) @
  | VBit SBool                -- @ Bit    @
  | VWord SWord               -- @ [n]Bit @
  | VNil
  | VCons Thunk Thunk         -- @ [n]a @ head, tail
  | VFun (Thunk -> TheMonad Value)     -- functions
  | VPoly (TValue -> TheMonad Value)   -- polymorphic values (kind *)

data Thunk
  = Thunk (IORef (Either (TheMonad Value) Value))
  | Ready Value

force :: Thunk -> TheMonad Value
force (Ready v) = return v
force (Thunk ref) = do
  r <- liftIO $ readIORef ref
  case r of
    Left m -> do
      v <- m
      liftIO $ writeIORef ref (Right v)
      return v
    Right v -> return v

delay :: TheMonad Value -> TheMonad Thunk
delay m = Thunk <$> liftIO (newIORef (Left m))

ready :: Value -> TheMonad Thunk
ready v = Thunk <$> liftIO (newIORef (Right v))

-- Constructors and Accessors --------------------------------------------------

tlam :: (TValue -> Value) -> Value
tlam f = VPoly (return . f)

vSeq :: [Thunk] -> Value
vSeq []       = VNil
vSeq (x : xs) = VCons x (Ready (vSeq xs))

vApply :: Value -> Value -> TheMonad Value
vApply (VFun f) v = f (Ready v)
vApply _ _ = fail "vApply: not a function"

fromVBit :: Value -> SBool
fromVBit (VBit b) = b
fromVBit _ = error "fromVBit: not a bit"

fromWord :: Value -> TheMonad SWord
fromWord (VWord s) = return s
fromWord v = do
  thunks <- fromSeq v
  vs <- traverse force thunks
  let bs = map fromVBit vs
  return $ Data.SBV.fromBitsBE bs

fromSeq :: Value -> TheMonad [Thunk]
fromSeq VNil = return []
fromSeq (VCons x th) = do
  v <- force th
  xs <- fromSeq v
  return (x : xs)
fromSeq (VWord s) = return $ reverse [ Ready (VBit (sbvTestBit s i)) | i <- [0 .. bitSize s - 1] ]
fromSeq _ = error "fromSeq: not a sequence"

fromVCons :: Value -> (Thunk, Thunk)
fromVCons (VCons h t) = (h, t)
fromVCons (VWord s) = fromVCons (foldr (\h t -> VCons (Ready h) (Ready t)) VNil bs)
  where bs = reverse [ VBit (sbvTestBit s i) | i <- [0 .. bitSize s - 1] ]
fromVCons _ = error "fromVCons: not a stream"

fromVFun :: Value -> (Thunk -> TheMonad Value)
fromVFun (VFun f) = f
fromVFun _ = error "fromVFun: not a function"

fromVTuple :: Value -> [Thunk]
fromVTuple (VTuple thunks) = thunks
fromVTuple _ = error "fromVTuple: not a tuple"

fromVRecord :: Value -> [(Name, Thunk)]
fromVRecord v = case v of
  VRecord fs -> fs
  _          -> evalPanic "fromVRecord" ["not a record"]

lookupRecord :: Name -> Value -> Thunk
lookupRecord f rec = case lookup f (fromVRecord rec) of
  Just th -> th
  Nothing -> error "lookupRecord"

-- Errors ----------------------------------------------------------------------

evalPanic :: String -> [String] -> a
evalPanic cxt = panic ("[Symbolic]" ++ cxt)
