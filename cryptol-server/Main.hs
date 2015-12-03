-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Alpha version of a Cryptol server that communicates via JSON over
-- ZeroMQ. This API is highly unstable and extremely likely to change
-- in the near future.

{-# LANGUAGE CPP #-}
{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wall -fno-warn-type-defaults #-}
module Main where

import Control.Concurrent
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Control
import qualified Control.Exception as X
import Data.Aeson
import Data.Aeson.Encode.Pretty
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as BSL
import Data.Char
import Data.IORef
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Data.Word
import System.Environment
import System.Exit
import System.FilePath
import System.ZMQ4
import Text.Read

import qualified Cryptol.Eval.Value as E
import Cryptol.REPL.Command
import Cryptol.REPL.Monad
import Cryptol.Symbolic (ProverResult(..))
import qualified Cryptol.TypeCheck.AST as T
import qualified Cryptol.ModuleSystem as M
import Cryptol.Utils.PP

import Cryptol.Aeson ()

import Prelude ()
import Prelude.Compat

data RCommand
  = RCEvalExpr Text
  | RCApplyFun FunHandle E.Value
  | RCTypeOf Text
  | RCSetOpt Text Text
  | RCCheck Text
  | RCExhaust Text
  | RCProve Text
  | RCSat Text
  | RCLoadPrelude
  | RCLoadModule FilePath
  | RCDecls
  | RCUnknownCmd Text
  | RCExit

instance FromJSON RCommand where
  parseJSON = withObject "RCommand" $ \o -> do
    tag <- o .: "tag"
    flip (withText "tag") tag $ \case
      "evalExpr"    -> RCEvalExpr              <$> o .: "expr"
      "applyFun"    -> RCApplyFun              <$> o .: "handle" <*> o .: "arg"
      "typeOf"      -> RCTypeOf                <$> o .: "expr"
      "setOpt"      -> RCSetOpt                <$> o .: "key" <*> o .: "value"
      "check"       -> RCCheck                 <$> o .: "expr"
      "exhaust"     -> RCExhaust               <$> o .: "expr"
      "prove"       -> RCProve                 <$> o .: "expr"
      "sat"         -> RCSat                   <$> o .: "expr"
      "loadPrelude" -> return RCLoadPrelude
      "loadModule"  -> RCLoadModule . T.unpack <$> o .: "filePath"
      "browse"      -> return RCDecls
      "exit"        -> return RCExit
      unknown       -> return (RCUnknownCmd unknown)

newtype FunHandle = FH Int
  deriving (Eq, Ord, Enum, Bounded, Show)

instance ToJSON FunHandle where
  toJSON (FH i) = toJSON i

instance FromJSON FunHandle where
  parseJSON v = FH <$> parseJSON v

data RResult
  = RRValue E.Value
  | RRFunValue FunHandle T.Type
  | RRType T.Schema String -- pretty-printed type
  | RRDecls M.IfaceDecls
  | RRCheck String
  | RRExhaust String
  | RRSat [[E.Value]]
    -- ^ A list of satisfying assignments. Empty list means unsat, max
    -- length determined by @satNum@ interpreter option
  | RRProve (Maybe [E.Value])
    -- ^ Counterexample if invalid or 'Nothing' if valid
  | RRProverError String
  | RRInteractiveError REPLException String -- pretty-printed exception
  | RRUnknownCmd Text
  | RRBadMessage BS.ByteString String
  | RROk
  | RRInterrupted

instance ToJSON RResult where
  toJSON = \case
    RRValue v -> object
      [ "tag" .= "value", "value" .= v ]
    RRFunValue fh t -> object
      [ "tag" .= "funValue", "handle" .= fh, "type" .= t ]
    RRType s pps -> object
      [ "tag" .= "type", "value" .= s, "pp" .= pps ]
    RRDecls ifds -> object
      [ "tag" .= "decls", "decls" .= ifds ]
    RRCheck out -> object
      [ "tag" .= "check", "out" .= out ]
    RRExhaust out -> object
      [ "tag" .= "exhaust", "out" .= out ]
    RRSat out -> object
      [ "tag" .= "sat", "assignments" .= out ]
    RRProve out -> object
      [ "tag" .= "prove", "counterexample" .= out ]
    RRProverError msg -> object
      [ "tag" .= "proverError", "message" .= msg ]
    RRInteractiveError err pps -> object
      [ "tag" .= "interactiveError", "error" .= err, "pp" .= pps ]
    RRUnknownCmd txt -> object
      [ "tag" .= "unknownCommand", "command" .= txt ]
    RRBadMessage msg err -> object
      [ "tag" .= "badMessage", "message" .= BS.unpack msg, "error" .= err ]
    RROk -> object
      [ "tag" .= "ok" ]
    RRInterrupted -> object
      [ "tag" .= "interrupted" ]

data ControlMsg
  = CMConnect
    -- ^ Request a new Cryptol context and connection
  | CMInterrupt
    -- ^ Request an interrupt of all current Cryptol contexts
  | CMExit
    -- ^ Request that the entire server shut down
  | CMUnknown Text
    -- ^ Unknown message

instance FromJSON ControlMsg where
  parseJSON = withObject "ControlMsg" $ \o -> do
    tag <- o .: "tag"
    flip (withText "tag") tag $ \case
      "connect" -> return CMConnect
      "interrupt" -> return CMInterrupt
      "exit" -> return CMExit
      other -> return $ CMUnknown other

data ControlReply
  = CRConnect Word16
    -- ^ Return the port for a new connection
  | CRInterrupted
    -- ^ Acknowledge receipt of an interrupt command
  | CRExiting
    -- ^ Acknowledge receipt of an exit command
  | CRBadMessage BS.ByteString String
    -- ^ Acknowledge receipt of an ill-formed control message

instance ToJSON ControlReply where
  toJSON = \case
    CRConnect port -> object
      [ "tag" .= "connect", "port" .= port ]
    CRInterrupted -> object
      [ "tag" .= "interrupted" ]
    CRExiting -> object
      [ "tag" .= "exiting" ]
    CRBadMessage msg err -> object
      [ "tag" .= "badMessage", "message" .= BS.unpack msg, "error" .= err ]

server :: Word16 -> IO ()
server port =
  withContext $ \ctx ->
  withSocket ctx Rep $ \rep -> do
  let addr = "tcp://127.0.0.1:" ++ show port
  putStrLn ("[cryptol-server] coming online at " ++ addr)
  bind rep addr
  workers <- newIORef Set.empty
  let loop = do
        msg <- receive rep
        putStrLn "[cryptol-server] received message:"
        case decodeStrict msg of
          Nothing -> BS.putStrLn msg
          Just js -> BSL.putStrLn (encodePretty (js :: Value))
        case eitherDecodeStrict msg of
          Left err -> reply rep $ CRBadMessage msg err
          Right CMConnect -> do
            putStrLn "[cryptol-server] handling new incoming connection"
            newRep <- socket ctx Rep
            bind newRep "tcp://127.0.0.1:*"
            newAddr <- lastEndpoint newRep
            let portStr = reverse . takeWhile isDigit . reverse $ newAddr
            putStrLn ("[cryptol-server] starting worker on interface " ++ newAddr)
            tid <- forkFinally (runRepl newRep) (removeCurrentWorker workers)
            addNewWorker workers tid
            reply rep $ CRConnect (read portStr)
          Right CMInterrupt -> do
            s <- readIORef workers
            -- TODO: only throw to the relevant worker; we'll need
            -- port number from request
            forM_ s $ \tid -> throwTo tid X.UserInterrupt
            reply rep $ CRInterrupted
          Right CMExit -> do
            putStrLn "[cryptol-server] shutting down"
            reply rep $ CRExiting
            exitSuccess
          Right (CMUnknown cmd) -> do
            putStrLn ("[cryptol-server] unknown control command: " ++ T.unpack cmd)
            reply rep $ CRBadMessage msg "unknown control command"
        loop
  loop

reply :: (ToJSON a, MonadIO m) => Socket Rep -> a -> m ()
reply rep msg = liftIO $ do
  let bmsg = BS.concat . BSL.toChunks . encodePretty $ msg
  putStrLn "[cryptol-server] sending response:"
  BS.putStrLn bmsg
  send rep [] bmsg

addNewWorker :: IORef (Set ThreadId) -> ThreadId -> IO ()
addNewWorker workers tid =
  atomicModifyIORef workers $ \s -> (Set.insert tid s, ())

removeCurrentWorker :: IORef (Set ThreadId) -> a -> IO ()
removeCurrentWorker workers _result = do
  tid <- myThreadId
  atomicModifyIORef workers $ \s -> (Set.delete tid s, ())

runRepl :: Socket Rep -> IO ()
runRepl rep = runREPL False $ do -- TODO: batch mode?
  mCryptolPath <- io $ lookupEnv "CRYPTOLPATH"
  case mCryptolPath of
    Nothing -> return ()
    Just path -> prependSearchPath path'
#if defined(mingw32_HOST_OS) || defined(__MINGW32__)
      -- Windows paths search from end to beginning
      where path' = reverse (splitSearchPath path)
#else
      where path' = splitSearchPath path
#endif
  funHandles <- io $ newIORef (Map.empty, minBound :: FunHandle)
  let handle err = reply rep (RRInteractiveError err (show (pp err)))
      handleAsync :: X.AsyncException -> IO ()
      handleAsync _int = reply rep RROk
      loop = liftBaseWith $ \run -> X.handle handleAsync $ run $ do
        msg <- io $ receive rep
        io $ putStrLn "[cryptol-worker] received message:"
        case decodeStrict msg of
          Nothing -> io $ BS.putStrLn msg
          Just js -> io $ BSL.putStrLn (encodePretty (js :: Value))
        flip catch handle $ case eitherDecodeStrict msg of
          Left cmdErr -> reply rep (RRBadMessage msg cmdErr)
          Right rc -> case rc of
            RCEvalExpr txt -> do
              expr <- replParseExpr (T.unpack txt)
              (val, ty) <- replEvalExpr expr
              case val of
                E.VFun f -> do
                  fh <- io $ atomicModifyIORef' funHandles $ \(m, fh) ->
                    let m' = Map.insert fh f m
                        fh' = succ fh
                    in ((m', fh'), fh)
                  reply rep (RRFunValue fh ty)
                _ -> reply rep (RRValue val)
            RCApplyFun fh arg -> do
              (m, _) <- io $ readIORef funHandles
              case Map.lookup fh m of
                Nothing -> reply rep (RRBadMessage "invalid function handle" (show fh))
                Just f -> do
                  case f arg of
                    E.VFun g -> do
                      gh <- io $ atomicModifyIORef' funHandles $ \(m', gh) ->
                        let m'' = Map.insert gh g m'
                            gh' = succ gh
                        in ((m'', gh'), gh)
                      -- TODO: bookkeeping to track the type of this value
                      reply rep (RRFunValue gh T.tZero)
                    val -> reply rep (RRValue val)
            RCTypeOf txt -> do
              expr <- replParseExpr (T.unpack txt)
              (_expr, _def, sch) <- replCheckExpr expr
              reply rep (RRType sch (show (pp sch)))
            RCSetOpt key val -> do
              setOptionCmd (T.unpack key ++ "=" ++ T.unpack val)
              reply rep RROk
            RCCheck expr -> do
              (_, out) <- withCapturedOutput (qcCmd QCRandom (T.unpack expr))
              reply rep (RRCheck out)
            RCExhaust expr -> do
              (_, out) <- withCapturedOutput (qcCmd QCExhaust (T.unpack expr))
              reply rep (RRExhaust out)
            RCProve expr -> do
              result <- onlineProveSat False (T.unpack expr) Nothing
              case result of
                AllSatResult [cex] ->
                  reply rep (RRProve (Just (map (\(_,_,v) -> v) cex)))
                ThmResult _ ->
                  reply rep (RRProve Nothing)
                ProverError err ->
                  reply rep (RRProverError err)
                _ ->
                  reply rep (RRProverError "unexpected prover result")
            RCSat expr ->  do
              result <- onlineProveSat True (T.unpack expr) Nothing
              case result of
                AllSatResult sas ->
                  reply rep (RRSat (map (map (\(_,_,v) -> v)) sas))
                ThmResult _ ->
                  reply rep (RRSat [])
                ProverError err ->
                  reply rep (RRProverError err)
                _ ->
                  reply rep (RRProverError "unexpected prover result")
            RCLoadPrelude -> do
              loadPrelude
              reply rep RROk
            RCLoadModule fp -> do
              loadCmd fp
              reply rep RROk
            RCDecls -> do
              (decls, _namingEnv, _nameDisp) <- getFocusedEnv
              reply rep (RRDecls decls)
            RCUnknownCmd cmd -> reply rep (RRUnknownCmd cmd)
            RCExit -> do
              reply rep RROk
              io $ close rep
              io $ putStrLn "[cryptol-worker] shutting down"
  void $ forever loop

withCapturedOutput :: REPL a -> REPL (a, String)
withCapturedOutput m = do
  old <- getPutStr
  buf <- io $ newIORef ""
  setPutStr $ \s -> modifyIORef' buf (++ s)
  x <- m
  s <- io $ readIORef buf
  setPutStr old
  return (x, s)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> server 5555
    [portStr] ->
       case readMaybe portStr of
         Just port -> server port
         Nothing -> server 5555
    _ -> error "port is the only allowed argument"
