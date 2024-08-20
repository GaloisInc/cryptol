-- |
-- Module      :  Cryptol.REPL.Command
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RecordWildCards #-}
-- See Note [-Wincomplete-uni-patterns and irrefutable patterns] in Cryptol.TypeCheck.TypePat
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Cryptol.REPL.Command (
    -- * Commands
    Command(..), CommandDescr(..), CommandBody(..), CommandResult(..)
  , parseCommand
  , runCommand
  , splitCommand
  , findCommand
  , findCommandExact
  , findNbCommand
  , commandList
  , emptyCommandResult

  , moduleCmd, loadCmd, loadPrelude, setOptionCmd

    -- Parsing
  , interactiveConfig
  , replParseExpr

    -- Evaluation and Typechecking
  , replEvalExpr
  , replCheckExpr

    -- Check, SAT, and prove
  , TestReport(..)
  , qcExpr, qcCmd, QCMode(..)
  , satCmd
  , proveCmd
  , onlineProveSat
  , offlineProveSat

    -- Check docstrings
  , checkDocStrings
  , SubcommandResult(..)
  , DocstringResult(..)

    -- Misc utilities
  , handleCtrlC
  , sanitize
  , withRWTempFile

    -- To support Notebook interface (might need to refactor)
  , replParse
  , liftModuleCmd
  , moduleCmdResult
  ) where

import Cryptol.REPL.Monad
import Cryptol.REPL.Trie
import Cryptol.REPL.Browse
import Cryptol.REPL.Help

import qualified Cryptol.ModuleSystem as M
import qualified Cryptol.ModuleSystem.Interface as M
import qualified Cryptol.ModuleSystem.Monad as M
import qualified Cryptol.ModuleSystem.Name as M
import qualified Cryptol.ModuleSystem.NamingEnv as M
import qualified Cryptol.ModuleSystem.Renamer as M
    (RenamerWarning(SymbolShadowed, PrefixAssocChanged))
import qualified Cryptol.Utils.Ident as M
import qualified Cryptol.ModuleSystem.Env as M
import Cryptol.ModuleSystem.Fingerprint(fingerprintHexString)

import           Cryptol.Backend.FloatHelpers as FP
import qualified Cryptol.Backend.Monad as E
import qualified Cryptol.Backend.SeqMap as E
import Cryptol.Backend.Concrete ( Concrete(..) )
import qualified Cryptol.Eval.Concrete as Concrete
import qualified Cryptol.Eval.Env as E
import           Cryptol.Eval.FFI
import           Cryptol.Eval.FFI.GenHeader
import qualified Cryptol.Eval.Type as E
import qualified Cryptol.Eval.Value as E
import qualified Cryptol.Eval.Reference as R
import Cryptol.Testing.Random
import qualified Cryptol.Testing.Random  as TestR
import Cryptol.Parser
    (parseExprWith,parseReplWith,ParseError(),Config(..),defaultConfig
    ,parseModName,parseHelpName,parseImpName)
import           Cryptol.Parser.Position (Position(..),Range(..),HasLoc(..))
import qualified Cryptol.TypeCheck.AST as T
import qualified Cryptol.TypeCheck.Error as T
import qualified Cryptol.TypeCheck.Parseable as T
import qualified Cryptol.TypeCheck.Subst as T
import           Cryptol.TypeCheck.Solve(defaultReplExpr)
import           Cryptol.TypeCheck.PP (dump)
import qualified Cryptol.Utils.Benchmark as Bench
import           Cryptol.Utils.PP hiding ((</>))
import           Cryptol.Utils.Panic(panic)
import           Cryptol.Utils.RecordMap
import qualified Cryptol.Parser.AST as P
import qualified Cryptol.Transform.Specialize as S
import Cryptol.Symbolic
  ( ProverCommand(..), QueryType(..)
  , ProverStats,ProverResult(..),CounterExampleType(..)
  )
import qualified Cryptol.Symbolic.SBV as SBV
import qualified Cryptol.Symbolic.What4 as W4
import Cryptol.Version (displayVersion)

import qualified Control.Exception as X
import Control.Monad hiding (mapM, mapM)
import qualified Control.Monad.Catch as Ex
import Control.Monad.IO.Class(liftIO)
import Text.Read (readMaybe)
import Control.Applicative ((<|>))
import qualified Data.Set as Set
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BS8
import Data.Bits (shiftL, (.&.), (.|.))
import Data.Char (isSpace,isPunctuation,isSymbol,isAlphaNum,isAscii)
import Data.Function (on)
import Data.List (intercalate, nub, isPrefixOf)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe,mapMaybe,isNothing)
import System.Environment (lookupEnv)
import System.Exit (ExitCode(ExitSuccess))
import System.Process (shell,createProcess,waitForProcess)
import qualified System.Process as Process(runCommand)
import System.FilePath((</>), (-<.>), isPathSeparator)
import System.Directory(getHomeDirectory,setCurrentDirectory,doesDirectoryExist
                       ,getTemporaryDirectory,setPermissions,removeFile
                       ,emptyPermissions,setOwnerReadable)
import System.IO
         (Handle,hFlush,stdout,openTempFile,hClose,openFile
         ,IOMode(..),hGetContents,hSeek,SeekMode(..))
import qualified System.Random.TF as TF
import qualified System.Random.TF.Instances as TFI
import Numeric (showFFloat)
import qualified Data.Text as T
import Data.IORef(newIORef, readIORef, writeIORef, modifyIORef)

import GHC.Float (log1p, expm1)

import Prelude ()
import Prelude.Compat

import qualified Data.SBV.Internals as SBV (showTDiff)
import Data.Foldable (foldl')



-- Commands --------------------------------------------------------------------

-- | Commands.
data Command
  = Command (Int -> Maybe FilePath -> REPL CommandResult) -- ^ Successfully parsed command
  | Ambiguous String [String] -- ^ Ambiguous command, list of conflicting
                              --   commands
  | Unknown String            -- ^ The unknown command

-- | Command builder.
data CommandDescr = CommandDescr
  { cNames    :: [String]
  , cArgs     :: [String]
  , cBody     :: CommandBody
  , cHelp     :: String
  , cLongHelp :: String
  }

instance Show CommandDescr where
  show = show . cNames

instance Eq CommandDescr where
  (==) = (==) `on` cNames

instance Ord CommandDescr where
  compare = compare `on` cNames

data CommandBody
  = ExprArg     (String   -> (Int,Int) -> Maybe FilePath -> REPL CommandResult)
  | FileExprArg (FilePath -> String -> (Int,Int) -> Maybe FilePath -> REPL CommandResult)
  | DeclsArg    (String   -> REPL CommandResult)
  | ExprTypeArg (String   -> REPL CommandResult)
  | ModNameArg  (String   -> REPL CommandResult)
  | FilenameArg (FilePath -> REPL CommandResult)
  | OptionArg   (String   -> REPL CommandResult)
  | ShellArg    (String   -> REPL CommandResult)
  | HelpArg     (String   -> REPL CommandResult)
  | NoArg       (REPL CommandResult)

data CommandResult = CommandResult
  { crType :: Maybe String -- ^ type output for relevant commands
  , crValue :: Maybe String -- ^ value output for relevant commands
  , crSuccess :: Bool -- ^ indicator that command successfully performed its task
  }
  deriving (Show)

emptyCommandResult :: CommandResult
emptyCommandResult = CommandResult
  { crType = Nothing
  , crValue = Nothing
  , crSuccess = True
  }

-- | REPL command parsing.
commands :: CommandMap
commands  = foldl insert emptyTrie commandList
  where
  insert m d = foldl (insertOne d) m (cNames d)
  insertOne d m name = insertTrie name d m

-- | Notebook command parsing.
nbCommands :: CommandMap
nbCommands  = foldl insert emptyTrie nbCommandList
  where
  insert m d = foldl (insertOne d) m (cNames d)
  insertOne d m name = insertTrie name d m

-- | A subset of commands safe for Notebook execution
nbCommandList :: [CommandDescr]
nbCommandList  =
  [ CommandDescr [ ":t", ":type" ] ["EXPR"] (ExprArg typeOfCmd)
    "Check the type of an expression."
    ""
  , CommandDescr [ ":b", ":browse" ] ["[ MODULE ]"] (ModNameArg browseCmd)
    "Display information about loaded modules."
    (unlines
       [ "With no arguent, :browse shows information about the names in scope."
       , "With an argument M, shows information about the names exported from M"
       ]
    )
  , CommandDescr [ ":version"] [] (NoArg versionCmd)
    "Display the version of this Cryptol executable"
    ""
  , CommandDescr [ ":?", ":help" ] ["[ TOPIC ]"] (HelpArg helpCmd)
    "Display a brief description of a function, type, or command. (e.g. :help :help)"
    (unlines
      [ "TOPIC can be any of:"
      , " * Specific REPL colon-commands (e.g. :help :prove)"
      , " * Functions (e.g. :help join)"
      , " * Infix operators (e.g. :help +)"
      , " * Type constructors (e.g. :help Z)"
      , " * Type constraints (e.g. :help fin)"
      , " * :set-able options (e.g. :help :set base)" ])
  , CommandDescr [ ":s", ":set" ] ["[ OPTION [ = VALUE ] ]"] (OptionArg setOptionCmd)
    "Set an environmental option (:set on its own displays current values)."
    ""
  , CommandDescr [ ":check" ] ["[ EXPR ]"] (ExprArg (qcCmd QCRandom))
    "Use random testing to check that the argument always returns true.\n(If no argument, check all properties.)"
    ""
  , CommandDescr [ ":exhaust" ] ["[ EXPR ]"] (ExprArg (qcCmd QCExhaust))
    "Use exhaustive testing to prove that the argument always returns\ntrue. (If no argument, check all properties.)"
    ""
  , CommandDescr [ ":prove" ] ["[ EXPR ]"] (ExprArg proveCmd)
    "Use an external solver to prove that the argument always returns\ntrue. (If no argument, check all properties.)"
    ""
  , CommandDescr [ ":sat" ] ["[ EXPR ]"] (ExprArg satCmd)
    "Use a solver to find a satisfying assignment for which the argument\nreturns true. (If no argument, find an assignment for all properties.)"
    ""
  , CommandDescr [ ":safe" ] ["[ EXPR ]"] (ExprArg safeCmd)
    "Use an external solver to prove that an expression is safe\n(does not encounter run-time errors) for all inputs."
    ""
  , CommandDescr [ ":debug_specialize" ] ["EXPR"](ExprArg specializeCmd)
    "Do type specialization on a closed expression."
    ""
  , CommandDescr [ ":eval" ] ["EXPR"] (ExprArg refEvalCmd)
    "Evaluate an expression with the reference evaluator."
    ""
  , CommandDescr [ ":ast" ] ["EXPR"] (ExprArg astOfCmd)
    "Print out the pre-typechecked AST of a given term."
    ""
  , CommandDescr [ ":extract-coq" ] [] (NoArg extractCoqCmd)
    "Print out the post-typechecked AST of all currently defined terms,\nin a Coq-parseable format."
    ""
  , CommandDescr [ ":time" ] ["EXPR"] (ExprArg timeCmd)
    "Measure the time it takes to evaluate the given expression."
    (unlines
      [ "The expression will be evaluated many times to get accurate results."
      , "Note that the first evaluation of a binding may take longer due to"
      , "  laziness, and this may affect the reported time. If this is not"
      , "  desired then make sure to evaluate the expression once first before"
      , "  running :time."
      , "The amount of time to spend collecting measurements can be changed"
      , "  with the timeMeasurementPeriod option."
      , "Reports the average wall clock time, CPU time, and cycles."
      , "  (Cycles are in unspecified units that may be CPU cycles.)"
      , "Binds the result to"
      , "  it : { avgTime : Float64"
      , "       , avgCpuTime : Float64"
      , "       , avgCycles : Integer }" ])

  , CommandDescr [ ":set-seed" ] ["SEED"] (OptionArg seedCmd)
      "Seed the random number generator for operations using randomness"
      (unlines
        [ "A seed takes the form of either a single integer or a 4-tuple"
        , "of unsigned 64-bit integers.  Examples of commands using randomness"
        , "are dumpTests and check."
        ])
  , CommandDescr [ ":new-seed"] [] (NoArg newSeedCmd)
      "Randomly generate and set a new seed for the random number generator"
      ""
  , CommandDescr [ ":check-docstrings" ] [] (ModNameArg checkDocStringsCmd)
      "Run the REPL code blocks in the module's docstring comments"
      ""
  ]

commandList :: [CommandDescr]
commandList  =
  nbCommandList ++
  [ CommandDescr [ ":q", ":quit" ] [] (NoArg quitCmd)
    "Exit the REPL."
    ""
  , CommandDescr [ ":l", ":load" ] ["FILE"] (FilenameArg loadCmd)
    "Load a module by filename."
    ""
  , CommandDescr [ ":r", ":reload" ] [] (NoArg reloadCmd)
    "Reload the currently loaded module."
    ""
  , CommandDescr [ ":e", ":edit" ] ["[ FILE ]"] (FilenameArg editCmd)
    "Edit FILE or the currently loaded module."
    ""
  , CommandDescr [ ":!" ] ["COMMAND"] (ShellArg runShellCmd)
    "Execute a command in the shell."
    ""
  , CommandDescr [ ":cd" ] ["DIR"] (FilenameArg cdCmd)
    "Set the current working directory."
    ""
  , CommandDescr [ ":m", ":module" ] ["[ MODULE ]"] (FilenameArg moduleCmd)
    "Load a module by its name."
    ""
  , CommandDescr [ ":f", ":focus" ] ["[ MODULE ]"] (ModNameArg focusCmd)
    "Focus name scope inside a loaded module."
    ""
  , CommandDescr [ ":w", ":writeByteArray" ] ["FILE", "EXPR"] (FileExprArg writeFileCmd)
    "Write data of type 'fin n => [n][8]' to a file."
    ""
  , CommandDescr [ ":readByteArray" ] ["FILE"] (FilenameArg readFileCmd)
    "Read data from a file as type 'fin n => [n][8]', binding\nthe value to variable 'it'."
    ""
  , CommandDescr [ ":dumptests" ] ["FILE", "EXPR"] (FileExprArg dumpTestsCmd)
    (unlines [ "Dump a tab-separated collection of tests for the given"
             , "expression into a file. The first column in each line is"
             , "the expected output, and the remainder are the inputs. The"
             , "number of tests is determined by the \"tests\" option."
             ])
    ""
  , CommandDescr [ ":generate-foreign-header" ] ["FILE"] (FilenameArg genHeaderCmd)
    "Generate a C header file from foreign declarations in a Cryptol file."
    (unlines
      [ "Converts all foreign declarations in the given Cryptol file into C"
      , "function declarations, and writes them to a file with the same name"
      , "but with a .h extension." ])


  , CommandDescr [ ":file-deps" ] [ "FILE" ]
    (FilenameArg (moduleInfoCmd True))
    "Show information about the dependencies of a file"
    ""

  , CommandDescr [ ":module-deps" ] [ "MODULE" ]
    (ModNameArg (moduleInfoCmd False))
    "Show information about the dependencies of a module"
    ""
  ]

genHelp :: [CommandDescr] -> [String]
genHelp cs = map cmdHelp cs
  where
  cmdHelp cmd  = concat $ [ "  ", cmdNames cmd, pad (cmdNames cmd),
                            intercalate ("\n  " ++ pad []) (lines (cHelp cmd)) ]
  cmdNames cmd = intercalate ", " (cNames cmd)
  padding      = 2 + maximum (map (length . cmdNames) cs)
  pad n        = replicate (max 0 (padding - length n)) ' '


-- Command Evaluation ----------------------------------------------------------

-- | Run a command.
runCommand :: Int -> Maybe FilePath -> Command -> REPL CommandResult
runCommand lineNum mbBatch c = case c of

  Command cmd -> cmd lineNum mbBatch `Cryptol.REPL.Monad.catch` handler
    where
    handler re = do
      rPutStrLn ""
      rPrint (pp re)
      return emptyCommandResult { crSuccess = False }

  Unknown cmd -> do
    rPutStrLn ("Unknown command: " ++ cmd)
    return emptyCommandResult { crSuccess = False }

  Ambiguous cmd cmds -> do
    rPutStrLn (cmd ++ " is ambiguous, it could mean one of:")
    rPutStrLn ("\t" ++ intercalate ", " cmds)
    return emptyCommandResult { crSuccess = False }


evalCmd :: String -> Int -> Maybe FilePath -> REPL CommandResult
evalCmd str lineNum mbBatch = do
  ri <- replParseInput str lineNum mbBatch
  case ri of
    P.ExprInput expr -> do
      (val,_ty) <- replEvalExpr expr
      ppOpts <- getPPValOpts
      valDoc <- rEvalRethrow (E.ppValue Concrete ppOpts val)

      -- This is the point where the value gets forced. We deepseq the
      -- pretty-printed representation of it, rather than the value
      -- itself, leaving it up to the pretty-printer to determine how
      -- much of the value to force
      --out <- io $ rethrowEvalError
      --          $ return $!! show $ pp $ E.WithBase ppOpts val

      let value = show valDoc
      rPutStrLn value
      pure emptyCommandResult { crValue = Just value }

    P.LetInput ds -> do
      -- explicitly make this a top-level declaration, so that it will
      -- be generalized if mono-binds is enabled
      replEvalDecls ds
      pure emptyCommandResult

    P.EmptyInput ->
      -- comment or empty input does nothing
      pure emptyCommandResult

  -- parsing and evaluating expressions can fail in many different ways
  `catch` \e -> do
      rPutStrLn ""
      rPrint (pp e)
      pure emptyCommandResult { crSuccess = False }

printCounterexample :: CounterExampleType -> Doc -> [Concrete.Value] -> REPL ()
printCounterexample cexTy exprDoc vs =
  do ppOpts <- getPPValOpts
     -- NB: Use a precedence of 1 here, as `vs` will be pretty-printed as
     -- arguments to the function in `exprDoc`. This ensures that arguments
     -- are parenthesized as needed.
     docs <- mapM (rEval . E.ppValuePrec Concrete ppOpts 1) vs
     let cexRes = case cexTy of
           SafetyViolation    -> [text "~> ERROR"]
           PredicateFalsified -> [text "= False"]
     rPrint $ nest 2 (sep ([exprDoc] ++ docs ++ cexRes))

printSatisfyingModel :: Doc -> [Concrete.Value] -> REPL ()
printSatisfyingModel exprDoc vs =
  do ppOpts <- getPPValOpts
     docs <- mapM (rEval . E.ppValue Concrete ppOpts) vs
     rPrint $ nest 2 (sep ([exprDoc] ++ docs ++ [text "= True"]))


dumpTestsCmd :: FilePath -> String -> (Int,Int) -> Maybe FilePath -> REPL CommandResult
dumpTestsCmd outFile str pos fnm =
  do expr <- replParseExpr str pos fnm
     (val, ty) <- replEvalExpr expr
     ppopts <- getPPValOpts
     testNum <- getKnownUser "tests" :: REPL Int
     tenv <- E.envTypes . M.deEnv <$> getDynEnv
     let tyv = E.evalValType tenv ty
     gens <-
       case TestR.dumpableType tyv of
         Nothing -> raise (TypeNotTestable ty)
         Just gens -> return gens
     tests <- withRandomGen (\g -> io $ TestR.returnTests' g gens val testNum)
     out <- forM tests $
            \(args, x) ->
              do argOut <- mapM (rEval . E.ppValue Concrete ppopts) args
                 resOut <- rEval (E.ppValue Concrete ppopts x)
                 return (renderOneLine resOut ++ "\t" ++ intercalate "\t" (map renderOneLine argOut) ++ "\n")
     writeResult <- io $ X.try (writeFile outFile (concat out))
     case writeResult of
       Right{} -> pure emptyCommandResult
       Left e ->
         do rPutStrLn (X.displayException (e :: X.SomeException))
            pure emptyCommandResult { crSuccess = False }


data QCMode = QCRandom | QCExhaust deriving (Eq, Show)


-- | Randomly test a property, or exhaustively check it if the number
-- of values in the type under test is smaller than the @tests@
-- environment variable, or we specify exhaustive testing.
qcCmd :: QCMode -> String -> (Int,Int) -> Maybe FilePath -> REPL CommandResult
qcCmd qcMode "" _pos _fnm =
  do (xs,disp) <- getPropertyNames
     let nameStr x = show (fixNameDisp disp (pp x))
     if null xs
        then do
          rPutStrLn "There are no properties in scope."
          pure emptyCommandResult { crSuccess = False }
        else do
          let evalProp result (x,d) =
               do let str = nameStr x
                  rPutStr $ "property " ++ str ++ " "
                  let texpr = T.EVar x
                  let schema = M.ifDeclSig d
                  nd <- M.mctxNameDisp <$> getFocusedEnv
                  let doc = fixNameDisp nd (pp texpr)
                  testReport <- qcExpr qcMode doc texpr schema
                  pure $! result && isPass (reportResult testReport)
          success <- foldM evalProp True xs
          pure emptyCommandResult { crSuccess = success }

qcCmd qcMode str pos fnm =
  do expr <- replParseExpr str pos fnm
     (_,texpr,schema) <- replCheckExpr expr
     nd <- M.mctxNameDisp <$> getFocusedEnv
     let doc = fixNameDisp nd (ppPrec 3 expr) -- function application has precedence 3
     testReport <- qcExpr qcMode doc texpr schema
     pure emptyCommandResult { crSuccess = isPass (reportResult testReport) }


data TestReport = TestReport
  { reportExpr :: Doc
  , reportResult :: TestResult
  , reportTestsRun :: Integer
  , reportTestsPossible :: Maybe Integer
  }

qcExpr ::
  QCMode ->
  Doc ->
  T.Expr ->
  T.Schema ->
  REPL TestReport
qcExpr qcMode exprDoc texpr schema =
  do (val,ty) <- replEvalCheckedExpr texpr schema >>= \mb_res -> case mb_res of
       Just res -> pure res
       -- If instance is not found, doesn't necessarily mean that there is no instance.
       -- And due to nondeterminism in result from the solver (for finding solution to
       -- numeric type constraints), `:check` can get to this exception sometimes, but
       -- successfully find an instance and test with it other times.
       Nothing -> raise (InstantiationsNotFound schema)
     testNum <- (toInteger :: Int -> Integer) <$> getKnownUser "tests"
     tenv <- E.envTypes . M.deEnv <$> getDynEnv
     let tyv = E.evalValType tenv ty
     -- tv has already had polymorphism instantiated
     percentRef <- io $ newIORef Nothing
     testsRef <- io $ newIORef 0

     case testableType tyv of
       Just (Just sz,tys,vss,_gens) | qcMode == QCExhaust || sz <= testNum -> do
            rPutStrLn "Using exhaustive testing."
            prt testingMsg
            (res,num) <-
                  Ex.catch (exhaustiveTests (\n -> ppProgress percentRef testsRef n sz)
                                            val vss)
                         (\ex -> do rPutStrLn "\nTest interrupted..."
                                    num <- io $ readIORef testsRef
                                    let report = TestReport exprDoc Pass num (Just sz)
                                    ppReport tys False report
                                    rPutStrLn $ interruptedExhaust num sz
                                    Ex.throwM (ex :: Ex.SomeException))
            let report = TestReport exprDoc res num (Just sz)
            delProgress
            delTesting
            ppReport tys True report
            return report

       Just (sz,tys,_,gens) | qcMode == QCRandom -> do
            rPutStrLn "Using random testing."
            prt testingMsg
            (res,num) <-
              withRandomGen
                (randomTests' (\n -> ppProgress percentRef testsRef n testNum)
                                      testNum val gens)
              `Ex.catch` (\ex -> do rPutStrLn "\nTest interrupted..."
                                    num <- io $ readIORef testsRef
                                    let report = TestReport exprDoc Pass num sz
                                    ppReport tys False report
                                    case sz of
                                      Just n -> rPutStrLn $ coverageString num n
                                      _ -> return ()
                                    Ex.throwM (ex :: Ex.SomeException))
            let report = TestReport exprDoc res num sz
            delProgress
            delTesting
            ppReport tys False report
            case sz of
              Just n | isPass res -> rPutStrLn $ coverageString testNum n
              _ -> return ()
            return report
       _ -> raise (TypeNotTestable ty)

  where
  testingMsg = "Testing... "

  interruptedExhaust testNum sz =
     let percent = (100.0 :: Double) * (fromInteger testNum) / fromInteger sz
         showValNum
            | sz > 2 ^ (20::Integer) =
              "2^^" ++ show (lg2 sz)
            | otherwise = show sz
      in "Test coverage: "
            ++ showFFloat (Just 2) percent "% ("
            ++ show testNum ++ " of "
            ++ showValNum
            ++ " values)"

  coverageString testNum sz =
     let (percent, expectedUnique) = expectedCoverage testNum sz
         showValNum
           | sz > 2 ^ (20::Integer) =
             "2^^" ++ show (lg2 sz)
           | otherwise = show sz
     in "Expected test coverage: "
       ++ showFFloat (Just 2) percent "% ("
       ++ showFFloat (Just 0) expectedUnique " of "
       ++ showValNum
       ++ " values)"

  totProgressWidth = 4    -- 100%

  lg2 :: Integer -> Integer
  lg2 x | x >= 2^(1024::Int) = 1024 + lg2 (x `div` 2^(1024::Int))
        | x == 0       = 0
        | otherwise    = let valNumD = fromInteger x :: Double
                         in round $ logBase 2 valNumD :: Integer

  prt msg   = rPutStr msg >> io (hFlush stdout)

  ppProgress percentRef testsRef this tot =
    do io $ writeIORef testsRef this
       let percent = show (div (100 * this) tot) ++ "%"
           width   = length percent
           pad     = replicate (totProgressWidth - width) ' '
       unlessBatch $
         do oldPercent <- io $ readIORef percentRef
            case oldPercent of
              Nothing ->
                do io $ writeIORef percentRef (Just percent)
                   prt (pad ++ percent)
              Just p | p /= percent ->
                do io $ writeIORef percentRef (Just percent)
                   delProgress
                   prt (pad ++ percent)
              _ -> return ()

  del n       = unlessBatch
              $ prt (replicate n '\BS' ++ replicate n ' ' ++ replicate n '\BS')
  delTesting  = del (length testingMsg)
  delProgress = del totProgressWidth


ppReport :: [E.TValue] -> Bool -> TestReport -> REPL ()
ppReport _tys isExhaustive (TestReport _exprDoc Pass testNum _testPossible) =
    do rPutStrLn ("Passed " ++ show testNum ++ " tests.")
       when isExhaustive (rPutStrLn "Q.E.D.")
ppReport tys _ (TestReport exprDoc failure _testNum _testPossible) =
    do ppFailure tys exprDoc failure

ppFailure :: [E.TValue] -> Doc -> TestResult -> REPL ()
ppFailure tys exprDoc failure = do
    ~(EnvBool showEx) <- getUser "showExamples"

    vs <- case failure of
            FailFalse vs ->
              do rPutStrLn "Counterexample"
                 when showEx (printCounterexample PredicateFalsified exprDoc vs)
                 pure vs
            FailError err vs
              | null vs || not showEx ->
                do rPutStrLn "ERROR"
                   rPrint (pp err)
                   pure vs
              | otherwise ->
                do rPutStrLn "ERROR for the following inputs:"
                   printCounterexample SafetyViolation exprDoc vs
                   rPrint (pp err)
                   pure vs

            Pass -> panic "Cryptol.REPL.Command" ["unexpected Test.Pass"]

    -- bind the 'it' variable
    case (tys,vs) of
      ([t],[v]) -> bindItVariableVal t v
      _ -> let fs = [ M.packIdent ("arg" ++ show (i::Int)) | i <- [ 1 .. ] ]
               t = E.TVRec (recordFromFields (zip fs tys))
               v = E.VRecord (recordFromFields (zip fs (map return vs)))
           in bindItVariableVal t v


-- | This function computes the expected coverage percentage and
-- expected number of unique test vectors when using random testing.
--
-- The expected test coverage proportion is:
--  @1 - ((n-1)/n)^k@
--
-- This formula takes into account the fact that test vectors are chosen
-- uniformly at random _with replacement_, and thus the same vectors
-- may be generated multiple times.  If the test vectors were chosen
-- randomly without replacement, the proportion would instead be @k/n@.
--
-- We compute raising to the @k@ power in the log domain to improve
-- numerical precision. The equivalant comptutation is:
--   @-expm1( k * log1p (-1/n) )@
--
-- Where @expm1(x) = exp(x) - 1@ and @log1p(x) = log(1 + x)@.
--
-- However, if @sz@ is large enough, even carefully preserving
-- precision may not be enough to get sensible results.  In such
-- situations, we expect the naive approximation @k/n@ to be very
-- close to accurate and the expected number of unique values is
-- essentially equal to the number of tests.
expectedCoverage :: Integer -> Integer -> (Double, Double)
expectedCoverage testNum sz =
    -- If the Double computation has enough precision, use the
    --  "with replacement" formula.
    if testNum > 0 && proportion > 0 then
       (100.0 * proportion, szD * proportion)
    else
       (100.0 * naiveProportion, numD)

  where
   szD :: Double
   szD = fromInteger sz

   numD :: Double
   numD = fromIntegral testNum

   naiveProportion = numD / szD

   proportion = negate (expm1 (numD * log1p (negate (recip szD))))

satCmd, proveCmd :: String -> (Int,Int) -> Maybe FilePath -> REPL CommandResult
satCmd = cmdProveSat True
proveCmd = cmdProveSat False

showProverStats :: Maybe String -> ProverStats -> REPL ()
showProverStats mprover stat = rPutStrLn msg
  where

  msg = "(Total Elapsed Time: " ++ SBV.showTDiff stat ++
        maybe "" (\p -> ", using " ++ show p) mprover ++ ")"

rethrowErrorCall :: REPL a -> REPL a
rethrowErrorCall m = REPL (\r -> unREPL m r `X.catches` hs)
  where
    hs =
      [ X.Handler $ \ (X.ErrorCallWithLocation s _) -> X.throwIO (SBVError s)
      , X.Handler $ \ e -> X.throwIO (SBVException e)
      , X.Handler $ \ e -> X.throwIO (SBVPortfolioException e)
      , X.Handler $ \ e -> X.throwIO (W4Exception e)
      ]

-- | Attempts to prove the given term is safe for all inputs
safeCmd :: String -> (Int,Int) -> Maybe FilePath -> REPL CommandResult
safeCmd str pos fnm = do
  proverName <- getKnownUser "prover"
  fileName   <- getKnownUser "smtFile"
  let mfile = if fileName == "-" then Nothing else Just fileName
  pexpr <- replParseExpr str pos fnm
  nd <- M.mctxNameDisp <$> getFocusedEnv
  let exprDoc = fixNameDisp nd (ppPrec 3 pexpr) -- function application has precedence 3

  let rng = fromMaybe (mkInteractiveRange pos fnm) (getLoc pexpr)
  (_,texpr,schema) <- replCheckExpr pexpr

  if proverName `elem` ["offline","sbv-offline","w4-offline"] then
    do success <- offlineProveSat proverName SafetyQuery texpr schema mfile
       pure emptyCommandResult { crSuccess = success }
  else
     do (firstProver,result,stats) <- rethrowErrorCall (onlineProveSat proverName SafetyQuery texpr schema mfile)
        cmdResult <- case result of
          EmptyResult         ->
            panic "REPL.Command" [ "got EmptyResult for online prover query" ]

          ProverError msg ->
            do rPutStrLn msg
               pure emptyCommandResult { crSuccess = False }

          ThmResult _ts ->
            do rPutStrLn "Safe"
               pure emptyCommandResult

          CounterExample cexType tevs -> do
            rPutStrLn "Counterexample"
            let tes = map ( \(t,e,_) -> (t,e)) tevs
                vs  = map ( \(_,_,v) -> v)     tevs

            (t,e) <- mkSolverResult "counterexample" rng False (Right tes)

            ~(EnvBool yes) <- getUser "showExamples"
            when yes $ printCounterexample cexType exprDoc vs
            when yes $ printSafetyViolation texpr schema vs

            void $ bindItVariable t e

            pure emptyCommandResult { crSuccess = False }

          AllSatResult _ -> do
            panic "REPL.Command" ["Unexpected AllSAtResult for ':safe' call"]

        seeStats <- getUserShowProverStats
        when seeStats (showProverStats firstProver stats)
        pure cmdResult


-- | Console-specific version of 'proveSat'. Prints output to the
-- console, and binds the @it@ variable to a record whose form depends
-- on the expression given. See ticket #66 for a discussion of this
-- design.
cmdProveSat :: Bool -> String -> (Int,Int) -> Maybe FilePath -> REPL CommandResult
cmdProveSat isSat "" _pos _fnm =
  do (xs,disp) <- getPropertyNames
     let nameStr x = show (fixNameDisp disp (pp x))
     if null xs
        then do
          rPutStrLn "There are no properties in scope."
          pure emptyCommandResult { crSuccess = False }
        else do
          let check acc (x,d) = do
                let str = nameStr x
                if isSat
                  then rPutStr $ ":sat "   ++ str ++ "\n\t"
                  else rPutStr $ ":prove " ++ str ++ "\n\t"
                let texpr = T.EVar x
                let schema = M.ifDeclSig d
                nd <- M.mctxNameDisp <$> getFocusedEnv
                let doc = fixNameDisp nd (pp texpr)
                success <- proveSatExpr isSat (M.nameLoc x) doc texpr schema
                pure $! acc && success
          success <- foldM check True xs
          pure emptyCommandResult { crSuccess = success }


cmdProveSat isSat str pos fnm = do
  pexpr <- replParseExpr str pos fnm
  nd <- M.mctxNameDisp <$> getFocusedEnv
  let doc = fixNameDisp nd (ppPrec 3 pexpr) -- function application has precedence 3
  (_,texpr,schema) <- replCheckExpr pexpr
  let rng = fromMaybe (mkInteractiveRange pos fnm) (getLoc pexpr)
  success <- proveSatExpr isSat rng doc texpr schema
  pure emptyCommandResult { crSuccess = success }

proveSatExpr ::
  Bool ->
  Range ->
  Doc ->
  T.Expr ->
  T.Schema ->
  REPL Bool
proveSatExpr isSat rng exprDoc texpr schema = do
  let cexStr | isSat = "satisfying assignment"
             | otherwise = "counterexample"
  qtype <- if isSat then SatQuery <$> getUserSatNum else pure ProveQuery
  proverName <- getKnownUser "prover"
  fileName   <- getKnownUser "smtFile"
  let mfile = if fileName == "-" then Nothing else Just fileName

  if proverName `elem` ["offline","sbv-offline","w4-offline"] then
     offlineProveSat proverName qtype texpr schema mfile
  else
     do (firstProver,result,stats) <- rethrowErrorCall (onlineProveSat proverName qtype texpr schema mfile)
        success <- case result of
          EmptyResult         ->
            panic "REPL.Command" [ "got EmptyResult for online prover query" ]

          ProverError msg -> False <$ rPutStrLn msg

          ThmResult ts -> do
            rPutStrLn (if isSat then "Unsatisfiable" else "Q.E.D.")
            (t, e) <- mkSolverResult cexStr rng (not isSat) (Left ts)
            void $ bindItVariable t e
            pure (not isSat)

          CounterExample cexType tevs -> do
            rPutStrLn "Counterexample"
            let tes = map ( \(t,e,_) -> (t,e)) tevs
                vs  = map ( \(_,_,v) -> v)     tevs

            (t,e) <- mkSolverResult cexStr rng isSat (Right tes)

            ~(EnvBool yes) <- getUser "showExamples"
            when yes $ printCounterexample cexType exprDoc vs

            -- if there's a safety violation, evalute the counterexample to
            -- find and print the actual concrete error
            case cexType of
              SafetyViolation -> when yes $ printSafetyViolation texpr schema vs
              _ -> return ()

            void $ bindItVariable t e
            pure False

          AllSatResult tevss -> do
            rPutStrLn "Satisfiable"
            let tess = map (map $ \(t,e,_) -> (t,e)) tevss
                vss  = map (map $ \(_,_,v) -> v)     tevss
            resultRecs <- mapM (mkSolverResult cexStr rng isSat . Right) tess
            let collectTes tes = (t, es)
                  where
                    (ts, es) = unzip tes
                    t = case nub ts of
                          [t'] -> t'
                          _ -> panic "REPL.Command.onlineProveSat"
                                 [ "satisfying assignments with different types" ]
                (ty, exprs) =
                  case resultRecs of
                    [] -> panic "REPL.Command.onlineProveSat"
                            [ "no satisfying assignments after mkSolverResult" ]
                    [(t, e)] -> (t, [e])
                    _        -> collectTes resultRecs

            ~(EnvBool yes) <- getUser "showExamples"
            when yes $ forM_ vss (printSatisfyingModel exprDoc)

            let numModels = length tevss
            when (numModels > 1) (rPutStrLn ("Models found: " ++ show numModels))

            case exprs of
              [e] -> void $ bindItVariable ty e
              _   -> bindItVariables ty exprs

            pure True

        seeStats <- getUserShowProverStats
        when seeStats (showProverStats firstProver stats)
        pure success


printSafetyViolation :: T.Expr -> T.Schema -> [E.GenValue Concrete] -> REPL ()
printSafetyViolation texpr schema vs =
    catch
      (do fn <- replEvalCheckedExpr texpr schema >>= \mb_res -> case mb_res of
            Just (fn, _) -> pure fn
            Nothing -> raise (EvalPolyError schema)
          rEval (E.forceValue =<< foldM (\f v -> E.fromVFun Concrete f (pure v)) fn vs))
      (\case
          EvalError eex -> rPutStrLn (show (pp eex))
          ex -> raise ex)

onlineProveSat ::
  String ->
  QueryType ->
  T.Expr ->
  T.Schema ->
  Maybe FilePath ->
  REPL (Maybe String,ProverResult,ProverStats)
onlineProveSat proverName qtype expr schema mfile = do
  verbose <- getKnownUser "debug"
  modelValidate <- getUserProverValidate
  validEvalContext expr
  validEvalContext schema
  decls <- fmap M.deDecls getDynEnv
  timing <- io (newIORef 0)
  ~(EnvBool ignoreSafety) <- getUser "ignoreSafety"
  ~(EnvNum timeoutSec) <- getUser "proverTimeout"
  let cmd = ProverCommand {
          pcQueryType    = qtype
        , pcProverName   = proverName
        , pcVerbose      = verbose
        , pcValidate     = modelValidate
        , pcProverStats  = timing
        , pcExtraDecls   = decls
        , pcSmtFile      = mfile
        , pcExpr         = expr
        , pcSchema       = schema
        , pcIgnoreSafety = ignoreSafety
        }
  (firstProver, res) <- getProverConfig >>= \case
       Left sbvCfg -> liftModuleCmd $ SBV.satProve sbvCfg timeoutSec cmd
       Right w4Cfg ->
         do ~(EnvBool hashConsing) <- getUser "hashConsing"
            ~(EnvBool warnUninterp) <- getUser "warnUninterp"
            liftModuleCmd $ W4.satProve w4Cfg hashConsing warnUninterp timeoutSec cmd

  stas <- io (readIORef timing)
  return (firstProver,res,stas)

offlineProveSat :: String -> QueryType -> T.Expr -> T.Schema -> Maybe FilePath -> REPL Bool
offlineProveSat proverName qtype expr schema mfile = do
  verbose <- getKnownUser "debug"
  modelValidate <- getUserProverValidate

  decls <- fmap M.deDecls getDynEnv
  timing <- io (newIORef 0)
  ~(EnvBool ignoreSafety) <- getUser "ignoreSafety"
  let cmd = ProverCommand {
          pcQueryType    = qtype
        , pcProverName   = proverName
        , pcVerbose      = verbose
        , pcValidate     = modelValidate
        , pcProverStats  = timing
        , pcExtraDecls   = decls
        , pcSmtFile      = mfile
        , pcExpr         = expr
        , pcSchema       = schema
        , pcIgnoreSafety = ignoreSafety
        }

  put <- getPutStr
  let putLn x = put (x ++ "\n")
  let displayMsg =
        do let filename = fromMaybe "standard output" mfile
           let satWord = case qtype of
                           SatQuery _  -> "satisfiability"
                           ProveQuery  -> "validity"
                           SafetyQuery -> "safety"
           putLn $
               "Writing to SMT-Lib file " ++ filename ++ "..."
           putLn $
             "To determine the " ++ satWord ++
             " of the expression, use an external SMT solver."

  getProverConfig >>= \case
    Left sbvCfg ->
      do result <- liftModuleCmd $ SBV.satProveOffline sbvCfg cmd
         case result of
           Left msg -> False <$ rPutStrLn msg
           Right smtlib -> do
             io $ displayMsg
             case mfile of
               Just path -> io $ writeFile path smtlib
               Nothing -> rPutStr smtlib
             pure True

    Right _w4Cfg ->
      do ~(EnvBool hashConsing) <- getUser "hashConsing"
         ~(EnvBool warnUninterp) <- getUser "warnUninterp"
         result <- liftModuleCmd $ W4.satProveOffline hashConsing warnUninterp cmd $ \f ->
                     do displayMsg
                        case mfile of
                          Just path ->
                            X.bracket (openFile path WriteMode) hClose f
                          Nothing ->
                            withRWTempFile "smtOutput.tmp" $ \h ->
                              do f h
                                 hSeek h AbsoluteSeek 0
                                 hGetContents h >>= put

         case result of
           Just msg -> rPutStrLn msg
           Nothing -> return ()
         pure True


rIdent :: M.Ident
rIdent  = M.packIdent "result"

-- | Make a type/expression pair that is suitable for binding to @it@
-- after running @:sat@ or @:prove@
mkSolverResult ::
  String ->
  Range ->
  Bool ->
  Either [E.TValue] [(E.TValue, T.Expr)] ->
  REPL (E.TValue, T.Expr)
mkSolverResult thing rng result earg =
  do prims <- getPrimMap
     let addError t = (t, T.ELocated rng (T.eError prims (E.tValTy t) ("no " ++ thing ++ " available")))

         argF = case earg of
                  Left ts   -> mkArgs (map addError ts)
                  Right tes -> mkArgs tes

         eTrue  = T.ePrim prims (M.prelPrim "True")
         eFalse = T.ePrim prims (M.prelPrim "False")
         resultE = if result then eTrue else eFalse

         rty = E.TVRec (recordFromFields $ [(rIdent, E.TVBit)] ++ map fst argF)
         re  = T.ERec (recordFromFields $ [(rIdent, resultE)] ++ map snd argF)

     return (rty, re)
  where
  mkArgs tes = zipWith mkArg [1 :: Int ..] tes
    where
    mkArg n (t,e) =
      let argName = M.packIdent ("arg" ++ show n)
       in ((argName,t),(argName,e))

specializeCmd :: String -> (Int,Int) -> Maybe FilePath -> REPL CommandResult
specializeCmd str pos fnm = do
  parseExpr <- replParseExpr str pos fnm
  (_, expr, schema) <- replCheckExpr parseExpr
  spexpr <- replSpecExpr expr
  rPutStrLn  "Expression type:"
  rPrint    $ pp schema
  rPutStrLn  "Original expression:"
  rPutStrLn $ dump expr
  rPutStrLn  "Specialized expression:"
  let value = dump spexpr
  rPutStrLn value
  pure emptyCommandResult { crValue = Just value }

refEvalCmd :: String -> (Int,Int) -> Maybe FilePath -> REPL CommandResult
refEvalCmd str pos fnm = do
  parseExpr <- replParseExpr str pos fnm
  (_, expr, schema) <- replCheckExpr parseExpr
  validEvalContext expr
  validEvalContext schema
  val <- liftModuleCmd (rethrowEvalError . R.evaluate expr)
  opts <- getPPValOpts
  let value = show (R.ppEValue opts val)
  rPutStrLn value
  pure emptyCommandResult { crValue = Just value }

astOfCmd :: String -> (Int,Int) -> Maybe FilePath -> REPL CommandResult
astOfCmd str pos fnm = do
 expr <- replParseExpr str pos fnm
 (re,_,_) <- replCheckExpr (P.noPos expr)
 rPrint (fmap M.nameUnique re)
 pure emptyCommandResult

extractCoqCmd :: REPL CommandResult
extractCoqCmd = do
  me <- getModuleEnv
  rPrint $ T.showParseable $ concatMap T.mDecls $ M.loadedModules me
  pure emptyCommandResult

typeOfCmd :: String -> (Int,Int) -> Maybe FilePath -> REPL CommandResult
typeOfCmd str pos fnm = do

  expr         <- replParseExpr str pos fnm
  (_re,def,sig) <- replCheckExpr expr

  -- XXX need more warnings from the module system
  whenDebug (rPutStrLn (dump def))
  fDisp <- M.mctxNameDisp <$> getFocusedEnv
  -- type annotation ':' has precedence 2
  let output = show $ runDoc fDisp $ group $ hang
                 (ppPrec 2 expr <+> text ":") 2 (pp sig)

  rPutStrLn output
  pure emptyCommandResult { crType = Just output }

timeCmd :: String -> (Int, Int) -> Maybe FilePath -> REPL CommandResult
timeCmd str pos fnm = do
  period <- getKnownUser "timeMeasurementPeriod" :: REPL Int
  quiet <- getKnownUser "timeQuiet"
  unless quiet $
    rPutStrLn $ "Measuring for " ++ show period ++ " seconds"
  pExpr <- replParseExpr str pos fnm
  (_, def, sig) <- replCheckExpr pExpr
  replPrepareCheckedExpr def sig >>= \case
    Nothing -> raise (EvalPolyError sig)
    Just (_, expr) -> do
      Bench.BenchmarkStats {..} <- liftModuleCmd
        (rethrowEvalError . M.benchmarkExpr (fromIntegral period) expr)
      unless quiet $
        rPutStrLn $ "Avg time: " ++ Bench.secs benchAvgTime
             ++ "    Avg CPU time: " ++ Bench.secs benchAvgCpuTime
             ++ "    Avg cycles: " ++ show benchAvgCycles
      let mkStatsRec time cpuTime cycles = recordFromFields
            [("avgTime", time), ("avgCpuTime", cpuTime), ("avgCycles", cycles)]
          itType = E.TVRec $ mkStatsRec E.tvFloat64 E.tvFloat64 E.TVInteger
          itVal = E.VRecord $ mkStatsRec
            (pure $ E.VFloat $ FP.floatFromDouble benchAvgTime)
            (pure $ E.VFloat $ FP.floatFromDouble benchAvgCpuTime)
            (pure $ E.VInteger $ toInteger benchAvgCycles)
      bindItVariableVal itType itVal
  pure emptyCommandResult -- TODO: gather timing outputs

readFileCmd :: FilePath -> REPL CommandResult
readFileCmd fp = do
  bytes <- replReadFile fp (\err -> rPutStrLn (show err) >> return Nothing)
  case bytes of
    Nothing -> return emptyCommandResult { crSuccess = False }
    Just bs ->
      do pm <- getPrimMap
         let val = byteStringToInteger bs
         let len = BS.length bs
         let split = T.ePrim pm (M.prelPrim "split")
         let number = T.ePrim pm (M.prelPrim "number")
         let f = T.EProofApp (foldl T.ETApp split [T.tNum len, T.tNum (8::Integer), T.tBit])
         let t = T.tWord (T.tNum (toInteger len * 8))
         let x = T.EProofApp (T.ETApp (T.ETApp number (T.tNum val)) t)
         let expr = T.EApp f x
         void $ bindItVariable (E.TVSeq (toInteger len) (E.TVSeq 8 E.TVBit)) expr
         pure emptyCommandResult

-- | Convert a 'ByteString' (big-endian) of length @n@ to an 'Integer'
-- with @8*n@ bits. This function uses a balanced binary fold to
-- achieve /O(n log n)/ total memory allocation and run-time, in
-- contrast to the /O(n^2)/ that would be required by a naive
-- left-fold.
byteStringToInteger :: BS.ByteString -> Integer
-- byteStringToInteger = BS.foldl' (\a b -> a `shiftL` 8 .|. toInteger b) 0
byteStringToInteger bs
  | l == 0 = 0
  | l == 1 = toInteger (BS.head bs)
  | otherwise = x1 `shiftL` (l2 * 8) .|. x2
  where
    l = BS.length bs
    l1 = l `div` 2
    l2 = l - l1
    (bs1, bs2) = BS.splitAt l1 bs
    x1 = byteStringToInteger bs1
    x2 = byteStringToInteger bs2

writeFileCmd :: FilePath -> String -> (Int,Int) -> Maybe FilePath -> REPL CommandResult
writeFileCmd file str pos fnm = do
  expr         <- replParseExpr str pos fnm
  (val,ty)     <- replEvalExpr expr
  if not (tIsByteSeq ty)
    then do
      rPrint $ "Cannot write expression of types other than [n][8]."
              <+> "Type was: " <+> pp ty
      pure emptyCommandResult { crSuccess = False }
    else do
      bytes <- serializeValue val
      replWriteFile file bytes
 where
  tIsByteSeq x = maybe False
                       (tIsByte . snd)
                       (T.tIsSeq x)
  tIsByte    x = maybe False
                       (\(n,b) -> T.tIsBit b && T.tIsNum n == Just 8)
                       (T.tIsSeq x)
  serializeValue (E.VSeq n vs) = do
    ws <- rEval
            (mapM (>>= E.fromVWord Concrete "serializeValue") $ E.enumerateSeqMap n vs)
    return $ BS.pack $ map serializeByte ws
  serializeValue _             =
    panic "Cryptol.REPL.Command.writeFileCmd"
      ["Impossible: Non-VSeq value of type [n][8]."]
  serializeByte (Concrete.BV _ v) = fromIntegral (v .&. 0xFF)


rEval :: E.Eval a -> REPL a
rEval m = io (E.runEval mempty m)

rEvalRethrow :: E.Eval a -> REPL a
rEvalRethrow m = io $ rethrowEvalError $ E.runEval mempty m

reloadCmd :: REPL CommandResult
reloadCmd  = do
  mb <- getLoadedMod
  case mb of
    Just lm  ->
      case lPath lm of
        M.InFile f -> loadCmd f
        _ -> return emptyCommandResult
    Nothing -> return emptyCommandResult


editCmd :: String -> REPL CommandResult
editCmd path =
  do mbE <- getEditPath
     mbL <- getLoadedMod
     if not (null path)
        then do when (isNothing mbL)
                  $ setLoadedMod LoadedModule { lFocus = Nothing
                                              , lPath = M.InFile path }
                doEdit path
        else case msum [ M.InFile <$> mbE, lPath <$> mbL ] of
               Nothing ->
                do rPutStrLn "No filed to edit."
                   pure emptyCommandResult { crSuccess = False }
               Just p  ->
                  case p of
                    M.InFile f   -> doEdit f
                    M.InMem l bs -> do
                      _ <- withROTempFile l bs replEdit
                      pure emptyCommandResult
  where
  doEdit p =
    do setEditPath p
       _ <- replEdit p
       reloadCmd

withRWTempFile :: String -> (Handle -> IO a) -> IO a
withRWTempFile name k =
  X.bracket
    (do tmp <- getTemporaryDirectory
        let esc c = if isAscii c && isAlphaNum c then c else '_'
        openTempFile tmp (map esc name))
    (\(nm,h) -> hClose h >> removeFile nm)
    (k . snd)

withROTempFile :: String -> ByteString -> (FilePath -> REPL a) -> REPL a
withROTempFile name cnt k =
  do (path,h) <- mkTmp
     do mkFile path h
        k path
      `finally` liftIO (do hClose h
                           removeFile path)
  where
  mkTmp =
    liftIO $
    do tmp <- getTemporaryDirectory
       let esc c = if isAscii c && isAlphaNum c then c else '_'
       openTempFile tmp (map esc name ++ ".cry")

  mkFile path h =
    liftIO $
    do BS8.hPutStrLn h cnt
       hFlush h
       setPermissions path (setOwnerReadable True emptyPermissions)



moduleCmd :: String -> REPL CommandResult
moduleCmd modString
  | null modString = return emptyCommandResult
  | otherwise      = do
    case parseModName modString of
      Just m ->
        do mpath <- liftModuleCmd (M.findModule m)
           case mpath of
             M.InFile file ->
               do setEditPath file
                  setLoadedMod LoadedModule { lFocus = Just (P.ImpTop m), lPath = mpath }
                  loadHelper (M.loadModuleByPath file)
             M.InMem {} -> loadHelper (M.loadModuleByName m)
      Nothing ->
        do rPutStrLn "Invalid module name."
           pure emptyCommandResult { crSuccess = False }


focusCmd :: String -> REPL CommandResult
focusCmd modString
  | null modString =
   do mb <- getLoadedMod
      case mb of
        Nothing -> pure ()
        Just lm ->
          case lName lm of
            Nothing -> pure ()
            Just name -> do
              let top = P.ImpTop name
              liftModuleCmd (`M.runModuleM` M.setFocusedModule top)
              setLoadedMod lm { lFocus = Just top }
      pure emptyCommandResult

  | otherwise =
    case parseImpName modString of
      Nothing ->
        do rPutStrLn "Invalid module name."
           pure emptyCommandResult { crSuccess = False }
    
      Just pimpName -> do
        impName <- liftModuleCmd (setFocusedModuleCmd pimpName)
        mb <- getLoadedMod
        case mb of
          Nothing -> pure ()
          Just lm -> setLoadedMod lm { lFocus = Just impName }
        pure emptyCommandResult

setFocusedModuleCmd :: P.ImpName P.PName -> M.ModuleCmd (P.ImpName T.Name)
setFocusedModuleCmd pimpName i = M.runModuleM i $
 do impName <- M.renameImpNameInCurrentEnv pimpName
    M.setFocusedModule impName
    pure impName

loadPrelude :: REPL ()
loadPrelude  = void $ moduleCmd $ show $ pp M.preludeName

loadCmd :: FilePath -> REPL CommandResult
loadCmd path
  | null path = return emptyCommandResult

  -- when `:load`, the edit and focused paths become the parameter
  | otherwise = do setEditPath path
                   setLoadedMod LoadedModule { lFocus = Nothing
                                             , lPath = M.InFile path
                                             }
                   loadHelper (M.loadModuleByPath path)

loadHelper :: M.ModuleCmd (M.ModulePath,T.TCTopEntity) -> REPL CommandResult
loadHelper how =
  do clearLoadedMod
     (path,ent) <- liftModuleCmd how

     whenDebug (rPutStrLn (dump ent))
     setLoadedMod LoadedModule
        { lFocus = Just (P.ImpTop (T.tcTopEntitytName ent))
        , lPath = path
        }
     -- after a successful load, the current module becomes the edit target
     case path of
       M.InFile f -> setEditPath f
       M.InMem {} -> clearEditPath
     setDynEnv mempty
     pure emptyCommandResult

genHeaderCmd :: FilePath -> REPL CommandResult
genHeaderCmd path
  | null path = pure emptyCommandResult
  | otherwise = do
    (mPath, m) <- liftModuleCmd $ M.checkModuleByPath path
    let decls = case m of
                   T.TCTopModule mo -> findForeignDecls mo
                   T.TCTopSignature {} -> []
    if null decls
      then do
        rPutStrLn $ "No foreign declarations in " ++ pretty mPath
        pure emptyCommandResult { crSuccess = False }
      else do
        let header = generateForeignHeader decls
        case mPath of
          M.InFile p -> do
            let hPath = p -<.> "h"
            rPutStrLn $ "Writing header to " ++ hPath
            replWriteFileString hPath header
          M.InMem _ _ ->
            do rPutStrLn header
               pure emptyCommandResult

versionCmd :: REPL CommandResult
versionCmd = do
  displayVersion rPutStrLn
  pure emptyCommandResult

quitCmd :: REPL CommandResult
quitCmd  = do
  stop
  pure emptyCommandResult

browseCmd :: String -> REPL CommandResult
browseCmd input
  | null input =
    do fe <- getFocusedEnv
       rPrint (browseModContext BrowseInScope fe)
       pure emptyCommandResult
  | otherwise =
    case parseImpName input of
      Nothing -> do
        rPutStrLn "Invalid module name"
        pure emptyCommandResult { crSuccess = False }
      Just pimpName -> do
        impName <- liftModuleCmd (`M.runModuleM` M.renameImpNameInCurrentEnv pimpName)
        mb <- M.modContextOf impName <$> getModuleEnv
        case mb of
          Nothing -> do
            rPutStrLn ("Module " ++ show input ++ " is not loaded")
            pure emptyCommandResult { crSuccess = False }
          Just fe -> do
            rPrint (browseModContext BrowseExported fe)
            pure emptyCommandResult


setOptionCmd :: String -> REPL CommandResult
setOptionCmd str
  | Just value <- mbValue = setUser key value >>= \success -> pure emptyCommandResult { crSuccess = success }
  | null key              = mapM_ (describe . optName) (leaves userOptions) >> pure emptyCommandResult
  | otherwise             = describe key
  where
  (before,after) = break (== '=') str
  key   = trim before
  mbValue = case after of
              _ : stuff -> Just (trim stuff)
              _         -> Nothing

  describe k = do
    ev <- tryGetUser k
    case ev of
      Just v  -> do rPutStrLn (k ++ " = " ++ showEnvVal v)
                    pure emptyCommandResult
      Nothing -> do rPutStrLn ("Unknown user option: `" ++ k ++ "`")
                    when (any isSpace k) $ do
                      let (k1, k2) = break isSpace k
                      rPutStrLn ("Did you mean: `:set " ++ k1 ++ " =" ++ k2 ++ "`?")
                    pure emptyCommandResult { crSuccess = False }

showEnvVal :: EnvVal -> String
showEnvVal ev =
  case ev of
    EnvString s   -> s
    EnvProg p as  -> intercalate " " (p:as)
    EnvNum n      -> show n
    EnvBool True  -> "on"
    EnvBool False -> "off"

-- XXX at the moment, this can only look at declarations.
helpCmd :: String -> REPL CommandResult
helpCmd cmd
  | null cmd  = emptyCommandResult <$ mapM_ rPutStrLn (genHelp commandList)
  | cmd0 : args <- words cmd, ":" `isPrefixOf` cmd0 =
    case findCommandExact cmd0 of
      []  -> runCommand 1 Nothing (Unknown cmd0)
      [c] -> showCmdHelp c args
      cs  -> runCommand 1 Nothing (Ambiguous cmd0 (concatMap cNames cs))
  | otherwise =
    wrapResult <$>
    case parseHelpName cmd of
      Just qname -> True <$ helpForNamed qname
      Nothing    -> False <$ rPutStrLn ("Unable to parse name: " ++ cmd)

  where
  wrapResult success = emptyCommandResult { crSuccess = success }

  showCmdHelp c [arg] | ":set" `elem` cNames c = wrapResult <$> showOptionHelp arg
  showCmdHelp c _args =
    do rPutStrLn ("\n    " ++ intercalate ", " (cNames c) ++ " " ++ intercalate " " (cArgs c))
       rPutStrLn ""
       rPutStrLn (cHelp c)
       rPutStrLn ""
       unless (null (cLongHelp c)) $ do
         rPutStrLn (cLongHelp c)
         rPutStrLn ""
       pure emptyCommandResult

  showOptionHelp arg =
    case lookupTrieExact arg userOptions of
      [opt] ->
        do let k = optName opt
           ev <- tryGetUser k
           rPutStrLn $ "\n    " ++ k ++ " = " ++ maybe "???" showEnvVal ev
           rPutStrLn ""
           rPutStrLn ("Default value: " ++ showEnvVal (optDefault opt))
           rPutStrLn ""
           rPutStrLn (optHelp opt)
           rPutStrLn ""
           pure True
      [] -> False <$ rPutStrLn ("Unknown setting name `" ++ arg ++ "`")
      _  -> False <$ rPutStrLn ("Ambiguous setting name `" ++ arg ++ "`")


runShellCmd :: String -> REPL CommandResult
runShellCmd cmd
  = io $ do h <- Process.runCommand cmd
            _ <- waitForProcess h
            return emptyCommandResult -- This could check for exit code 0

cdCmd :: FilePath -> REPL CommandResult
cdCmd f | null f = do rPutStrLn $ "[error] :cd requires a path argument"
                      pure emptyCommandResult { crSuccess = False }
        | otherwise = do
  exists <- io $ doesDirectoryExist f
  if exists
    then emptyCommandResult <$ io (setCurrentDirectory f)
    else raise $ DirectoryNotFound f

-- C-c Handlings ---------------------------------------------------------------

-- XXX this should probably do something a bit more specific.
handleCtrlC :: a -> REPL a
handleCtrlC a = do rPutStrLn "Ctrl-C"
                   resetTCSolver
                   return a

-- Utilities -------------------------------------------------------------------

-- | Lift a parsing action into the REPL monad.
replParse :: (String -> Either ParseError a) -> String -> REPL a
replParse parse str = case parse str of
  Right a -> return a
  Left e  -> raise (ParseError e)

replParseInput :: String -> Int -> Maybe FilePath -> REPL (P.ReplInput P.PName)
replParseInput str lineNum fnm = replParse (parseReplWith cfg . T.pack) str
  where
  cfg = case fnm of
          Nothing -> interactiveConfig{ cfgStart = Position lineNum 1 }
          Just f  -> defaultConfig
                     { cfgSource = f
                     , cfgStart  = Position lineNum 1
                     }

replParseExpr :: String -> (Int,Int) -> Maybe FilePath -> REPL (P.Expr P.PName)
replParseExpr str (l,c) fnm = replParse (parseExprWith cfg. T.pack) str
  where
  cfg = case fnm of
          Nothing -> interactiveConfig{ cfgStart = Position l c }
          Just f  -> defaultConfig
                     { cfgSource = f
                     , cfgStart  = Position l c
                     }

mkInteractiveRange :: (Int,Int) -> Maybe FilePath -> Range
mkInteractiveRange (l,c) mb = Range p p src
  where
  p = Position l c
  src = case mb of
          Nothing -> "<interactive>"
          Just b  -> b

interactiveConfig :: Config
interactiveConfig = defaultConfig { cfgSource = "<interactive>" }

getPrimMap :: REPL M.PrimMap
getPrimMap  = liftModuleCmd M.getPrimMap

liftModuleCmd :: M.ModuleCmd a -> REPL a
liftModuleCmd cmd =
  do evo <- getEvalOptsAction
     env <- getModuleEnv
     callStacks <- getCallStacks
     tcSolver <- getTCSolver
     let minp =
             M.ModuleInput
                { minpCallStacks = callStacks
                , minpEvalOpts   = evo
                , minpByteReader = BS.readFile
                , minpModuleEnv  = env
                , minpTCSolver   = tcSolver
                }
     moduleCmdResult =<< io (cmd minp)

-- TODO: add filter for my exhaustie prop guards warning here

moduleCmdResult :: M.ModuleRes a -> REPL a
moduleCmdResult (res,ws0) = do
  warnDefaulting  <- getKnownUser "warnDefaulting"
  warnShadowing   <- getKnownUser "warnShadowing"
  warnPrefixAssoc <- getKnownUser "warnPrefixAssoc"
  warnNonExhConGrds <- getKnownUser "warnNonExhaustiveConstraintGuards"
  -- XXX: let's generalize this pattern
  let isShadowWarn (M.SymbolShadowed {}) = True
      isShadowWarn _                     = False

      isPrefixAssocWarn (M.PrefixAssocChanged {}) = True
      isPrefixAssocWarn _                         = False

      filterRenamer True _ w = Just w
      filterRenamer _ check (M.RenamerWarnings xs) =
        case filter (not . check) xs of
          [] -> Nothing
          ys -> Just (M.RenamerWarnings ys)
      filterRenamer _ _ w = Just w

      -- ignore certain warnings during typechecking
      filterTypecheck :: M.ModuleWarning -> Maybe M.ModuleWarning
      filterTypecheck (M.TypeCheckWarnings nameMap xs) =
        case filter (allow . snd) xs of
          [] -> Nothing
          ys -> Just (M.TypeCheckWarnings nameMap ys)
          where
            allow :: T.Warning -> Bool
            allow = \case
              T.DefaultingTo _ _ | not warnDefaulting -> False
              T.NonExhaustivePropGuards _ | not warnNonExhConGrds -> False
              _ -> True
      filterTypecheck w = Just w

  let ws = mapMaybe (filterRenamer warnShadowing isShadowWarn)
         . mapMaybe (filterRenamer warnPrefixAssoc isPrefixAssocWarn)
         . mapMaybe filterTypecheck
         $ ws0
  names <- M.mctxNameDisp <$> getFocusedEnv
  mapM_ (rPrint . runDoc names . pp) ws
  case res of
    Right (a,me') -> setModuleEnv me' >> return a
    Left err      ->
      do e <- case err of
                M.ErrorInFile (M.InFile file) e ->
                  -- on error, the file with the error becomes the edit
                  -- target.  Note, however, that the focused module is not
                  -- changed.
                  do setEditPath file
                     return e
                _ -> return err
         raise (ModuleSystemError names e)


replCheckExpr :: P.Expr P.PName -> REPL (P.Expr M.Name,T.Expr,T.Schema)
replCheckExpr e = liftModuleCmd $ M.checkExpr e

-- | Check declarations as though they were defined at the top-level.
replCheckDecls :: [P.Decl P.PName] -> REPL [T.DeclGroup]
replCheckDecls ds = do

  -- check the decls
  npds        <- liftModuleCmd (M.noPat ds)

  let mkTop d = P.Decl P.TopLevel { P.tlExport = P.Public
                                  , P.tlDoc    = Nothing
                                  , P.tlValue  = d }
  (names,ds',tyMap) <- liftModuleCmd (M.checkDecls (map mkTop npds))

  -- extend the naming env and type synonym maps
  denv        <- getDynEnv
  setDynEnv denv { M.deNames  = names `M.shadowing` M.deNames denv
                 , M.deTySyns = tyMap <> M.deTySyns denv
                 }
  return ds'

replSpecExpr :: T.Expr -> REPL T.Expr
replSpecExpr e = liftModuleCmd $ S.specialize e

replEvalExpr :: P.Expr P.PName -> REPL (Concrete.Value, T.Type)
replEvalExpr expr =
  do (_,def,sig) <- replCheckExpr expr
     replEvalCheckedExpr def sig >>= \case
       Just res -> pure res
       Nothing -> raise (EvalPolyError sig)

replEvalCheckedExpr :: T.Expr -> T.Schema -> REPL (Maybe (Concrete.Value, T.Type))
replEvalCheckedExpr def sig =
  replPrepareCheckedExpr def sig >>=
    traverse \(tys, def1) -> do
      let su = T.listParamSubst tys
      let ty = T.apSubst su (T.sType sig)
      whenDebug (rPutStrLn (dump def1))

      tenv <- E.envTypes . M.deEnv <$> getDynEnv
      let tyv = E.evalValType tenv ty

      -- add "it" to the namespace via a new declaration
      itVar <- bindItVariable tyv def1

      let itExpr = case getLoc def of
                      Nothing  -> T.EVar itVar
                      Just rng -> T.ELocated rng (T.EVar itVar)

      -- evaluate the it variable
      val <- liftModuleCmd (rethrowEvalError . M.evalExpr itExpr)
      return (val,ty)

-- | Check that we are in a valid evaluation context and apply defaulting.
replPrepareCheckedExpr :: T.Expr -> T.Schema ->
  REPL (Maybe ([(T.TParam, T.Type)], T.Expr))
replPrepareCheckedExpr def sig = do
  validEvalContext def
  validEvalContext sig

  s <- getTCSolver
  mbDef <- io (defaultReplExpr s def sig)

  case mbDef of
    Nothing -> pure Nothing
    Just (tys, def1) -> do
      warnDefaults tys
      pure $ Just (tys, def1)
  where
  warnDefaults ts =
    case ts of
      [] -> return ()
      _  -> do rPutStrLn "Showing a specific instance of polymorphic result:"
               mapM_ warnDefault ts

  warnDefault (x,t) =
    rPrint ("  *" <+> nest 2  ("Using" <+> quotes (pp t) <+> "for" <+>
                                pp (T.tvarDesc (T.tpInfo x))))

itIdent :: M.Ident
itIdent  = M.packIdent "it"

replWriteFile :: FilePath -> BS.ByteString -> REPL CommandResult
replWriteFile = replWriteFileWith BS.writeFile

replWriteFileString :: FilePath -> String -> REPL CommandResult
replWriteFileString = replWriteFileWith writeFile

replWriteFileWith :: (FilePath -> a -> IO ()) -> FilePath -> a -> REPL CommandResult
replWriteFileWith write fp contents =
 do x <- io (X.try (write fp contents))
    case x of
      Left e ->
        do rPutStrLn (show (e :: X.SomeException))
           pure emptyCommandResult { crSuccess = False }
      Right _ ->
        pure emptyCommandResult

replReadFile :: FilePath -> (X.SomeException -> REPL (Maybe BS.ByteString)) -> REPL (Maybe BS.ByteString)
replReadFile fp handler =
 do x <- io $ X.catch (Right `fmap` BS.readFile fp) (\e -> return $ Left e)
    either handler (return . Just) x

-- | Creates a fresh binding of "it" to the expression given, and adds
-- it to the current dynamic environment.  The fresh name generated
-- is returned.
bindItVariable :: E.TValue -> T.Expr -> REPL T.Name
bindItVariable ty expr = do
  freshIt <- freshName itIdent M.UserName
  let schema = T.Forall { T.sVars  = []
                        , T.sProps = []
                        , T.sType  = E.tValTy ty
                        }
      decl = T.Decl { T.dName       = freshIt
                    , T.dSignature  = schema
                    , T.dDefinition = T.DExpr expr
                    , T.dPragmas    = []
                    , T.dInfix      = False
                    , T.dFixity     = Nothing
                    , T.dDoc        = Nothing
                    }
  liftModuleCmd (M.evalDecls [T.NonRecursive decl])
  denv <- getDynEnv
  let nenv' = M.singletonNS M.NSValue (P.UnQual itIdent) freshIt
                           `M.shadowing` M.deNames denv
  setDynEnv $ denv { M.deNames = nenv' }
  return freshIt


-- | Extend the dynamic environment with a fresh binding for "it",
-- as defined by the given value.  If we cannot determine the definition
-- of the value, then we don't bind `it`.
bindItVariableVal :: E.TValue -> Concrete.Value -> REPL ()
bindItVariableVal ty val =
  do prims   <- getPrimMap
     mb      <- rEval (Concrete.toExpr prims ty val)
     case mb of
       Nothing   -> return ()
       Just expr -> void $ bindItVariable ty expr


-- | Creates a fresh binding of "it" to a finite sequence of
-- expressions of the same type, and adds that sequence to the current
-- dynamic environment
bindItVariables :: E.TValue -> [T.Expr] -> REPL ()
bindItVariables ty exprs = void $ bindItVariable seqTy seqExpr
  where
    len = length exprs
    seqTy = E.TVSeq (toInteger len) ty
    seqExpr = T.EList exprs (E.tValTy ty)

replEvalDecls :: [P.Decl P.PName] -> REPL ()
replEvalDecls ds = do
  dgs <- replCheckDecls ds
  validEvalContext dgs
  whenDebug (mapM_ (\dg -> (rPutStrLn (dump dg))) dgs)
  liftModuleCmd (M.evalDecls dgs)

replEdit :: String -> REPL Bool
replEdit file = do
  mb <- io (lookupEnv "EDITOR")
  let editor = fromMaybe "vim" mb
  io $ do
    (_,_,_,ph) <- createProcess (shell (unwords [editor, file]))
    exit       <- waitForProcess ph
    return (exit == ExitSuccess)

type CommandMap = Trie CommandDescr

newSeedCmd :: REPL CommandResult
newSeedCmd =
  do  seed <- createAndSetSeed
      rPutStrLn "Seed initialized to:"
      let value = show seed
      rPutStrLn value
      pure emptyCommandResult { crValue = Just value }
  where
    createAndSetSeed =
      withRandomGen $ \g0 ->
        let (s1, g1) = TFI.random g0
            (s2, g2) = TFI.random g1
            (s3, g3) = TFI.random g2
            (s4, _)  = TFI.random g3
            seed = (s1, s2, s3, s4)
        in  pure (seed, TF.seedTFGen seed)

seedCmd :: String -> REPL CommandResult
seedCmd s =
  do success <- case mbGen of
       Nothing -> False <$ rPutStrLn "Could not parse seed argument - expecting an integer or 4-tuple of integers."
       Just gen -> True <$ setRandomGen gen
     pure emptyCommandResult { crSuccess = success }

  where
    mbGen =
          (TF.mkTFGen <$> readMaybe s)
      <|> (TF.seedTFGen <$> readMaybe s)

-- Command Parsing -------------------------------------------------------------

-- | Strip leading space.
sanitize :: String -> String
sanitize  = dropWhile isSpace

-- | Strip trailing space.
sanitizeEnd :: String -> String
sanitizeEnd = reverse . sanitize . reverse

trim :: String -> String
trim = sanitizeEnd . sanitize

-- | Split at the first word boundary.
splitCommand :: String -> Maybe (Int,String,String)
splitCommand = go 0
  where
   go !len (c  : more)
      | isSpace c = go (len+1) more

   go !len (':': more)
      | (as,bs) <- span (\x -> isPunctuation x || isSymbol x) more
      , (ws,cs) <- span isSpace bs
      , not (null as) = Just (len+1+length as+length ws, ':' : as, cs)

      | (as,bs) <- break isSpace more
      , (ws,cs) <- span isSpace bs
      , not (null as) = Just (len+1+length as+length ws, ':' : as, cs)

      | otherwise = Nothing

   go !len expr
      | null expr = Nothing
      | otherwise = Just (len+length expr, expr, [])

-- | Uncons a list.
uncons :: [a] -> Maybe (a,[a])
uncons as = case as of
  a:rest -> Just (a,rest)
  _      -> Nothing

-- | Lookup a string in the command list.
findCommand :: String -> [CommandDescr]
findCommand str = lookupTrie str commands

-- | Lookup a string in the command list, returning an exact match
-- even if it's the prefix of another command.
findCommandExact :: String -> [CommandDescr]
findCommandExact str = lookupTrieExact str commands

-- | Lookup a string in the notebook-safe command list.
findNbCommand :: Bool -> String -> [CommandDescr]
findNbCommand True  str = lookupTrieExact str nbCommands
findNbCommand False str = lookupTrie      str nbCommands

-- | Parse a line as a command.
parseCommand :: (String -> [CommandDescr]) -> String -> Maybe Command
parseCommand findCmd line = do
  (cmdLen,cmd,args) <- splitCommand line
  let args' = sanitizeEnd args
  case findCmd cmd of
    [c] -> case cBody c of
      ExprArg     body -> Just (Command \l fp -> (body args' (l,cmdLen+1) fp))
      DeclsArg    body -> Just (Command \_ _ -> (body args'))
      ExprTypeArg body -> Just (Command \_ _ -> (body args'))
      ModNameArg  body -> Just (Command \_ _ -> (body args'))
      FilenameArg body -> Just (Command \_ _ -> (body =<< expandHome args'))
      OptionArg   body -> Just (Command \_ _ -> (body args'))
      ShellArg    body -> Just (Command \_ _ -> (body args'))
      HelpArg     body -> Just (Command \_ _ -> (body args'))
      NoArg       body -> Just (Command \_ _ -> body)
      FileExprArg body ->
           do (fpLen,fp,expr) <- extractFilePath args'
              Just (Command \l fp' -> do let col = cmdLen + fpLen + 1
                                         hm <- expandHome fp
                                         body hm expr (l,col) fp')
    [] -> case uncons cmd of
      Just (':',_) -> Just (Unknown cmd)
      Just _       -> Just (Command (evalCmd line))
      _            -> Nothing

    cs -> Just (Ambiguous cmd (concatMap cNames cs))

  where
  expandHome path =
    case path of
      '~' : c : more | isPathSeparator c -> do dir <- io getHomeDirectory
                                               return (dir </> more)
      _ -> return path

  extractFilePath ipt =
    let quoted q = (\(a,b) -> (length a + 2, a, drop 1 b)) . break (== q)
    in case ipt of
        ""        -> Nothing
        '\'':rest -> Just $ quoted '\'' rest
        '"':rest  -> Just $ quoted '"' rest
        _         -> let (a,b) = break isSpace ipt in
                     if null a then Nothing else Just (length a, a, b)



moduleInfoCmd :: Bool -> String -> REPL CommandResult
moduleInfoCmd isFile name
  | isFile = showInfo =<< liftModuleCmd (M.getFileDependencies name)
  | otherwise =
    case parseModName name of
      Just m  -> showInfo =<< liftModuleCmd (M.getModuleDependencies m)
      Nothing -> do rPutStrLn "Invalid module name."
                    pure emptyCommandResult { crSuccess = False }

  where
  showInfo (p,fi) =
    do rPutStr "{ \"source\": "
       case p of
         M.InFile f  -> rPutStrLn (show f)
         M.InMem l _ -> rPutStrLn ("{ \"internal\": " ++ show l ++ " }")

       rPutStrLn (", \"fingerprint\": \"0x" ++
                       fingerprintHexString (M.fiFingerprint fi) ++ "\"")

       let depList f x ys =
             do rPutStr (", " ++ show (x :: String) ++ ":")
                case ys of
                  [] -> rPutStrLn " []"
                  i : is ->
                    do rPutStrLn ""
                       rPutStrLn ("     [ " ++ f i)
                       mapM_ (\j -> rPutStrLn ("     , " ++ f j)) is
                       rPutStrLn "     ]"

       depList show               "includes" (Set.toList (M.fiIncludeDeps fi))
       depList (show . show . pp) "imports"  (Set.toList (M.fiImportDeps  fi))
       depList show               "foreign"  (Map.toList (M.fiForeignDeps fi))

       rPutStrLn "}"
       pure emptyCommandResult

-- | Extract the code blocks from the body of a docstring.
--
-- A single code block starts with at least 3 backticks followed by an
-- optional language specifier of "cryptol". This allowed other kinds
-- of code blocks to be included (and ignored) in docstrings. Longer
-- backtick sequences can be used when a code block needs to be able to
-- contain backtick sequences.
--
-- @
-- /**
--  * A docstring example
--  *
--  * ```cryptol
--  * :check example
--  * ```
--  */
-- @
extractCodeBlocks :: T.Text -> [[T.Text]]
extractCodeBlocks raw = go [] (T.lines raw)
  where
    go finished [] = reverse finished
    go finished (x:xs)
      | (spaces, x1) <- T.span (' ' ==) x
      , (ticks, x2) <- T.span ('`' ==) x1
      , 3 <= T.length ticks
      , not (T.elem '`' x2)
      , let info = T.strip x2
      = if info `elem` ["", "repl"] -- supported languages "unlabeled" and repl
        then keep finished (T.length spaces) (T.length ticks) [] xs
        else skip finished ticks xs
      | otherwise = go finished xs

    -- process a code block that we're keeping
    keep finished _ _ acc [] = go (reverse acc : finished) [] -- unterminated code fences are defined to be terminated by github
    keep finished indentLen ticksLen acc (x:xs)
      | x1 <- T.dropWhile (' ' ==) x
      , (ticks, x2) <- T.span ('`' ==) x1
      , ticksLen <= T.length ticks
      , T.all (' ' ==) x2
      = go (reverse acc : finished) xs

      | otherwise =
        let x' =
              case T.span (' ' ==) x of
                (spaces, x1)
                  | T.length spaces <= indentLen -> x1
                  | otherwise -> T.drop indentLen x
        in keep finished indentLen ticksLen (x' : acc) xs

    -- process a code block that we're skipping
    skip finished _ [] = go finished []
    skip finished close (x:xs)
      | close == x = go finished xs
      | otherwise = skip finished close xs

data SubcommandResult = SubcommandResult
  { srInput :: T.Text
  , srResult :: CommandResult
  , srLog :: String
  }

-- | Check a single code block from inside a docstring.
--
-- The result will contain the results of processing the commands up to
-- the first failure.
--
-- Execution of the commands is run in an isolated REPL environment.
checkBlock ::
  [T.Text] {- ^ lines of the code block -} ->
  REPL [SubcommandResult]
checkBlock = isolated . go
  where
    go [] = pure []
    go (line:block) =
      case parseCommand (findNbCommand True) (T.unpack line) of
        Nothing -> do
          pure [SubcommandResult
            { srInput = line
            , srLog = "Failed to parse command"
            , srResult = emptyCommandResult { crSuccess = False }
            }]
        Just Ambiguous{} -> do
          pure [SubcommandResult
            { srInput = line
            , srLog = "Ambiguous command"
            , srResult = emptyCommandResult { crSuccess = False }
            }]
        Just Unknown{} -> do
          pure [SubcommandResult
            { srInput = line
            , srLog = "Unknown command"
            , srResult = emptyCommandResult { crSuccess = False }
            }]
        Just (Command cmd) -> do
          (logtxt, eresult) <- captureLog (Cryptol.REPL.Monad.try (cmd 0 Nothing))
          case eresult of
            Left e -> do
              let result = SubcommandResult
                    { srInput = line
                    , srLog = logtxt ++ show (pp e) ++ "\n"
                    , srResult = emptyCommandResult { crSuccess = False }
                    }
              pure [result]
            Right result -> do
              let subresult = SubcommandResult
                    { srInput = line
                    , srLog = logtxt
                    , srResult = result
                    }
              subresults <- checkBlock block
              pure (subresult : subresults)

captureLog :: REPL a -> REPL (String, a)
captureLog m = do
  previousLogger <- getLogger
  outputsRef <- io (newIORef [])
  setPutStr (\str -> modifyIORef outputsRef (str:))
  result <- m `finally` setLogger previousLogger
  outputs <- io (readIORef outputsRef)
  let output = interpretControls (concat (reverse outputs))
  pure (output, result)

-- | Apply control character semantics to the result of the logger
interpretControls :: String -> String
interpretControls ('\b' : xs) = interpretControls xs
interpretControls (_ : '\b' : xs) = interpretControls xs
interpretControls (x : xs) = x : interpretControls xs
interpretControls [] = []

-- | The result of running a docstring as attached to a definition
data DocstringResult = DocstringResult
  { drName   :: T.DocFor -- ^ The associated definition of the docstring
  , drFences :: [[SubcommandResult]] -- ^ list of fences in this definition's docstring
  }

-- | Check all the code blocks in a given docstring.
checkDocItem :: T.DocItem -> REPL DocstringResult
checkDocItem item =
 do xs <- case traverse extractCodeBlocks (T.docText item) of
            [] -> pure [] -- optimization
            bs ->
              Ex.bracket
                (liftModuleCmd (`M.runModuleM` (M.getFocusedModule <* M.setFocusedModule (T.docModContext item))))
                (\mb -> liftModuleCmd (`M.runModuleM` M.setMaybeFocusedModule mb))
                (\_ -> traverse checkBlock (concat bs))
    pure DocstringResult
      { drName = T.docFor item
      , drFences = xs
      }

-- | Check all of the docstrings in the given module.
--
-- The outer list elements correspond to the code blocks from the
-- docstrings in file order. Each inner list corresponds to the
-- REPL commands inside each of the docstrings.
checkDocStrings :: M.LoadedModule -> REPL [DocstringResult]
checkDocStrings m = do
  let dat = M.lmdModule (M.lmData m)
  let ds = T.gatherModuleDocstrings (M.ifaceNameToModuleMap (M.lmInterface m)) dat
  traverse checkDocItem ds

-- | Evaluate all the docstrings in the specified module.
--
-- This command succeeds when:
-- * the module can be found
-- * the docstrings can be parsed for code blocks
-- * all of the commands in the docstrings succeed
checkDocStringsCmd ::
  String {- ^ module name -} ->
  REPL CommandResult
checkDocStringsCmd input
  | null input = do
    mb <- getLoadedMod
    case lName =<< mb of
      Nothing -> do
        rPutStrLn "No current module"
        pure emptyCommandResult { crSuccess = False }
      Just mn -> checkModName mn
  | otherwise =
    case parseModName input of
      Nothing -> do
        rPutStrLn "Invalid module name"
        pure emptyCommandResult { crSuccess = False }
      Just mn -> checkModName mn

  where

    countOutcomes :: [[SubcommandResult]] -> (Int, Int, Int)
    countOutcomes = foldl' countOutcomes1 (0, 0, 0)
      where
        countOutcomes1 (successes, nofences, failures) []
          = (successes, nofences + 1, failures)
        countOutcomes1 acc result = foldl' countOutcomes2 acc result

        countOutcomes2 (successes, nofences, failures) result
          | crSuccess (srResult result) = (successes + 1, nofences, failures)
          | otherwise = (successes, nofences, failures + 1)


    checkModName :: P.ModName -> REPL CommandResult
    checkModName mn =
     do env <- getModuleEnv
        case M.lookupModule mn env of
          Nothing ->
            case M.lookupSignature mn env of
              Nothing ->
               do rPutStrLn ("Module " ++ show input ++ " is not loaded")
                  pure emptyCommandResult { crSuccess = False }
              Just{} ->
               do rPutStrLn "Skipping docstrings on interface module"
                  pure emptyCommandResult

          Just fe
            | T.isParametrizedModule (M.lmdModule (M.lmData fe)) -> do
              rPutStrLn "Skipping docstrings on parameterized module"
              pure emptyCommandResult

            | otherwise -> do
              results <- checkDocStrings fe
              let (successes, nofences, failures) = countOutcomes [concat (drFences r) | r <- results]

              forM_ results $ \dr ->
                unless (null (drFences dr)) $
                 do rPutStrLn ""
                    rPutStrLn ("\nChecking " ++ show (pp (drName dr)))
                    forM_ (drFences dr) $ \fence ->
                      forM_ fence $ \line -> do
                        rPutStrLn ""
                        rPutStrLn (T.unpack (srInput line))
                        rPutStr (srLog line)

              rPutStrLn ""
              rPutStrLn ("Successes: " ++ show successes ++ ", No fences: " ++ show nofences ++ ", Failures: " ++ show failures)

              pure emptyCommandResult { crSuccess = failures == 0 }
