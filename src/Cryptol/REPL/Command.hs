-- |
-- Module      :  Cryptol.REPL.Command
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RecordWildCards #-}
module Cryptol.REPL.Command (
    -- * Commands
    Command(..), CommandDescr(..), CommandBody(..), CommandExitCode(..)
  , parseCommand
  , runCommand
  , splitCommand
  , findCommand
  , findCommandExact
  , findNbCommand
  , commandList

  , moduleCmd, loadCmd, loadPrelude, setOptionCmd

    -- Parsing
  , interactiveConfig
  , replParseExpr

    -- Evaluation and Typechecking
  , replEvalExpr
  , replCheckExpr

    -- Check, SAT, and prove
  , qcCmd, QCMode(..)
  , satCmd
  , proveCmd
  , onlineProveSat
  , offlineProveSat

    -- Misc utilities
  , handleCtrlC
  , sanitize

    -- To support Notebook interface (might need to refactor)
  , replParse
  , liftModuleCmd
  , moduleCmdResult
  ) where

import Cryptol.REPL.Monad
import Cryptol.REPL.Trie

import qualified Cryptol.ModuleSystem as M
import qualified Cryptol.ModuleSystem.Name as M
import qualified Cryptol.ModuleSystem.NamingEnv as M
import qualified Cryptol.ModuleSystem.Renamer as M (RenamerWarning(SymbolShadowed))
import qualified Cryptol.Utils.Ident as M
import qualified Cryptol.ModuleSystem.Env as M

import           Cryptol.Eval.Concrete( Concrete(..) )
import qualified Cryptol.Eval.Concrete as Concrete
import qualified Cryptol.Eval.Monad as E
import qualified Cryptol.Eval.Value as E
import qualified Cryptol.Eval.Reference as R
import Cryptol.Testing.Random
import qualified Cryptol.Testing.Random  as TestR
import Cryptol.Parser
    (parseExprWith,parseReplWith,ParseError(),Config(..),defaultConfig
    ,parseModName,parseHelpName)
import qualified Cryptol.TypeCheck.AST as T
import qualified Cryptol.TypeCheck.Error as T
import qualified Cryptol.TypeCheck.Parseable as T
import qualified Cryptol.TypeCheck.Subst as T
import           Cryptol.TypeCheck.Solve(defaultReplExpr)
import qualified Cryptol.TypeCheck.Solver.SMT as SMT
import Cryptol.TypeCheck.PP (dump,ppWithNames,emptyNameMap)
import Cryptol.Utils.PP
import Cryptol.Utils.Panic(panic)
import qualified Cryptol.Parser.AST as P
import qualified Cryptol.Transform.Specialize as S
import Cryptol.Symbolic (ProverCommand(..), QueryType(..), SatNum(..),ProverStats,ProverResult(..))
import qualified Cryptol.Symbolic.SBV as SBV
import qualified Cryptol.Symbolic.What4 as W4

import qualified Control.Exception as X
import Control.Monad hiding (mapM, mapM)
import Control.Monad.IO.Class(liftIO)
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BS8
import Data.Bits (shiftL, (.&.), (.|.))
import Data.Char (isSpace,isPunctuation,isSymbol,isAlphaNum,isAscii)
import Data.Function (on)
import Data.List (intercalate, nub, sortBy, groupBy,
                                        partition, isPrefixOf,intersperse)
import Data.Maybe (fromMaybe,mapMaybe,isNothing)
import System.Environment (lookupEnv)
import System.Exit (ExitCode(ExitSuccess))
import System.Process (shell,createProcess,waitForProcess)
import qualified System.Process as Process(runCommand)
import System.FilePath((</>), isPathSeparator)
import System.Directory(getHomeDirectory,setCurrentDirectory,doesDirectoryExist
                       ,getTemporaryDirectory,setPermissions,removeFile
                       ,emptyPermissions,setOwnerReadable)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import System.IO
         (Handle,hFlush,stdout,openTempFile,hClose,openFile
         ,IOMode(..),hGetContents,hSeek,SeekMode(..))
import System.Random.TF(newTFGen)
import Numeric (showFFloat)
import qualified Data.Text as T
import Data.IORef(newIORef,readIORef)

import GHC.Float (log1p, expm1)

import Prelude ()
import Prelude.Compat

import qualified Data.SBV.Internals as SBV (showTDiff)

-- Commands --------------------------------------------------------------------

-- | Commands.
data Command
  = Command (REPL ())         -- ^ Successfully parsed command
  | Ambiguous String [String] -- ^ Ambiguous command, list of conflicting
                              --   commands
  | Unknown String            -- ^ The unknown command

-- | Command builder.
data CommandDescr = CommandDescr
  { cNames  :: [String]
  , cArgs   :: [String]
  , cBody   :: CommandBody
  , cHelp   :: String
  }

instance Show CommandDescr where
  show = show . cNames

instance Eq CommandDescr where
  (==) = (==) `on` cNames

instance Ord CommandDescr where
  compare = compare `on` cNames

data CommandBody
  = ExprArg     (String   -> REPL ())
  | FileExprArg (FilePath -> String -> REPL ())
  | DeclsArg    (String   -> REPL ())
  | ExprTypeArg (String   -> REPL ())
  | ModNameArg  (String   -> REPL ())
  | FilenameArg (FilePath -> REPL ())
  | OptionArg   (String   -> REPL ())
  | ShellArg    (String   -> REPL ())
  | HelpArg     (String   -> REPL ())
  | NoArg       (REPL ())


data CommandExitCode = CommandOk
                     | CommandError -- XXX: More?


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
  , CommandDescr [ ":b", ":browse" ] ["[ MODULE ]"] (ModNameArg browseCmd)
    "Display environment for all loaded modules, or for a specific module."
  , CommandDescr [ ":?", ":help" ] ["[ TOPIC ]"] (HelpArg helpCmd)
    "Display a brief description of a function, type, or command."
  , CommandDescr [ ":s", ":set" ] ["[ OPTION [ = VALUE ] ]"] (OptionArg setOptionCmd)
    "Set an environmental option (:set on its own displays current values)."
  , CommandDescr [ ":check" ] ["[ EXPR ]"] (ExprArg (void . qcCmd QCRandom))
    "Use random testing to check that the argument always returns true.\n(If no argument, check all properties.)"
  , CommandDescr [ ":exhaust" ] ["[ EXPR ]"] (ExprArg (void . qcCmd QCExhaust))
    "Use exhaustive testing to prove that the argument always returns\ntrue. (If no argument, check all properties.)"
  , CommandDescr [ ":prove" ] ["[ EXPR ]"] (ExprArg proveCmd)
    "Use an external solver to prove that the argument always returns\ntrue. (If no argument, check all properties.)"
  , CommandDescr [ ":sat" ] ["[ EXPR ]"] (ExprArg satCmd)
    "Use a solver to find a satisfying assignment for which the argument\nreturns true. (If no argument, find an assignment for all properties.)"
  , CommandDescr [ ":debug_specialize" ] ["EXPR"](ExprArg specializeCmd)
    "Do type specialization on a closed expression."
  , CommandDescr [ ":eval" ] ["EXPR"] (ExprArg refEvalCmd)
    "Evaluate an expression with the reference evaluator."
  , CommandDescr [ ":ast" ] ["EXPR"] (ExprArg astOfCmd)
    "Print out the pre-typechecked AST of a given term."
  , CommandDescr [ ":extract-coq" ] [] (NoArg allTerms)
    "Print out the post-typechecked AST of all currently defined terms,\nin a Coq-parseable format."
  ]

commandList :: [CommandDescr]
commandList  =
  nbCommandList ++
  [ CommandDescr [ ":q", ":quit" ] [] (NoArg quitCmd)
    "Exit the REPL."
  , CommandDescr [ ":l", ":load" ] ["FILE"] (FilenameArg loadCmd)
    "Load a module by filename."
  , CommandDescr [ ":r", ":reload" ] [] (NoArg reloadCmd)
    "Reload the currently loaded module."
  , CommandDescr [ ":e", ":edit" ] ["[ FILE ]"] (FilenameArg editCmd)
    "Edit FILE or the currently loaded module."
  , CommandDescr [ ":!" ] ["COMMAND"] (ShellArg runShellCmd)
    "Execute a command in the shell."
  , CommandDescr [ ":cd" ] ["DIR"] (FilenameArg cdCmd)
    "Set the current working directory."
  , CommandDescr [ ":m", ":module" ] ["[ MODULE ]"] (FilenameArg moduleCmd)
    "Load a module by its name."
  , CommandDescr [ ":w", ":writeByteArray" ] ["FILE", "EXPR"] (FileExprArg writeFileCmd)
    "Write data of type 'fin n => [n][8]' to a file."
  , CommandDescr [ ":readByteArray" ] ["FILE"] (FilenameArg readFileCmd)
    "Read data from a file as type 'fin n => [n][8]', binding\nthe value to variable 'it'."
  , CommandDescr [ ":dumptests" ] ["FILE", "EXPR"] (FileExprArg dumpTestsCmd)
    (unlines [ "Dump a tab-separated collection of tests for the given"
             , "expression into a file. The first column in each line is"
             , "the expected output, and the remainder are the inputs. The"
             , "number of tests is determined by the \"tests\" option."
             ])
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
runCommand :: Command -> REPL CommandExitCode
runCommand c = case c of

  Command cmd -> (cmd >> return CommandOk) `Cryptol.REPL.Monad.catch` handler
    where
    handler re = rPutStrLn "" >> rPrint (pp re) >> return CommandError

  Unknown cmd -> do rPutStrLn ("Unknown command: " ++ cmd)
                    return CommandError

  Ambiguous cmd cmds -> do
    rPutStrLn (cmd ++ " is ambiguous, it could mean one of:")
    rPutStrLn ("\t" ++ intercalate ", " cmds)
    return CommandError


-- Get the setting we should use for displaying values.
getPPValOpts :: REPL E.PPOpts
getPPValOpts =
  do base      <- getKnownUser "base"
     ascii     <- getKnownUser "ascii"
     infLength <- getKnownUser "infLength"
     return E.PPOpts { E.useBase      = base
                     , E.useAscii     = ascii
                     , E.useInfLength = infLength
                     }

getEvalOpts :: REPL E.EvalOpts
getEvalOpts =
  do ppOpts <- getPPValOpts
     l      <- getLogger
     return E.EvalOpts { E.evalPPOpts = ppOpts, E.evalLogger = l }

evalCmd :: String -> REPL ()
evalCmd str = do
  letEnabled <- getLetEnabled
  ri <- if letEnabled
          then replParseInput str
          else P.ExprInput <$> replParseExpr str
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

      rPutStrLn (show valDoc)
    P.LetInput decl -> do
      -- explicitly make this a top-level declaration, so that it will
      -- be generalized if mono-binds is enabled
      replEvalDecl decl

printCounterexample :: Bool -> P.Expr P.PName -> [Concrete.Value] -> REPL ()
printCounterexample isSat pexpr vs =
  do ppOpts <- getPPValOpts
     docs <- mapM (rEval . E.ppValue Concrete ppOpts) vs
     let doc = ppPrec 3 pexpr -- function application has precedence 3
     rPrint $ hang doc 2 (sep docs) <+>
       text (if isSat then "= True" else "= False")

dumpTestsCmd :: FilePath -> String -> REPL ()
dumpTestsCmd outFile str =
  do expr <- replParseExpr str
     (val, ty) <- replEvalExpr expr
     evo <- getEvalOpts
     ppopts <- getPPValOpts
     testNum <- getKnownUser "tests" :: REPL Int
     g <- io newTFGen
     gens <-
       case TestR.dumpableType ty of
         Nothing -> raise (TypeNotTestable ty)
         Just gens -> return gens
     tests <- io $ TestR.returnTests g evo gens val testNum
     out <- forM tests $
            \(args, x) ->
              do argOut <- mapM (rEval . E.ppValue Concrete ppopts) args
                 resOut <- rEval (E.ppValue Concrete ppopts x)
                 return (renderOneLine resOut ++ "\t" ++ intercalate "\t" (map renderOneLine argOut) ++ "\n")
     io $ writeFile outFile (concat out) `X.catch` handler
  where
    handler :: X.SomeException -> IO ()
    handler e = putStrLn (X.displayException e)



data QCMode = QCRandom | QCExhaust deriving (Eq, Show)

-- | Randomly test a property, or exhaustively check it if the number
-- of values in the type under test is smaller than the @tests@
-- environment variable, or we specify exhaustive testing.
qcCmd :: QCMode -> String -> REPL [TestReport]
qcCmd qcMode "" =
  do (xs,disp) <- getPropertyNames
     let nameStr x = show (fixNameDisp disp (pp x))
     if null xs
        then rPutStrLn "There are no properties in scope." *> return []
        else concat <$> (forM xs $ \x ->
               do let str = nameStr x
                  rPutStr $ "property " ++ str ++ " "
                  qcCmd qcMode str)

qcCmd qcMode str =
  do expr <- replParseExpr str
     (val,ty) <- replEvalExpr expr
     testNum <- getKnownUser "tests"
     case testableType ty of
       Just (Just sz,tys,vss) | qcMode == QCExhaust || sz <= toInteger testNum -> do
            rPutStrLn "Using exhaustive testing."
            let f _ [] = panic "Cryptol.REPL.Command"
                                    ["Exhaustive testing ran out of test cases"]
                f _ (vs : vss1) = do
                  evo <- getEvalOpts
                  result <- io $ evalTest evo val vs
                  return (result, vss1)
                testSpec = TestSpec {
                    testFn = f
                  , testProp = str
                  , testTotal = sz
                  , testPossible = Just sz
                  , testRptProgress = ppProgress
                  , testClrProgress = delProgress
                  , testRptFailure = ppFailure tys expr
                  , testRptSuccess = do
                      delTesting
                      prtLn $ "Passed " ++ show sz ++ " tests."
                      rPutStrLn "Q.E.D."
                  }
            prt testingMsg
            report <- runTests testSpec vss
            return [report]

       Just (sz,tys,_) | qcMode == QCRandom ->
         case TestR.testableTypeGenerators ty of
              Nothing   -> raise (TypeNotTestable ty)
              Just gens -> do
                rPutStrLn "Using random testing."
                evo <- getEvalOpts
                let testSpec = TestSpec {
                        testFn = \sz' g ->
                                      io $ TestR.runOneTest evo val gens sz' g
                      , testProp = str
                      , testTotal = toInteger testNum
                      , testPossible = sz
                      , testRptProgress = ppProgress
                      , testClrProgress = delProgress
                      , testRptFailure = ppFailure tys expr
                      , testRptSuccess = do
                          delTesting
                          prtLn $ "Passed " ++ show testNum ++ " tests."
                      }
                prt testingMsg
                g <- io newTFGen
                report <- runTests testSpec g
                when (isPass (reportResult report)) $
                  case sz of
                    Nothing -> return ()
                    Just n -> rPutStrLn $ coverageString testNum n
                return [report]
       _ -> raise (TypeNotTestable ty)

  where
  testingMsg = "Testing... "

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
  prtLn msg = rPutStrLn msg >> io (hFlush stdout)

  ppProgress this tot = unlessBatch $
    let percent = show (div (100 * this) tot) ++ "%"
        width   = length percent
        pad     = replicate (totProgressWidth - width) ' '
    in prt (pad ++ percent)

  del n       = unlessBatch
              $ prt (replicate n '\BS' ++ replicate n ' ' ++ replicate n '\BS')
  delTesting  = del (length testingMsg)
  delProgress = del totProgressWidth

  ppFailure tys pexpr failure = do
    delTesting
    opts <- getPPValOpts
    case failure of
      FailFalse vs -> do
        let isSat = False
        printCounterexample isSat pexpr vs
        case (tys,vs) of
          ([t],[v]) -> bindItVariableVal t v
          _ -> let fs = [ M.packIdent ("arg" ++ show (i::Int)) | i <- [ 1 .. ] ]
                   t = T.TRec (zip fs tys)
                   v = E.VRecord (Map.fromList (zip fs (map return vs)))
               in bindItVariableVal t v

      FailError err [] -> do
        prtLn "ERROR"
        rPrint (pp err)
      FailError err vs -> do
        prtLn "ERROR for the following inputs:"
        mapM_ (\v -> rPrint =<< (rEval $ E.ppValue Concrete opts v)) vs
        rPrint (pp err)
      Pass -> panic "Cryptol.REPL.Command" ["unexpected Test.Pass"]


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
expectedCoverage :: Int -> Integer -> (Double, Double)
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

satCmd, proveCmd :: String -> REPL ()
satCmd = cmdProveSat True
proveCmd = cmdProveSat False

showProverStats :: Maybe String -> ProverStats -> REPL ()
showProverStats mprover stat = rPutStrLn msg
  where

  msg = "(Total Elapsed Time: " ++ SBV.showTDiff stat ++
        maybe "" (\p -> ", using " ++ show p) mprover ++ ")"

rethrowErrorCall :: REPL a -> REPL a
rethrowErrorCall m = REPL (\r -> unREPL m r `X.catch` handler `X.catch` handler')
  where
    handler (X.ErrorCallWithLocation s _) = X.throwIO (SBVError s)
    handler' e = X.throwIO (SBVException e)


-- | Console-specific version of 'proveSat'. Prints output to the
-- console, and binds the @it@ variable to a record whose form depends
-- on the expression given. See ticket #66 for a discussion of this
-- design.
cmdProveSat :: Bool -> String -> REPL ()
cmdProveSat isSat "" =
  do (xs,disp) <- getPropertyNames
     let nameStr x = show (fixNameDisp disp (pp x))
     if null xs
        then rPutStrLn "There are no properties in scope."
        else forM_ xs $ \x ->
               do let str = nameStr x
                  if isSat
                     then rPutStr $ ":sat "   ++ str ++ "\n\t"
                     else rPutStr $ ":prove " ++ str ++ "\n\t"
                  cmdProveSat isSat str
cmdProveSat isSat str = do
  let cexStr | isSat = "satisfying assignment"
             | otherwise = "counterexample"
  proverName <- getKnownUser "prover"
  fileName   <- getKnownUser "smtfile"
  let mfile = if fileName == "-" then Nothing else Just fileName

  if proverName `elem` ["offline","sbv-offline","w4-offline"] then
     offlineProveSat proverName isSat str mfile
  else
     do (firstProver,result,stats) <- rethrowErrorCall (onlineProveSat proverName isSat str mfile)
        case result of
          EmptyResult         ->
            panic "REPL.Command" [ "got EmptyResult for online prover query" ]
          ProverError msg     -> rPutStrLn msg
          ThmResult ts        -> do
            rPutStrLn (if isSat then "Unsatisfiable" else "Q.E.D.")
            (t, e) <- mkSolverResult cexStr (not isSat) (Left ts)
            bindItVariable t e
          AllSatResult tevss -> do
            let tess = map (map $ \(t,e,_) -> (t,e)) tevss
                vss  = map (map $ \(_,_,v) -> v)     tevss
            resultRecs <- mapM (mkSolverResult cexStr isSat . Right) tess
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
            pexpr <- replParseExpr str

            ~(EnvBool yes) <- getUser "show-examples"
            when yes $ forM_ vss (printCounterexample isSat pexpr)

            case (ty, exprs) of
              (t, [e]) -> bindItVariable t e
              (t, es ) -> bindItVariables t es

        seeStats <- getUserShowProverStats
        when seeStats (showProverStats firstProver stats)

onlineProveSat :: String
               -> Bool
               -> String -> Maybe FilePath
               -> REPL (Maybe String,ProverResult,ProverStats)
onlineProveSat proverName isSat str mfile = do
  verbose <- getKnownUser "debug"
  satNum <- getUserSatNum
  modelValidate <- getUserProverValidate
  parseExpr <- replParseExpr str
  (_, expr, schema) <- replCheckExpr parseExpr
  validEvalContext expr
  validEvalContext schema
  decls <- fmap M.deDecls getDynEnv
  timing <- io (newIORef 0)
  let cmd = ProverCommand {
          pcQueryType    = if isSat then SatQuery satNum else ProveQuery
        , pcProverName   = proverName
        , pcVerbose      = verbose
        , pcValidate     = modelValidate
        , pcProverStats  = timing
        , pcExtraDecls   = decls
        , pcSmtFile      = mfile
        , pcExpr         = expr
        , pcSchema       = schema
        }
  (firstProver, res) <-
     if | proverName `elem` W4.proverNames  -> liftModuleCmd $ W4.satProve cmd
        | proverName `elem` SBV.proverNames -> liftModuleCmd $ SBV.satProve cmd
        | otherwise -> panic "onlineProveSat" ["unexpected prover name", proverName]

  stas <- io (readIORef timing)
  return (firstProver,res,stas)

offlineProveSat :: String -> Bool -> String -> Maybe FilePath -> REPL ()
offlineProveSat proverName isSat str mfile = do
  verbose <- getKnownUser "debug"
  modelValidate <- getUserProverValidate
  parseExpr <- replParseExpr str
  (_, expr, schema) <- replCheckExpr parseExpr
  decls <- fmap M.deDecls getDynEnv
  timing <- io (newIORef 0)
  let cmd = ProverCommand {
          pcQueryType    = if isSat then SatQuery (SomeSat 0) else ProveQuery
        , pcProverName   = proverName
        , pcVerbose      = verbose
        , pcValidate     = modelValidate
        , pcProverStats  = timing
        , pcExtraDecls   = decls
        , pcSmtFile      = mfile
        , pcExpr         = expr
        , pcSchema       = schema
        }

  put <- getPutStr
  let putLn x = put (x ++ "\n")
  let displayMsg =
        do let filename = fromMaybe "standard output" mfile
           let satWord | isSat = "satisfiability"
                       | otherwise = "validity"
           putLn $
               "Writing to SMT-Lib file " ++ filename ++ "..."
           putLn $
             "To determine the " ++ satWord ++
             " of the expression, use an external SMT solver."

  if
   | proverName == "offline" || proverName == "sbv-offline" ->
      do result <- liftModuleCmd $ SBV.satProveOffline cmd
         case result of
           Left msg -> rPutStrLn msg
           Right smtlib -> do
             io $ displayMsg
             case mfile of
               Just path -> io $ writeFile path smtlib
               Nothing -> rPutStr smtlib

   | proverName == "w4-offline" ->
      do result <- liftModuleCmd $ W4.satProveOffline cmd $ \f ->
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

    | otherwise -> panic "offlineProveSat" ["unexpected offline solver name", proverName]

rIdent :: M.Ident
rIdent  = M.packIdent "result"

-- | Make a type/expression pair that is suitable for binding to @it@
-- after running @:sat@ or @:prove@
mkSolverResult :: String
               -> Bool
               -> Either [T.Type] [(T.Type, T.Expr)]
               -> REPL (T.Type, T.Expr)
mkSolverResult thing result earg =
  do prims <- getPrimMap
     let addError t = (t, T.eError prims t ("no " ++ thing ++ " available"))

         argF = case earg of
                  Left ts   -> mkArgs (map addError ts)
                  Right tes -> mkArgs tes

         eTrue  = T.ePrim prims (M.packIdent "True")
         eFalse = T.ePrim prims (M.packIdent "False")
         resultE = if result then eTrue else eFalse

         rty = T.TRec $ [(rIdent, T.tBit )] ++ map fst argF
         re  = T.ERec $ [(rIdent, resultE)] ++ map snd argF

     return (rty, re)
  where
  mkArgs tes = zipWith mkArg [1 :: Int ..] tes
    where
    mkArg n (t,e) =
      let argName = M.packIdent ("arg" ++ show n)
       in ((argName,t),(argName,e))

specializeCmd :: String -> REPL ()
specializeCmd str = do
  parseExpr <- replParseExpr str
  (_, expr, schema) <- replCheckExpr parseExpr
  spexpr <- replSpecExpr expr
  rPutStrLn  "Expression type:"
  rPrint    $ pp schema
  rPutStrLn  "Original expression:"
  rPutStrLn $ dump expr
  rPutStrLn  "Specialized expression:"
  rPutStrLn $ dump spexpr

refEvalCmd :: String -> REPL ()
refEvalCmd str = do
  parseExpr <- replParseExpr str
  (_, expr, schema) <- replCheckExpr parseExpr
  validEvalContext expr
  validEvalContext schema
  val <- liftModuleCmd (rethrowEvalError . R.evaluate expr)
  opts <- getPPValOpts
  rPrint $ R.ppValue opts val

astOfCmd :: String -> REPL ()
astOfCmd str = do
 expr <- replParseExpr str
 (re,_,_) <- replCheckExpr (P.noPos expr)
 rPrint (fmap M.nameUnique re)

allTerms :: REPL ()
allTerms = do
  me <- getModuleEnv
  rPrint $ T.showParseable $ concatMap T.mDecls $ M.loadedModules me

typeOfCmd :: String -> REPL ()
typeOfCmd str = do

  expr         <- replParseExpr str
  (_re,def,sig) <- replCheckExpr expr

  -- XXX need more warnings from the module system
  whenDebug (rPutStrLn (dump def))
  fDisp <- M.mctxNameDisp <$> getFocusedEnv
  -- type annotation ':' has precedence 2
  rPrint $ runDoc fDisp $ ppPrec 2 expr <+> text ":" <+> pp sig

readFileCmd :: FilePath -> REPL ()
readFileCmd fp = do
  bytes <- replReadFile fp (\err -> rPutStrLn (show err) >> return Nothing)
  case bytes of
    Nothing -> return ()
    Just bs ->
      do pm <- getPrimMap
         let val = byteStringToInteger bs
         let len = BS.length bs
         let split = T.ePrim pm (M.packIdent "split")
         let number = T.ePrim pm (M.packIdent "number")
         let f = T.EProofApp (foldl T.ETApp split [T.tNum len, T.tNum (8::Integer), T.tBit])
         let t = T.tWord (T.tNum (toInteger len * 8))
         let x = T.EProofApp (T.ETApp (T.ETApp number (T.tNum val)) t)
         let expr = T.EApp f x
         bindItVariable (T.tString len) expr

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

writeFileCmd :: FilePath -> String -> REPL ()
writeFileCmd file str = do
  expr         <- replParseExpr str
  (val,ty)     <- replEvalExpr expr
  if not (tIsByteSeq ty)
   then rPrint $  "Cannot write expression of types other than [n][8]."
              <+> "Type was: " <+> pp ty
   else wf file =<< serializeValue val
 where
  wf fp bytes = replWriteFile fp bytes (rPutStrLn . show)
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
rEval m = do ev <- getEvalOpts
             io (E.runEval ev m)

rEvalRethrow :: E.Eval a -> REPL a
rEvalRethrow m = do ev <- getEvalOpts
                    io $ rethrowEvalError $ E.runEval ev m

reloadCmd :: REPL ()
reloadCmd  = do
  mb <- getLoadedMod
  case mb of
    Just lm  ->
      case lName lm of
        Just m | M.isParamInstModName m -> loadHelper (M.loadModuleByName m)
        _ -> case lPath lm of
               M.InFile f -> loadCmd f
               _ -> return ()
    Nothing -> return ()


editCmd :: String -> REPL ()
editCmd path =
  do mbE <- getEditPath
     mbL <- getLoadedMod
     if not (null path)
        then do when (isNothing mbL)
                  $ setLoadedMod LoadedModule { lName = Nothing
                                              , lPath = M.InFile path }
                doEdit path
        else case msum [ M.InFile <$> mbE, lPath <$> mbL ] of
               Nothing -> rPutStrLn "No filed to edit."
               Just p  ->
                  case p of
                    M.InFile f   -> doEdit f
                    M.InMem l bs -> withROTempFile l bs replEdit >> pure ()
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



moduleCmd :: String -> REPL ()
moduleCmd modString
  | null modString = return ()
  | otherwise      = do
      case parseModName modString of
        Just m  -> loadHelper (M.loadModuleByName m)
        Nothing -> rPutStrLn "Invalid module name."

loadPrelude :: REPL ()
loadPrelude  = moduleCmd $ show $ pp M.preludeName

loadCmd :: FilePath -> REPL ()
loadCmd path
  | null path = return ()

  -- when `:load`, the edit and focused paths become the parameter
  | otherwise = do setEditPath path
                   setLoadedMod LoadedModule { lName = Nothing
                                             , lPath = M.InFile path
                                             }
                   loadHelper (M.loadModuleByPath path)

loadHelper :: M.ModuleCmd (M.ModulePath,T.Module) -> REPL ()
loadHelper how =
  do clearLoadedMod
     (path,m) <- liftModuleCmd how
     whenDebug (rPutStrLn (dump m))
     setLoadedMod LoadedModule
        { lName = Just (T.mName m)
        , lPath = path
        }
     -- after a successful load, the current module becomes the edit target
     case path of
       M.InFile f -> setEditPath f
       M.InMem {} -> clearEditPath
     setDynEnv mempty

quitCmd :: REPL ()
quitCmd  = stop


browseCmd :: String -> REPL ()
browseCmd input = do
  let mnames = map (M.textToModName . T.pack) (words input)
  validModNames <- (:) M.interactiveName <$> getModNames
  let checkModName m =
        unless (m `elem` validModNames) $
        rPutStrLn ("error: " ++ show m ++ " is not a loaded module.")
  mapM_ checkModName mnames

  fe <- getFocusedEnv

  let params = M.mctxParams fe
      iface  = M.mctxDecls fe
      names  = M.mctxNames fe
      disp   = M.mctxNameDisp fe
      provV  = M.mctxValueProvenance fe
      provT  = M.mctxTypeProvenace fe


  let f &&& g = \x -> f x && g x
      isUser x = case M.nameInfo x of
                   M.Declared _ M.SystemName -> False
                   _ -> True
      inSet s x = x `Set.member` s

  let (visibleTypes,visibleDecls) = M.visibleNames names

      restricted = if null mnames then const True else hasAnyModName mnames

      visibleType  = isUser &&& restricted &&& inSet visibleTypes
      visibleDecl  = isUser &&& restricted &&& inSet visibleDecls

  browseMParams  visibleType visibleDecl params disp
  browseTSyns    visibleType provT       iface disp
  browsePrimTys  visibleType provT       iface disp
  browseNewtypes visibleType provT       iface disp
  browseVars     visibleDecl provV       iface disp


browseMParams :: (M.Name -> Bool) -> (M.Name -> Bool) ->
                 M.IfaceParams -> NameDisp -> REPL ()
browseMParams visT visD M.IfaceParams { .. } names =
  do ppBlock names ppParamTy "Type Parameters"
                              (sorted visT T.mtpName ifParamTypes)
     ppBlock names ppParamFu "Value Parameters"
                              (sorted visD T.mvpName ifParamFuns)

  where
  ppParamTy T.ModTParam { .. } = hang ("type" <+> pp mtpName <+> ":")
                                                           2 (pp mtpKind)
  ppParamFu T.ModVParam { .. } = hang (pp mvpName <+> ":") 2 (pp mvpType)

  sorted vis nm mp = sortBy (M.cmpNameDisplay names `on` nm)
               $ filter (vis . nm) $ Map.elems mp

type Prov = Map M.Name M.DeclProvenance

browsePrimTys :: (M.Name -> Bool) -> Prov -> M.IfaceDecls -> NameDisp -> REPL ()
browsePrimTys isVisible prov M.IfaceDecls { .. } names =
  ppSection (Map.elems ifAbstractTypes)
    Section { secName = "Primitive Types"
            , secEntryName = T.atName
            , secProvenance = prov
            , secDisp = names
            , secPP = ppA
            , secVisible = isVisible
            }
  where
  ppA a = pp (T.atName a) <+> ":" <+> pp (T.atKind a)


browseTSyns :: (M.Name -> Bool) -> Prov -> M.IfaceDecls -> NameDisp -> REPL ()
browseTSyns isVisible prov M.IfaceDecls { .. } names =
  do ppSection tss
       Section { secName = "Type Synonyms"
               , secEntryName = T.tsName
               , secProvenance = prov
               , secDisp = names
               , secVisible = isVisible
               , secPP = pp
               }
     ppSection cts
       Section { secName = "Constraint Synonyms"
               , secEntryName = T.tsName
               , secProvenance = prov
               , secDisp = names
               , secVisible = isVisible
               , secPP = pp
               }
  where
  (cts,tss) = partition isCtrait (Map.elems ifTySyns)
  isCtrait t = T.kindResult (T.kindOf (T.tsDef t)) == T.KProp

browseNewtypes ::
  (M.Name -> Bool) -> Prov -> M.IfaceDecls -> NameDisp -> REPL ()
browseNewtypes isVisible prov M.IfaceDecls { .. } names =
  ppSection (Map.elems ifNewtypes)
    Section { secName = "Newtypes"
            , secEntryName = T.ntName
            , secVisible = isVisible
            , secProvenance = prov
            , secDisp = names
            , secPP = T.ppNewtypeShort
            }

browseVars :: (M.Name -> Bool) -> Prov -> M.IfaceDecls -> NameDisp -> REPL ()
browseVars isVisible prov M.IfaceDecls { .. } names =
  do ppSection props Section { secName = "Properties"
                             , secEntryName = M.ifDeclName
                             , secVisible = isVisible
                             , secProvenance = prov
                             , secDisp = names
                             , secPP = ppVar
                             }
     ppSection syms  Section { secName = "Symbols"
                             , secEntryName = M.ifDeclName
                             , secVisible = isVisible
                             , secProvenance = prov
                             , secDisp = names
                             , secPP = ppVar
                             }

  where
  isProp p     = T.PragmaProperty `elem` (M.ifDeclPragmas p)
  (props,syms) = partition isProp (Map.elems ifDecls)

  ppVar M.IfaceDecl { .. } = hang (pp ifDeclName <+> char ':') 2 (pp ifDeclSig)



data Section a = Section
  { secName       :: String
  , secEntryName  :: a -> M.Name
  , secVisible    :: M.Name -> Bool
  , secProvenance :: Map M.Name M.DeclProvenance
  , secDisp       :: NameDisp
  , secPP         :: a -> Doc
  }

ppSection :: [a] -> Section a -> REPL ()
ppSection things s
  | null grouped = pure ()
  | otherwise =
    do let heading = secName s
       rPutStrLn heading
       rPutStrLn (map (const '=') heading)
       rPutStrLn ""
       mapM_ ppSub grouped

  where
  ppSub (p,ts) =
    do let heading = provHeading p
       rPutStrLn ("  " ++ heading)
       rPutStrLn ("  " ++ map (const '-') heading)
       rPutStrLn ""
       rPutStrLn $ show $ runDoc (secDisp s) $ nest 4 $ vcat $ map (secPP s) ts
       rPutStrLn ""

  grouped = map rearrange $
            groupBy sameProv $
            sortBy cmpThings
            [ (n,p,t) | t <- things,
                        let n = secEntryName s t,
                        secVisible s n,
                        let p = case Map.lookup n (secProvenance s) of
                                  Just i -> i
                                  Nothing -> panic "ppSection"
                                               [ "Name with no provenance"
                                               , show n ]
           ]

  rearrange xs = (p, [ a | (_,_,a) <- xs ])
    where (_,p,_) : _ = xs

  cmpThings (n1, p1, _) (n2, p2, _) =
    case cmpProv p1 p2 of
      EQ -> M.cmpNameDisplay (secDisp s) n1 n2
      r  -> r

  sameProv (_,p1,_) (_,p2,_) = provOrd p1 == provOrd p2

  provOrd p =
    case p of
      M.NameIsParameter      -> Left 1 :: Either Int P.ModName
      M.NameIsDynamicDecl    -> Left 2
      M.NameIsLocalPublic    -> Left 3
      M.NameIsLocalPrivate   -> Left 4
      M.NameIsImportedFrom x -> Right x

  cmpProv p1 p2 = compare (provOrd p1) (provOrd p2)

  provHeading p =
    case p of
      M.NameIsParameter      -> "Parameters"
      M.NameIsDynamicDecl    -> "REPL"
      M.NameIsLocalPublic    -> "Public"
      M.NameIsLocalPrivate   -> "Private"
      M.NameIsImportedFrom m -> "From " ++ show (pp m)



ppBlock :: NameDisp -> (a -> Doc) -> String -> [a] -> REPL ()
ppBlock names ppFun name xs = unless (null xs) $
    do rPutStrLn name
       rPutStrLn (replicate (length name) '=')
       rPrint (runDoc names (nest 4 (vcat (map ppFun xs))))
       rPutStrLn ""


setOptionCmd :: String -> REPL ()
setOptionCmd str
  | Just value <- mbValue = setUser key value
  | null key              = mapM_ (describe . optName) (leaves userOptions)
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
      Just v  -> rPutStrLn (k ++ " = " ++ showEnvVal v)
      Nothing -> do rPutStrLn ("Unknown user option: `" ++ k ++ "`")
                    when (any isSpace k) $ do
                      let (k1, k2) = break isSpace k
                      rPutStrLn ("Did you mean: `:set " ++ k1 ++ " =" ++ k2 ++ "`?")

showEnvVal :: EnvVal -> String
showEnvVal ev =
  case ev of
    EnvString s   -> s
    EnvProg p as  -> intercalate " " (p:as)
    EnvNum n      -> show n
    EnvBool True  -> "on"
    EnvBool False -> "off"

-- XXX at the moment, this can only look at declarations.
helpCmd :: String -> REPL ()
helpCmd cmd
  | null cmd  = mapM_ rPutStrLn (genHelp commandList)
  | cmd0 : args <- words cmd, ":" `isPrefixOf` cmd0 =
    case findCommandExact cmd0 of
      []  -> void $ runCommand (Unknown cmd0)
      [c] -> showCmdHelp c args
      cs  -> void $ runCommand (Ambiguous cmd0 (concatMap cNames cs))
  | otherwise =
    case parseHelpName cmd of
      Just qname ->
        do fe <- getFocusedEnv
           let params = M.mctxParams fe
               env    = M.mctxDecls  fe
               rnEnv  = M.mctxNames  fe
               disp   = M.mctxNameDisp fe

               vNames = M.lookupValNames  qname rnEnv
               tNames = M.lookupTypeNames qname rnEnv

           let helps = map (showTypeHelp params env disp) tNames ++
                       map (showValHelp params env disp qname) vNames

               separ = rPutStrLn "            ---------"
           sequence_ (intersperse separ helps)

           when (null (vNames ++ tNames)) $
             rPrint $ "Undefined name:" <+> pp qname
      Nothing ->
           rPutStrLn ("Unable to parse name: " ++ cmd)

  where
  noInfo nameEnv name =
    case M.nameInfo name of
      M.Declared m _ ->
                      rPrint $runDoc nameEnv ("Name defined in module" <+> pp m)
      M.Parameter  -> rPutStrLn "// No documentation is available."



  showTypeHelp params env nameEnv name =
    fromMaybe (noInfo nameEnv name) $
    msum [ fromTySyn, fromPrimType, fromNewtype, fromTyParam ]

    where
    fromTySyn =
      do ts <- Map.lookup name (M.ifTySyns env)
         return (doShowTyHelp nameEnv (pp ts) (T.tsDoc ts))

    fromNewtype =
      do nt <- Map.lookup name (M.ifNewtypes env)
         let decl = pp nt $$ (pp name <+> text ":" <+> pp (T.newtypeConType nt))
         return $ doShowTyHelp nameEnv decl (T.ntDoc nt)

    fromPrimType =
      do a <- Map.lookup name (M.ifAbstractTypes env)
         pure $ do rPutStrLn ""
                   rPrint $ runDoc nameEnv $ nest 4
                          $ "primitive type" <+> pp (T.atName a)
                                     <+> ":" <+> pp (T.atKind a)

                   let (vs,cs) = T.atCtrs a
                   unless (null cs) $
                     do let example = T.TCon (T.abstractTypeTC a)
                                             (map (T.TVar . T.tpVar) vs)
                            ns = T.addTNames vs emptyNameMap
                            rs = [ "•" <+> ppWithNames ns c | c <- cs ]
                        rPutStrLn ""
                        rPrint $ runDoc nameEnv $ nest 4 $
                                    backticks (ppWithNames ns example) <+>
                                    "requires:" $$ nest 2 (vcat rs)

                   doShowFix (T.atFixitiy a)

                   case T.atDoc a of
                     Nothing -> pure ()
                     Just d -> do rPutStrLn ""
                                  rPutStrLn d

    fromTyParam =
      do p <- Map.lookup name (M.ifParamTypes params)
         let uses c = T.TVBound (T.mtpParam p) `Set.member` T.fvs c
             ctrs = filter uses (map P.thing (M.ifParamConstraints params))
             ctrDoc = case ctrs of
                        [] -> empty
                        [x] -> pp x
                        xs  -> parens $ hsep $ punctuate comma $ map pp xs
             decl = text "parameter" <+> pp name <+> text ":"
                      <+> pp (T.mtpKind p)
                   $$ ctrDoc
         return $ doShowTyHelp nameEnv decl (T.mtpDoc p)

  doShowTyHelp nameEnv decl doc =
    do rPutStrLn ""
       rPrint (runDoc nameEnv (nest 4 decl))
       case doc of
         Nothing -> return ()
         Just d  -> rPutStrLn "" >> rPutStrLn d

  doShowFix fx =
    case fx of
      Just f  ->
        let msg = "Precedence " ++ show (P.fLevel f) ++ ", " ++
                   (case P.fAssoc f of
                      P.LeftAssoc   -> "associates to the left."
                      P.RightAssoc  -> "associates to the right."
                      P.NonAssoc    -> "does not associate.")

        in rPutStrLn ('\n' : msg)

      Nothing -> return ()

  showValHelp params env nameEnv qname name =
    fromMaybe (noInfo nameEnv name)
              (msum [ fromDecl, fromNewtype, fromParameter ])
    where
    fromDecl =
      do M.IfaceDecl { .. } <- Map.lookup name (M.ifDecls env)
         return $
           do rPutStrLn ""

              let property
                    | P.PragmaProperty `elem` ifDeclPragmas = text "property"
                    | otherwise                             = empty
              rPrint $ runDoc nameEnv
                     $ nest 4
                     $ property
                       <+> pp qname
                       <+> colon
                       <+> pp (ifDeclSig)

              doShowFix $ ifDeclFixity `mplus`
                          (guard ifDeclInfix >> return P.defaultFixity)

              case ifDeclDoc of
                Just str -> rPutStrLn ('\n' : str)
                Nothing  -> return ()

    fromNewtype =
      do _ <- Map.lookup name (M.ifNewtypes env)
         return $ return ()

    fromParameter =
      do p <- Map.lookup name (M.ifParamFuns params)
         return $
           do rPutStrLn ""
              rPrint $ runDoc nameEnv
                     $ nest 4
                     $ text "parameter" <+> pp qname
                                        <+> colon
                                        <+> pp (T.mvpType p)

              doShowFix (T.mvpFixity p)

              case T.mvpDoc p of
                Just str -> rPutStrLn ('\n' : str)
                Nothing  -> return ()

  showCmdHelp c [arg] | ":set" `elem` cNames c = showOptionHelp arg
  showCmdHelp c _args =
    do rPutStrLn ("\n    " ++ intercalate ", " (cNames c) ++ " " ++ intercalate " " (cArgs c))
       rPutStrLn ""
       rPutStrLn (cHelp c)
       rPutStrLn ""

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
      [] -> rPutStrLn ("Unknown setting name `" ++ arg ++ "`")
      _  -> rPutStrLn ("Ambiguous setting name `" ++ arg ++ "`")


runShellCmd :: String -> REPL ()
runShellCmd cmd
  = io $ do h <- Process.runCommand cmd
            _ <- waitForProcess h
            return ()

cdCmd :: FilePath -> REPL ()
cdCmd f | null f = rPutStrLn $ "[error] :cd requires a path argument"
        | otherwise = do
  exists <- io $ doesDirectoryExist f
  if exists
    then io $ setCurrentDirectory f
    else raise $ DirectoryNotFound f

-- C-c Handlings ---------------------------------------------------------------

-- XXX this should probably do something a bit more specific.
handleCtrlC :: a -> REPL a
handleCtrlC a = do rPutStrLn "Ctrl-C"
                   return a


-- Utilities -------------------------------------------------------------------

hasAnyModName :: [M.ModName] -> M.Name -> Bool
hasAnyModName mnames n =
  case M.nameInfo n of
    M.Declared m _ -> m `elem` mnames
    M.Parameter  -> False


-- | Lift a parsing action into the REPL monad.
replParse :: (String -> Either ParseError a) -> String -> REPL a
replParse parse str = case parse str of
  Right a -> return a
  Left e  -> raise (ParseError e)

replParseInput :: String -> REPL (P.ReplInput P.PName)
replParseInput = replParse (parseReplWith interactiveConfig . T.pack)

replParseExpr :: String -> REPL (P.Expr P.PName)
replParseExpr = replParse (parseExprWith interactiveConfig . T.pack)

interactiveConfig :: Config
interactiveConfig = defaultConfig { cfgSource = "<interactive>" }

getPrimMap :: REPL M.PrimMap
getPrimMap  = liftModuleCmd M.getPrimMap

liftModuleCmd :: M.ModuleCmd a -> REPL a
liftModuleCmd cmd =
  do evo <- getEvalOpts
     env <- getModuleEnv
     moduleCmdResult =<< io (cmd (evo,env))

moduleCmdResult :: M.ModuleRes a -> REPL a
moduleCmdResult (res,ws0) = do
  warnDefaulting <- getKnownUser "warnDefaulting"
  warnShadowing  <- getKnownUser "warnShadowing"
  -- XXX: let's generalize this pattern
  let isDefaultWarn (T.DefaultingTo _ _) = True
      isDefaultWarn _ = False

      filterDefaults w | warnDefaulting = Just w
      filterDefaults (M.TypeCheckWarnings xs) =
        case filter (not . isDefaultWarn . snd) xs of
          [] -> Nothing
          ys -> Just (M.TypeCheckWarnings ys)
      filterDefaults w = Just w

      isShadowWarn (M.SymbolShadowed {}) = True
      isShadowWarn _                     = False

      filterShadowing w | warnShadowing = Just w
      filterShadowing (M.RenamerWarnings xs) =
        case filter (not . isShadowWarn) xs of
          [] -> Nothing
          ys -> Just (M.RenamerWarnings ys)
      filterShadowing w = Just w

  let ws = mapMaybe filterDefaults . mapMaybe filterShadowing $ ws0
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
  (names,ds') <- liftModuleCmd (M.checkDecls (map mkTop npds))

  -- extend the naming env
  denv        <- getDynEnv
  setDynEnv denv { M.deNames = names `M.shadowing` M.deNames denv }

  return ds'

replSpecExpr :: T.Expr -> REPL T.Expr
replSpecExpr e = liftModuleCmd $ S.specialize e

replEvalExpr :: P.Expr P.PName -> REPL (Concrete.Value, T.Type)
replEvalExpr expr =
  do (_,def,sig) <- replCheckExpr expr
     validEvalContext def
     validEvalContext sig
     me <- getModuleEnv
     let cfg = M.meSolverConfig me
     mbDef <- io $ SMT.withSolver cfg (\s -> defaultReplExpr s def sig)

     (def1,ty) <-
        case mbDef of
          Nothing -> raise (EvalPolyError sig)
          Just (tys,def1) ->
            do warnDefaults tys
               let su = T.listParamSubst tys
               return (def1, T.apSubst su (T.sType sig))

     val <- liftModuleCmd (rethrowEvalError . M.evalExpr def1)
     whenDebug (rPutStrLn (dump def1))
     -- add "it" to the namespace
     bindItVariable ty def1
     return (val,ty)
  where
  warnDefaults ts =
    case ts of
      [] -> return ()
      _  ->
        do warnDefaulting <- getKnownUser "warnDefaulting"
           when warnDefaulting $
             do rPutStrLn "Showing a specific instance of polymorphic result:"
                mapM_ warnDefault ts

  warnDefault (x,t) =
    rPrint ("  *" <+> nest 2  ("Using" <+> quotes (pp t) <+> "for" <+>
                                pp (T.tvarDesc (T.tpInfo x))))

itIdent :: M.Ident
itIdent  = M.packIdent "it"

replWriteFile :: FilePath -> BS.ByteString -> (X.SomeException -> REPL ()) -> REPL ()
replWriteFile fp bytes handler =
 do x <- io $ X.catch (BS.writeFile fp bytes >> return Nothing) (return . Just)
    maybe (return ()) handler x

replReadFile :: FilePath -> (X.SomeException -> REPL (Maybe BS.ByteString)) -> REPL (Maybe BS.ByteString)
replReadFile fp handler =
 do x <- io $ X.catch (Right `fmap` BS.readFile fp) (\e -> return $ Left e)
    either handler (return . Just) x

-- | Creates a fresh binding of "it" to the expression given, and adds
-- it to the current dynamic environment
bindItVariable :: T.Type -> T.Expr -> REPL ()
bindItVariable ty expr = do
  freshIt <- freshName itIdent M.UserName
  let schema = T.Forall { T.sVars  = []
                        , T.sProps = []
                        , T.sType  = ty
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
  let nenv' = M.singletonE (P.UnQual itIdent) freshIt
                           `M.shadowing` M.deNames denv
  setDynEnv $ denv { M.deNames = nenv' }


-- | Extend the dynamic environment with a fresh binding for "it",
-- as defined by the given value.  If we cannot determine the definition
-- of the value, then we don't bind `it`.
bindItVariableVal :: T.Type -> Concrete.Value -> REPL ()
bindItVariableVal ty val =
  do prims   <- getPrimMap
     mb      <- rEval (Concrete.toExpr prims ty val)
     case mb of
       Nothing   -> return ()
       Just expr -> bindItVariable ty expr




-- | Creates a fresh binding of "it" to a finite sequence of
-- expressions of the same type, and adds that sequence to the current
-- dynamic environment
bindItVariables :: T.Type -> [T.Expr] -> REPL ()
bindItVariables ty exprs = bindItVariable seqTy seqExpr
  where
    len = length exprs
    seqTy = T.tSeq (T.tNum len) ty
    seqExpr = T.EList exprs ty

replEvalDecl :: P.Decl P.PName -> REPL ()
replEvalDecl decl = do
  dgs <- replCheckDecls [decl]
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
splitCommand :: String -> Maybe (String,String)
splitCommand txt =
  case sanitize txt of
    ':' : more
      | (as,bs) <- span (\x -> isPunctuation x || isSymbol x) more
      , not (null as) -> Just (':' : as, sanitize bs)

      | (as,bs) <- break isSpace more
      , not (null as) -> Just (':' : as, sanitize bs)

      | otherwise -> Nothing

    expr -> guard (not (null expr)) >> return (expr,[])

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
  (cmd,args) <- splitCommand line
  let args' = sanitizeEnd args
  case findCmd cmd of
    [c] -> case cBody c of
      ExprArg     body -> Just (Command (body args'))
      DeclsArg    body -> Just (Command (body args'))
      ExprTypeArg body -> Just (Command (body args'))
      ModNameArg  body -> Just (Command (body args'))
      FilenameArg body -> Just (Command (body =<< expandHome args'))
      OptionArg   body -> Just (Command (body args'))
      ShellArg    body -> Just (Command (body args'))
      HelpArg     body -> Just (Command (body args'))
      NoArg       body -> Just (Command  body)
      FileExprArg body ->
        case extractFilePath args' of
           Just (fp,expr) -> Just (Command (expandHome fp >>= flip body expr))
           Nothing        -> Nothing
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
    let quoted q = (\(a,b) -> (a, drop 1 b)) . break (== q)
    in case ipt of
        ""        -> Nothing
        '\'':rest -> Just $ quoted '\'' rest
        '"':rest  -> Just $ quoted '"' rest
        _         -> Just $ break isSpace ipt
