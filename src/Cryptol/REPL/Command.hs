-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RecordWildCards #-}
module Cryptol.REPL.Command (
    -- * Commands
    Command(..), CommandDescr(..), CommandBody(..)
  , parseCommand
  , runCommand
  , splitCommand
  , findCommand
  , findCommandExact
  , findNbCommand

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

import qualified Cryptol.Eval.Value as E
import Cryptol.Testing.Concrete
import qualified Cryptol.Testing.Random  as TestR
import Cryptol.Parser
    (parseExprWith,parseReplWith,ParseError(),Config(..),defaultConfig
    ,parseModName,parseHelpName)
import qualified Cryptol.TypeCheck.AST as T
import qualified Cryptol.TypeCheck.Subst as T
import qualified Cryptol.TypeCheck.InferTypes as T
import           Cryptol.TypeCheck.Solve(defaultReplExpr)
import qualified Cryptol.TypeCheck.Solver.CrySAT as CrySAT
import Cryptol.TypeCheck.PP (dump,ppWithNames)
import Cryptol.Utils.PP
import Cryptol.Utils.Panic(panic)
import qualified Cryptol.Parser.AST as P
import qualified Cryptol.Transform.Specialize as S
import Cryptol.Symbolic (ProverCommand(..), QueryType(..), SatNum(..))
import qualified Cryptol.Symbolic as Symbolic

import Control.DeepSeq
import qualified Control.Exception as X
import Control.Monad hiding (mapM, mapM_)
import qualified Data.ByteString as BS
import Data.Bits ((.&.))
import Data.Char (isSpace,isPunctuation,isSymbol)
import Data.Function (on)
import Data.List (intercalate,nub,sortBy,partition)
import Data.Maybe (fromMaybe,mapMaybe)
import System.Environment (lookupEnv)
import System.Exit (ExitCode(ExitSuccess))
import System.Process (shell,createProcess,waitForProcess)
import qualified System.Process as Process(runCommand)
import System.FilePath((</>), isPathSeparator)
import System.Directory(getHomeDirectory,setCurrentDirectory,doesDirectoryExist)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.IntMap as IntMap
import System.IO(hFlush,stdout)
import System.Random.TF(newTFGen)
import Numeric (showFFloat)
import qualified Data.Text as ST
import qualified Data.Text.Lazy as T

import Prelude ()
import Prelude.Compat

-- Commands --------------------------------------------------------------------

-- | Commands.
data Command
  = Command (REPL ())         -- ^ Successfully parsed command
  | Ambiguous String [String] -- ^ Ambiguous command, list of conflicting
                              --   commands
  | Unknown String            -- ^ The unknown command

-- | Command builder.
data CommandDescr = CommandDescr
  { cNames :: [String]
  , cBody :: CommandBody
  , cHelp :: String
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
  | FilenameArg (FilePath -> REPL ())
  | OptionArg   (String   -> REPL ())
  | ShellArg    (String   -> REPL ())
  | NoArg       (REPL ())


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
  [ CommandDescr [ ":t", ":type" ] (ExprArg typeOfCmd)
    "check the type of an expression"
  , CommandDescr [ ":b", ":browse" ] (ExprTypeArg browseCmd)
    "display the current environment"
  , CommandDescr [ ":?", ":help" ] (ExprArg helpCmd)
    "display a brief description about a function"
  , CommandDescr [ ":s", ":set" ] (OptionArg setOptionCmd)
    "set an environmental option (:set on its own displays current values)"
  , CommandDescr [ ":check" ] (ExprArg (void . qcCmd QCRandom))
    "use random testing to check that the argument always returns true (if no argument, check all properties)"
  , CommandDescr [ ":exhaust" ] (ExprArg (void . qcCmd QCExhaust))
    "use exhaustive testing to prove that the argument always returns true (if no argument, check all properties)"
  , CommandDescr [ ":prove" ] (ExprArg proveCmd)
    "use an external solver to prove that the argument always returns true (if no argument, check all properties)"
  , CommandDescr [ ":sat" ] (ExprArg satCmd)
    "use a solver to find a satisfying assignment for which the argument returns true (if no argument, find an assignment for all properties)"
  , CommandDescr [ ":debug_specialize" ] (ExprArg specializeCmd)
    "do type specialization on a closed expression"
  ]

commandList :: [CommandDescr]
commandList  =
  nbCommandList ++
  [ CommandDescr [ ":q", ":quit" ] (NoArg quitCmd)
    "exit the REPL"
  , CommandDescr [ ":l", ":load" ] (FilenameArg loadCmd)
    "load a module"
  , CommandDescr [ ":r", ":reload" ] (NoArg reloadCmd)
    "reload the currently loaded module"
  , CommandDescr [ ":e", ":edit" ] (FilenameArg editCmd)
    "edit the currently loaded module"
  , CommandDescr [ ":!" ] (ShellArg runShellCmd)
    "execute a command in the shell"
  , CommandDescr [ ":cd" ] (FilenameArg cdCmd)
    "set the current working directory"
  , CommandDescr [ ":m", ":module" ] (FilenameArg moduleCmd)
    "load a module"
  , CommandDescr [ ":w", ":writeByteArray" ] (FileExprArg writeFileCmd)
    "write data of type `fin n => [n][8]` to a file"
  , CommandDescr [ ":readByteArray" ] (FilenameArg readFileCmd)
    "read data from a file as type `fin n => [n][8]`, binding the value to variable `it`"
  ]

genHelp :: [CommandDescr] -> [String]
genHelp cs = map cmdHelp cs
  where
  cmdHelp cmd  = concat [ "  ", cmdNames cmd, pad (cmdNames cmd), cHelp cmd ]
  cmdNames cmd = intercalate ", " (cNames cmd)
  padding      = 2 + maximum (map (length . cmdNames) cs)
  pad n        = replicate (max 0 (padding - length n)) ' '


-- Command Evaluation ----------------------------------------------------------

-- | Run a command.
runCommand :: Command -> REPL ()
runCommand c = case c of

  Command cmd -> cmd `Cryptol.REPL.Monad.catch` handler
    where
    handler re = rPutStrLn "" >> rPrint (pp re)

  Unknown cmd -> rPutStrLn ("Unknown command: " ++ cmd)

  Ambiguous cmd cmds -> do
    rPutStrLn (cmd ++ " is ambiguous, it could mean one of:")
    rPutStrLn ("\t" ++ intercalate ", " cmds)


-- Get the setting we should use for displaying values.
getPPValOpts :: REPL E.PPOpts
getPPValOpts =
  do EnvNum base      <- getUser "base"
     EnvBool ascii    <- getUser "ascii"
     EnvNum infLength <- getUser "infLength"
     return E.PPOpts { E.useBase      = base
                     , E.useAscii     = ascii
                     , E.useInfLength = infLength
                     }

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
      -- This is the point where the value gets forced. We deepseq the
      -- pretty-printed representation of it, rather than the value
      -- itself, leaving it up to the pretty-printer to determine how
      -- much of the value to force
      out <- io $ rethrowEvalError
                $ return $!! show $ pp $ E.WithBase ppOpts val
      rPutStrLn out
    P.LetInput decl -> do
      -- explicitly make this a top-level declaration, so that it will
      -- be generalized if mono-binds is enabled
      replEvalDecl decl

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
     EnvNum testNum  <- getUser "tests"
     case testableType ty of
       Just (sz,vss) | qcMode == QCExhaust || sz <= toInteger testNum -> do
            rPutStrLn "Using exhaustive testing."
            let f _ [] = panic "Cryptol.REPL.Command"
                                    ["Exhaustive testing ran out of test cases"]
                f _ (vs : vss1) = do
                  result <- io $ runOneTest val vs
                  return (result, vss1)
                testSpec = TestSpec {
                    testFn = f
                  , testProp = str
                  , testTotal = sz
                  , testPossible = sz
                  , testRptProgress = ppProgress
                  , testClrProgress = delProgress
                  , testRptFailure = ppFailure
                  , testRptSuccess = do
                      delTesting
                      prtLn $ "passed " ++ show sz ++ " tests."
                      rPutStrLn "Q.E.D."
                  }
            prt testingMsg
            report <- runTests testSpec vss
            return [report]

       Just (sz,_) -> case TestR.testableType ty of
              Nothing   -> raise (TypeNotTestable ty)
              Just gens -> do
                rPutStrLn "Using random testing."
                let testSpec = TestSpec {
                        testFn = \sz' g -> io $ TestR.runOneTest val gens sz' g
                      , testProp = str
                      , testTotal = toInteger testNum
                      , testPossible = sz
                      , testRptProgress = ppProgress
                      , testClrProgress = delProgress
                      , testRptFailure = ppFailure
                      , testRptSuccess = do
                          delTesting
                          prtLn $ "passed " ++ show testNum ++ " tests."
                      }
                prt testingMsg
                g <- io newTFGen
                report <- runTests testSpec g
                when (isPass (reportResult report)) $ do
                  let szD = fromIntegral sz :: Double
                      percent = fromIntegral (testNum * 100) / szD
                      showValNum
                        | sz > 2 ^ (20::Integer) =
                          "2^^" ++ show (lg2 sz)
                        | otherwise = show sz
                  rPutStrLn $ "Coverage: "
                    ++ showFFloat (Just 2) percent "% ("
                    ++ show testNum ++ " of "
                    ++ showValNum ++ " values)"
                return [report]
       Nothing -> return []

  where
  testingMsg = "testing..."

  totProgressWidth = 4    -- 100%

  lg2 :: Integer -> Integer
  lg2 x | x >= 2^(1024::Int) = 1024 + lg2 (x `div` 2^(1024::Int))
        | x == 0       = 0
        | otherwise    = let valNumD = fromIntegral x :: Double
                         in round $ logBase 2 valNumD :: Integer

  prt msg   = rPutStr msg >> io (hFlush stdout)
  prtLn msg = rPutStrLn msg >> io (hFlush stdout)

  ppProgress this tot = unlessBatch $
    let percent = show (div (100 * this) tot) ++ "%"
        width   = length percent
        pad     = replicate (totProgressWidth - width) ' '
    in prt (pad ++ percent)

  del n       = unlessBatch $ prt (replicate n '\BS')
  delTesting  = del (length testingMsg)
  delProgress = del totProgressWidth

  ppFailure failure = do
    delTesting
    opts <- getPPValOpts
    case failure of
      FailFalse [] -> do
        prtLn "FAILED"
      FailFalse vs -> do
        prtLn "FAILED for the following inputs:"
        mapM_ (rPrint . pp . E.WithBase opts) vs
      FailError err [] -> do
        prtLn "ERROR"
        rPrint (pp err)
      FailError err vs -> do
        prtLn "ERROR for the following inputs:"
        mapM_ (rPrint . pp . E.WithBase opts) vs
        rPrint (pp err)
      Pass -> panic "Cryptol.REPL.Command" ["unexpected Test.Pass"]

satCmd, proveCmd :: String -> REPL ()
satCmd = cmdProveSat True
proveCmd = cmdProveSat False

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
cmdProveSat isSat expr = do
  let cexStr | isSat = "satisfying assignment"
             | otherwise = "counterexample"
  EnvString proverName <- getUser "prover"
  EnvString fileName <- getUser "smtfile"
  let mfile = if fileName == "-" then Nothing else Just fileName
  case proverName of
    "offline" -> do
      result <- offlineProveSat isSat expr mfile
      case result of
        Left msg -> rPutStrLn msg
        Right smtlib -> do
          let filename = fromMaybe "standard output" mfile
          let satWord | isSat = "satisfiability"
                      | otherwise = "validity"
          rPutStrLn $
              "Writing to SMT-Lib file " ++ filename ++ "..."
          rPutStrLn $
            "To determine the " ++ satWord ++
            " of the expression, use an external SMT solver."
          case mfile of
            Just path -> io $ writeFile path smtlib
            Nothing -> rPutStr smtlib
    _ -> do
      result <- onlineProveSat isSat expr mfile
      ppOpts <- getPPValOpts
      case result of
        Symbolic.EmptyResult         ->
          panic "REPL.Command" [ "got EmptyResult for online prover query" ]
        Symbolic.ProverError msg     -> rPutStrLn msg
        Symbolic.ThmResult ts        -> do
          rPutStrLn (if isSat then "Unsatisfiable" else "Q.E.D.")
          (t, e) <- mkSolverResult cexStr (not isSat) (Left ts)
          bindItVariable t e
        Symbolic.AllSatResult tevss -> do
          let tess = map (map $ \(t,e,_) -> (t,e)) tevss
              vss  = map (map $ \(_,_,v) -> v)     tevss
              ppvs vs = do
                parseExpr <- replParseExpr expr
                let docs = map (pp . E.WithBase ppOpts) vs
                    -- function application has precedence 3
                    doc = ppPrec 3 parseExpr
                rPrint $ hsep (doc : docs) <+>
                  text (if isSat then "= True" else "= False")
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
                          [ "no satisfying assignments after mkSovlerResult" ]
                  [(t, e)] -> (t, [e])
                  _        -> collectTes resultRecs
          forM_ vss ppvs
          case (ty, exprs) of
            (t, [e]) -> bindItVariable t e
            (t, es ) -> bindItVariables t es

onlineProveSat :: Bool
               -> String -> Maybe FilePath -> REPL Symbolic.ProverResult
onlineProveSat isSat str mfile = do
  EnvString proverName <- getUser "prover"
  EnvBool verbose <- getUser "debug"
  satNum <- getUserSatNum
  parseExpr <- replParseExpr str
  (_, expr, schema) <- replCheckExpr parseExpr
  decls <- fmap M.deDecls getDynEnv
  let cmd = Symbolic.ProverCommand {
          pcQueryType    = if isSat then SatQuery satNum else ProveQuery
        , pcProverName   = proverName
        , pcVerbose      = verbose
        , pcExtraDecls   = decls
        , pcSmtFile      = mfile
        , pcExpr         = expr
        , pcSchema       = schema
        }
  liftModuleCmd $ Symbolic.satProve cmd

offlineProveSat :: Bool -> String -> Maybe FilePath -> REPL (Either String String)
offlineProveSat isSat str mfile = do
  EnvBool verbose <- getUser "debug"
  parseExpr <- replParseExpr str
  (_, expr, schema) <- replCheckExpr parseExpr
  decls <- fmap M.deDecls getDynEnv
  let cmd = Symbolic.ProverCommand {
          pcQueryType    = if isSat then SatQuery (SomeSat 0) else ProveQuery
        , pcProverName   = "offline"
        , pcVerbose      = verbose
        , pcExtraDecls   = decls
        , pcSmtFile      = mfile
        , pcExpr         = expr
        , pcSchema       = schema
        }
  liftModuleCmd $ Symbolic.satProveOffline cmd

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

typeOfCmd :: String -> REPL ()
typeOfCmd str = do

  expr         <- replParseExpr str
  (re,def,sig) <- replCheckExpr expr

  -- XXX need more warnings from the module system
  --io (mapM_ printWarning ws)
  whenDebug (rPutStrLn (dump def))
  (_,_,names) <- getFocusedEnv
  rPrint $ runDoc names $ pp re <+> text ":" <+> pp sig

readFileCmd :: FilePath -> REPL ()
readFileCmd fp = do
  bytes <- replReadFile fp (\err -> rPutStrLn (show err) >> return Nothing)
  case bytes of
      Nothing -> return ()
      Just bs ->
        do pm <- getPrimMap
           let expr = T.eString pm (map (toEnum . fromIntegral) (BS.unpack bs))
               ty   = T.tString (BS.length bs)
           bindItVariable ty expr

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
  serializeValue (E.VSeq _ vs) =
    return $ BS.pack $ map (serializeByte . E.fromVWord) vs
  serializeValue _             =
    panic "Cryptol.REPL.Command.writeFileCmd"
      ["Impossible: Non-VSeq value of type [n][8]."]
  serializeByte (E.BV _ v) = fromIntegral (v .&. 0xFF)

reloadCmd :: REPL ()
reloadCmd  = do
  mb <- getLoadedMod
  case mb of
    Just m  -> loadCmd (lPath m)
    Nothing -> return ()


editCmd :: String -> REPL ()
editCmd path
  | null path = do
      mb <- getLoadedMod
      case mb of

        Just m -> do
          success <- replEdit (lPath m)
          if success
             then loadCmd (lPath m)
             else return ()

        Nothing   -> do
          rPutStrLn "No files to edit."
          return ()

  | otherwise = do
      _  <- replEdit path
      mb <- getLoadedMod
      case mb of
        Nothing -> loadCmd path
        Just _  -> return ()

moduleCmd :: String -> REPL ()
moduleCmd modString
  | null modString = return ()
  | otherwise      = do
      case parseModName modString of
        Just m -> loadCmd =<< liftModuleCmd (M.findModule m)
        Nothing -> rPutStrLn "Invalid module name."

loadPrelude :: REPL ()
loadPrelude  = moduleCmd $ show $ pp M.preludeName

loadCmd :: FilePath -> REPL ()
loadCmd path
  | null path = return ()
  | otherwise = do
      setLoadedMod LoadedModule
        { lName = Nothing
        , lPath = path
        }

      m <- liftModuleCmd (M.loadModuleByPath path)
      whenDebug (rPutStrLn (dump m))
      setLoadedMod LoadedModule
        { lName = Just (T.mName m)
        , lPath = path
        }
      setDynEnv mempty

quitCmd :: REPL ()
quitCmd  = stop


browseCmd :: String -> REPL ()
browseCmd pfx = do
  (iface,names,disp) <- getFocusedEnv
  let (visibleTypes,visibleDecls) = M.visibleNames names

      (visibleType,visibleDecl)
        | null pfx  =
          ((`Set.member` visibleTypes)
          ,(`Set.member` visibleDecls))

        | otherwise =
          (\n -> n `Set.member` visibleTypes && pfx `isNamePrefix` n
          ,\n -> n `Set.member` visibleDecls && pfx `isNamePrefix` n)

  browseTSyns    visibleType iface disp
  browseNewtypes visibleType iface disp
  browseVars     visibleDecl iface disp

browseTSyns :: (M.Name -> Bool) -> M.IfaceDecls -> NameDisp -> REPL ()
browseTSyns isVisible M.IfaceDecls { .. } names = do
  let tsyns = sortBy (M.cmpNameDisplay names `on` T.tsName)
              [ ts | ts <- Map.elems ifTySyns, isVisible (T.tsName ts) ]
  unless (null tsyns) $ do
    rPutStrLn "Type Synonyms"
    rPutStrLn "============="
    rPrint (runDoc names (nest 4 (vcat (map pp tsyns))))
    rPutStrLn ""

browseNewtypes :: (M.Name -> Bool) -> M.IfaceDecls -> NameDisp -> REPL ()
browseNewtypes isVisible M.IfaceDecls { .. } names = do
  let nts = sortBy (M.cmpNameDisplay names `on` T.ntName)
            [ nt | nt <- Map.elems ifNewtypes, isVisible (T.ntName nt) ]
  unless (null nts) $ do
    rPutStrLn "Newtypes"
    rPutStrLn "========"
    rPrint (runDoc names (nest 4 (vcat (map T.ppNewtypeShort nts))))
    rPutStrLn ""

browseVars :: (M.Name -> Bool) -> M.IfaceDecls -> NameDisp -> REPL ()
browseVars isVisible M.IfaceDecls { .. } names = do
  let vars = sortBy (M.cmpNameDisplay names `on` M.ifDeclName)
             [ d | d <- Map.elems ifDecls, isVisible (M.ifDeclName d) ]


  let isProp p     = T.PragmaProperty `elem` (M.ifDeclPragmas p)
      (props,syms) = partition isProp vars

  ppBlock "Properties" props
  ppBlock "Symbols"    syms

  where
  ppBlock name xs = unless (null xs) $
    do rPutStrLn name
       rPutStrLn (replicate (length name) '=')
       let ppVar M.IfaceDecl { .. } = pp ifDeclName <+> char ':' <+> pp ifDeclSig
       rPrint (runDoc names (nest 4 (vcat (map ppVar xs))))
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
      Just (EnvString s)   -> rPutStrLn (k ++ " = " ++ s)
      Just (EnvProg p as)  -> rPutStrLn (k ++ " = " ++ intercalate " " (p:as))
      Just (EnvNum n)      -> rPutStrLn (k ++ " = " ++ show n)
      Just (EnvBool True)  -> rPutStrLn (k ++ " = on")
      Just (EnvBool False) -> rPutStrLn (k ++ " = off")
      Nothing              -> do rPutStrLn ("Unknown user option: `" ++ k ++ "`")
                                 when (any isSpace k) $ do
                                   let (k1, k2) = break isSpace k
                                   rPutStrLn ("Did you mean: `:set " ++ k1 ++ " =" ++ k2 ++ "`?")


-- XXX at the moment, this can only look at declarations.
helpCmd :: String -> REPL ()
helpCmd cmd
  | null cmd  = mapM_ rPutStrLn (genHelp commandList)
  | otherwise =
    case parseHelpName cmd of
      Just qname ->
        do (env,rnEnv,nameEnv) <- getFocusedEnv
           name <- liftModuleCmd (M.renameVar rnEnv qname)
           case Map.lookup name (M.ifDecls env) of
             Just M.IfaceDecl { .. } ->
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

                  case ifDeclDoc of
                    Just str -> rPutStrLn ('\n' : str)
                    Nothing  -> return ()

             Nothing -> rPutStrLn "// No documentation is available."

      Nothing ->
           rPutStrLn ("Unable to parse name: " ++ cmd)


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
handleCtrlC :: REPL ()
handleCtrlC  = rPutStrLn "Ctrl-C"


-- Utilities -------------------------------------------------------------------

isNamePrefix :: String -> M.Name -> Bool
isNamePrefix pfx =
  let pfx' = ST.pack pfx
   in \n -> case M.nameInfo n of
              M.Declared _ -> pfx' `ST.isPrefixOf` M.identText (M.nameIdent n)
              M.Parameter  -> False


{-
printWarning :: (Range,Warning) -> IO ()
printWarning = print . ppWarning

printError :: (Range,Error) -> IO ()
printError = print . ppError
-}

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
liftModuleCmd cmd = moduleCmdResult =<< io . cmd =<< getModuleEnv

moduleCmdResult :: M.ModuleRes a -> REPL a
moduleCmdResult (res,ws0) = do
  EnvBool warnDefaulting <- getUser "warnDefaulting"
  EnvBool warnShadowing  <- getUser "warnShadowing"
  -- XXX: let's generalize this pattern
  let isDefaultWarn (T.DefaultingTo _ _) = True
      isDefaultWarn _ = False

      filterDefaults w | warnDefaulting = Just w
      filterDefaults (M.TypeCheckWarnings xs) =
        case filter (not . isDefaultWarn . snd) xs of
          [] -> Nothing
          ys -> Just (M.TypeCheckWarnings ys)
      filterDefaults w = Just w

      isShadowWarn (M.SymbolShadowed _ _ _) = True

      filterShadowing w | warnShadowing = Just w
      filterShadowing (M.RenamerWarnings xs) =
        case filter (not . isShadowWarn) xs of
          [] -> Nothing
          ys -> Just (M.RenamerWarnings ys)
      filterShadowing w = Just w

  let ws = mapMaybe filterDefaults . mapMaybe filterShadowing $ ws0
  (_,_,names) <- getFocusedEnv
  mapM_ (rPrint . runDoc names . pp) ws
  case res of
    Right (a,me') -> setModuleEnv me' >> return a
    Left err      -> raise (ModuleSystemError names err)

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

replEvalExpr :: P.Expr P.PName -> REPL (E.Value, T.Type)
replEvalExpr expr =
  do (_,def,sig) <- replCheckExpr expr

     me <- getModuleEnv
     let cfg = M.meSolverConfig me
     mbDef <- io $ CrySAT.withSolver cfg (\s -> defaultReplExpr s def sig)

     (def1,ty) <-
        case mbDef of
          Nothing -> raise (EvalPolyError sig)
          Just (tys,def1) ->
            do let nms = T.addTNames (T.sVars sig) IntMap.empty
               mapM_ (warnDefault nms) tys
               let su = T.listSubst [ (T.tpVar a, t) | (a,t) <- tys ]
               return (def1, T.apSubst su (T.sType sig))

     val <- liftModuleCmd (M.evalExpr def1)
     _ <- io $ rethrowEvalError $ X.evaluate val
     whenDebug (rPutStrLn (dump def1))
     -- add "it" to the namespace
     bindItVariable ty def1
     return (val,ty)
  where
  warnDefault ns (x,t) =
        rPrint $ text "Assuming" <+> ppWithNames ns x <+> text "=" <+> pp t

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
  freshIt <- freshName itIdent
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
      FilenameArg body -> Just (Command (body =<< expandHome args'))
      OptionArg   body -> Just (Command (body args'))
      ShellArg    body -> Just (Command (body args'))
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
