-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE CPP, PatternGuards, FlexibleContexts #-}
module REPL.Command (
    -- * Commands
    Command(..), CommandDescr(..), CommandBody(..)
  , parseCommand
  , runCommand
  , splitCommand
  , findCommand
  , findCommandExact
  , findNbCommand

  , moduleCmd, loadCmd, loadPrelude

    -- Misc utilities
  , handleCtrlC
  , sanitize

    -- To support Notebook interface (might need to refactor)
  , replParse
  , liftModuleCmd
  , moduleCmdResult
  ) where

import REPL.Monad
import REPL.Trie

import qualified Cryptol.ModuleSystem as M
import qualified Cryptol.ModuleSystem.Base as M (preludeName)
import qualified Cryptol.ModuleSystem.NamingEnv as M

import qualified Cryptol.Eval.Value as E
import qualified Cryptol.Testing.Random  as TestR
import qualified Cryptol.Testing.Exhaust as TestX
import Cryptol.Parser
    (parseExprWith,parseReplWith,ParseError(),Config(..),defaultConfig,parseModName)
import Cryptol.Parser.Position (emptyRange,getLoc)
import qualified Cryptol.TypeCheck.AST as T
import qualified Cryptol.TypeCheck.Subst as T
import qualified Cryptol.TypeCheck.InferTypes as T
import Cryptol.TypeCheck.PP (dump,ppWithNames)
import Cryptol.TypeCheck.Defaulting(defaultExpr)
import Cryptol.Utils.PP
import Cryptol.Utils.Panic(panic)
import qualified Cryptol.Parser.AST as P
import Cryptol.Prims.Doc(helpDoc)
import qualified Cryptol.Transform.Specialize as S
import qualified Cryptol.Symbolic

import qualified Control.Exception as X
import Control.Monad (guard,unless,forM_,when)
import Data.Char (isSpace,isPunctuation,isSymbol)
import Data.Function (on)
import Data.List (intercalate,isPrefixOf)
import Data.Maybe (fromMaybe,mapMaybe)
import Data.Monoid (mempty)
import System.Exit (ExitCode(ExitSuccess))
import System.Process (shell,createProcess,waitForProcess)
import qualified System.Process as Process(runCommand)
import System.FilePath((</>), isPathSeparator)
import System.Directory(getHomeDirectory,setCurrentDirectory,doesDirectoryExist)
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import System.IO(hFlush,stdout)
import System.Random.TF(newTFGen)
import Numeric (showFFloat)

#if __GLASGOW_HASKELL__ < 706
import Control.Monad (liftM)
import qualified Text.ParserCombinators.ReadP as P
import Text.Read hiding (step)
import System.Environment (getEnvironment)

lookupEnv :: String -> IO (Maybe String)
lookupEnv key = lookup key `liftM` getEnvironment

readEither :: Read a => String -> Either String a
readEither s =
  case [ x | (x,"") <- readPrec_to_S read' minPrec s ] of
    [x] -> Right x
    []  -> Left "Prelude.read: no parse"
    _   -> Left "Prelude.read: ambiguous parse"
 where
  read' =
    do x <- readPrec
       lift P.skipSpaces
       return x

-- | Parse a string using the 'Read' instance.
-- Succeeds if there is exactly one valid result.
readMaybe :: Read a => String -> Maybe a
readMaybe s = case readEither s of
                Left _  -> Nothing
                Right a -> Just a
#else
import System.Environment (lookupEnv)
#endif

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
    "display a brief description about a built-in operator"
  , CommandDescr [ ":s", ":set" ] (OptionArg setOptionCmd)
    "set an environmental option (:set on its own displays current values)"
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

  , CommandDescr [ ":check" ] (ExprArg (qcCmd QCRandom))
    "use random testing to check that the argument always returns true (if no argument, check all properties)"
  , CommandDescr [ ":exhaust" ] (ExprArg (qcCmd QCExhaust))
    "use exhaustive testing to prove that the argument always returns true (if no argument, check all properties)"
  , CommandDescr [ ":prove" ] (ExprArg proveCmd)
    "use an external solver to prove that the argument always returns true (if no argument, check all properties)"
  , CommandDescr [ ":sat" ] (ExprArg satCmd)
    "use a solver to find a satisfying assignment for which the argument returns true (if no argument, find an assignment for all properties)"
  , CommandDescr [ ":debug_specialize" ] (ExprArg specializeCmd)
    "do type specialization on a closed expression"
  ]

genHelp :: [CommandDescr] -> [String]
genHelp cs = map cmdHelp cs
  where
  cmdHelp cmd = concat [ "  ", cmdNames cmd, pad (cmdNames cmd), cHelp cmd ]
  cmdNames cmd = intercalate ", " (cNames cmd)
  padding     = 2 + maximum (map (length . cmdNames) cs)
  pad n       = replicate (max 0 (padding - length n)) ' '


-- Command Evaluation ----------------------------------------------------------

-- | Run a command.
runCommand :: Command -> REPL ()
runCommand c = case c of

  Command cmd -> cmd `REPL.Monad.catch` handler
    where
    handler re = io (putStrLn "" >> print (pp re))

  Unknown cmd -> io (putStrLn ("Unknown command: " ++ cmd))

  Ambiguous cmd cmds -> io $ do
    putStrLn (cmd ++ " is ambiguous, it could mean one of:")
    putStrLn ("\t" ++ intercalate ", " cmds)


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
  ri <- replParseInput str
  case ri of
    P.ExprInput expr -> do
      (val,_ty) <- replEvalExpr expr
      ppOpts <- getPPValOpts
      io $ rethrowEvalError $ print $ pp $ E.WithBase ppOpts val
    P.LetInput decl -> do
      -- explicitly make this a top-level declaration, so that it has a chance
      -- to be generalized if mono-binds is enabled
      replEvalDecl decl

data QCMode = QCRandom | QCExhaust deriving (Eq, Show)

-- | Randomly test a property, or exhaustively check it if the number
-- of values in the type under test is smaller than the @tests@
-- environment variable, or we specify exhaustive testing.
qcCmd :: QCMode -> String -> REPL ()
qcCmd qcMode "" =
  do xs <- getPropertyNames
     if null xs
        then io $ putStrLn "There are no properties in scope."
        else forM_ xs $ \x ->
               do io $ putStr $ "property " ++ x ++ " "
                  qcCmd qcMode x

qcCmd qcMode str =
  do expr <- replParseExpr str
     (val,ty) <- replEvalExpr expr
     EnvNum testNum  <- getUser "tests"
     case TestX.testableType ty of
       Just (sz,vss) | qcMode == QCExhaust || sz <= toInteger testNum ->
         do io $ putStrLn "Using exhaustive testing."
            let doTest _ [] = panic "We've unexpectedly run out of test cases"
                                    []
                doTest _ (vs : vss1) =
                    if TestX.runTest val vs
                        then (Nothing, vss1)
                        else (Just vs, vss1)
            ok <- go doTest sz 0 vss
            when ok $ io $ putStrLn "Q.E.D."

       n -> case TestR.testableType ty of
              Nothing   -> raise (TypeNotTestable ty)
              Just gens ->
                do io $ putStrLn "Using random testing."
                   prt testingMsg
                   g <- io newTFGen
                   ok <- go (TestR.runTest val gens) testNum 0 g
                   when ok $
                     case n of
                       Just (valNum,_) ->
                         do let valNumD = fromIntegral valNum :: Double
                                percent = fromIntegral (testNum * 100)
                                        / valNumD
                                showValNum
                                   | valNum > 2 ^ (20::Integer) =
                                       "2^^" ++ show (round $ logBase 2 valNumD :: Integer)
                                   | otherwise = show valNum
                            io $ putStrLn $ "Coverage: "
                                     ++ showFFloat (Just 2) percent "% ("
                                     ++ show testNum ++ " of "
                                     ++ showValNum ++ " values)"
                       Nothing -> return ()

  where
  testingMsg = "testing..."

  totProgressWidth = 4    -- 100%

  prt msg   = io (putStr msg >> hFlush stdout)
  prtLn msg = io (putStrLn msg >> hFlush stdout)

  ppProgress this tot = unlessBatch $
    let percent = show (div (100 * this) tot) ++ "%"
        width   = length percent
        pad     = replicate (totProgressWidth - width) ' '
    in prt (pad ++ percent)

  del n       = unlessBatch $ prt (replicate n '\BS')
  delTesting  = del (length testingMsg)
  delProgress = del totProgressWidth

  go _ totNum testNum _
     | testNum >= totNum =
         do delTesting
            prtLn $ "passed " ++ show totNum ++ " tests."
            return True

  go doTest totNum testNum st =
     do ppProgress testNum totNum
        res <- io $ rethrowEvalError $ X.evaluate $ doTest (div (100 * (1 + testNum)) totNum) st
        case res of
          (Nothing, st1) -> do delProgress
                               go doTest totNum (testNum + 1) st1
          (Just vs, _g1) ->
             do opts <- getPPValOpts
                do delProgress
                   delTesting
                   prtLn "FAILED for the following inputs:"
                   io $ mapM_ (print . pp . E.WithBase opts) vs
                   return False

satCmd, proveCmd :: String -> REPL ()
satCmd = cmdProveSat True
proveCmd = cmdProveSat False

-- | Run a SAT solver on the given expression. Binds the @it@ variable
-- to a record whose form depends on the expression given. See ticket
-- #66 for a discussion of this design.
cmdProveSat :: Bool -> String -> REPL ()
cmdProveSat isSat "" =
  do xs <- getPropertyNames
     if null xs
        then io $ putStrLn "There are no properties in scope."
        else forM_ xs $ \x ->
               do io $ putStr $ "property " ++ x ++ " "
                  cmdProveSat isSat x
cmdProveSat isSat str = do
  EnvString proverName <- getUser "prover"
  EnvString fileName <- getUser "smtfile"
  let mfile = if fileName == "-" then Nothing else Just fileName
  case proverName of
    "offline" -> offlineProveSat isSat str mfile
    _ -> onlineProveSat isSat str proverName mfile

onlineProveSat :: Bool
               -> String -> String -> Maybe FilePath -> REPL ()
onlineProveSat isSat str proverName mfile = do
  EnvBool iteSolver <- getUser "iteSolver"
  EnvBool verbose <- getUser "debug"
  let cexStr | isSat = "satisfying assignment"
             | otherwise = "counterexample"
  parseExpr <- replParseExpr str
  (expr, schema) <- replCheckExpr parseExpr
  denv <- getDynEnv
  result <- liftModuleCmd $
    Cryptol.Symbolic.satProve isSat (proverName, iteSolver, verbose)
                                    (M.deDecls denv)
                                    mfile
                                    (expr, schema)
  ppOpts <- getPPValOpts
  case result of
    Left msg           -> io $ putStrLn msg
    Right (Left ts)    -> do
      io $ putStrLn (if isSat then "Unsatisfiable." else "Q.E.D.")
      let (t, e) = mkSolverResult cexStr (not isSat) (Left ts)
      bindItVariable t e
    Right (Right tevs) -> do
      let vs = map (\(_,_,v) -> v) tevs
          tes = map (\(t,e,_) -> (t,e)) tevs
          doc = ppPrec 3 parseExpr -- function application has precedence 3
          docs = map (pp . E.WithBase ppOpts) vs
      io $ print $ hsep (doc : docs) <+>
                   text (if isSat then "= True" else "= False")
      -- bind the counterexample to `it`
      let (t, e) = mkSolverResult cexStr isSat (Right tes)
      bindItVariable t e

offlineProveSat :: Bool -> String -> Maybe FilePath -> REPL ()
offlineProveSat isSat str mfile = do
  EnvBool useIte <- getUser "iteSolver"
  EnvBool vrb <- getUser "debug"
  parseExpr <- replParseExpr str
  exsch <- replCheckExpr parseExpr
  decls <- fmap M.deDecls getDynEnv
  result <- liftModuleCmd $
    Cryptol.Symbolic.satProveOffline isSat useIte vrb decls mfile exsch
  case result of
    Left msg -> io $ putStrLn msg
    Right () -> return ()

-- | Make a type/expression pair that is suitable for binding to @it@
-- after running @:sat@ or @:prove@
mkSolverResult :: String
               -> Bool
               -> Either [T.Type] [(T.Type, T.Expr)]
               -> (T.Type, T.Expr)
mkSolverResult thing result earg = (rty, re)
  where
    rName = T.Name "result"
    rty = T.TRec $ [(rName, T.tBit )] ++ map fst argF
    re  = T.ERec $ [(rName, resultE)] ++ map snd argF
    resultE = if result then T.eTrue else T.eFalse
    mkArgs tes = reverse (go tes [] (1 :: Int))
      where
        go [] fs _ = fs
        go ((t, e):tes') fs n = go tes' (((argName, t), (argName, e)):fs) (n+1)
          where argName = T.Name ("arg" ++ show n)
    argF = case earg of
      Left ts -> mkArgs $ (map addError) ts
        where addError t = (t, T.eError t ("no " ++ thing ++ " available"))
      Right tes -> mkArgs tes

specializeCmd :: String -> REPL ()
specializeCmd str = do
  parseExpr <- replParseExpr str
  (expr, schema) <- replCheckExpr parseExpr
  spexpr <- replSpecExpr expr
  io $ putStrLn  "Expression type:"
  io $ print    $ pp schema
  io $ putStrLn  "Original expression:"
  io $ putStrLn $ dump expr
  io $ putStrLn  "Specialized expression:"
  io $ putStrLn $ dump spexpr

typeOfCmd :: String -> REPL ()
typeOfCmd str = do
  expr      <- replParseExpr str
  (def,sig) <- replCheckExpr expr

  -- XXX need more warnings from the module system
  --io (mapM_ printWarning ws)
  whenDebug (io (putStrLn (dump def)))
  io $ print $ pp expr <+> text ":" <+> pp sig

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
          io (putStrLn "No files to edit.")
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
        Nothing -> io $ putStrLn "Invalid module name."

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
      whenDebug (io (putStrLn (dump m)))
      setLoadedMod LoadedModule
        { lName = Just (T.mName m)
        , lPath = path
        }
      setDynEnv mempty

quitCmd :: REPL ()
quitCmd  = stop


browseCmd :: String -> REPL ()
browseCmd pfx = do
  browseTSyns pfx
  browseNewtypes pfx
  browseVars pfx

browseTSyns :: String -> REPL ()
browseTSyns pfx = do
  tsyns <- getTSyns
  let tsyns' = Map.filterWithKey (\k _ -> pfx `isNamePrefix` k) tsyns
  unless (Map.null tsyns') $ io $ do
    putStrLn "Type Synonyms"
    putStrLn "============="
    let ppSyn (qn,T.TySyn _ ps cs ty) = pp (T.TySyn qn ps cs ty)
    print (nest 4 (vcat (map ppSyn (Map.toList tsyns'))))
    putStrLn ""

browseNewtypes :: String -> REPL ()
browseNewtypes pfx = do
  nts <- getNewtypes
  let nts' = Map.filterWithKey (\k _ -> pfx `isNamePrefix` k) nts
  unless (Map.null nts') $ io $ do
    putStrLn "Newtypes"
    putStrLn "========"
    let ppNT (qn,nt) = T.ppNewtypeShort (nt { T.ntName = qn })
    print (nest 4 (vcat (map ppNT (Map.toList nts'))))
    putStrLn ""

browseVars :: String -> REPL ()
browseVars pfx = do
  vars <- getVars
  let allNames = vars
          {- This shows the built-ins as well:
             Map.union vars
                  (Map.fromList [ (Name x,t) | (x,(_,t)) <- builtIns ]) -}
      vars' = Map.filterWithKey (\k _ -> pfx `isNamePrefix` k) allNames

      isProp p     = T.PragmaProperty `elem` (M.ifDeclPragmas p)
      (props,syms) = Map.partition isProp vars'

  ppBlock "Properties" props
  ppBlock "Symbols" syms

  where
  ppBlock name xs =
    unless (Map.null xs) $ io $ do
      putStrLn name
      putStrLn (replicate (length name) '=')
      let step k d acc =
              pp k <+> char ':' <+> pp (M.ifDeclSig d) : acc
      print (nest 4 (vcat (Map.foldrWithKey step [] xs)))
      putStrLn ""



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
    io $ case ev of
           Just (EnvString s)   -> putStrLn (k ++ " = " ++ s)
           Just (EnvNum n)      -> putStrLn (k ++ " = " ++ show n)
           Just (EnvBool True)  -> putStrLn (k ++ " = on")
           Just (EnvBool False) -> putStrLn (k ++ " = off")
           Nothing              -> do putStrLn ("Unknown user option: `" ++ k ++ "`")
                                      when (any isSpace k) $ do
                                        let (k1, k2) = break isSpace k
                                        putStrLn ("Did you mean: `:set " ++ k1 ++ " =" ++ k2 ++ "`?")


helpCmd :: String -> REPL ()
helpCmd cmd
  | null cmd = io (mapM_ putStrLn (genHelp commandList))
  | Just (ec,_) <- lookup cmd builtIns =
                io $ print $ helpDoc ec
  | otherwise = do io $ putStrLn $ "// No documentation is available."
                   typeOfCmd cmd


runShellCmd :: String -> REPL ()
runShellCmd cmd
  = io $ do h <- Process.runCommand cmd
            _ <- waitForProcess h
            return ()

cdCmd :: FilePath -> REPL ()
cdCmd f | null f = io $ putStrLn $ "[error] :cd requires a path argument"
        | otherwise = do
  exists <- io $ doesDirectoryExist f
  if exists
    then io $ setCurrentDirectory f
    else raise $ DirectoryNotFound f

-- C-c Handlings ---------------------------------------------------------------

-- XXX this should probably do something a bit more specific.
handleCtrlC :: REPL ()
handleCtrlC  = io (putStrLn "Ctrl-C")


-- Utilities -------------------------------------------------------------------

isNamePrefix :: String -> P.QName -> Bool
isNamePrefix pfx n = case n of
  P.QName _ (P.Name _) -> pfx `isPrefixOf` pretty n
  _                    -> False

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

replParseInput :: String -> REPL P.ReplInput
replParseInput = replParse $ parseReplWith interactiveConfig

replParseExpr :: String -> REPL P.Expr
replParseExpr = replParse $ parseExprWith interactiveConfig

interactiveConfig :: Config
interactiveConfig = defaultConfig { cfgSource = "<interactive>" }

liftModuleCmd :: M.ModuleCmd a -> REPL a
liftModuleCmd cmd = moduleCmdResult =<< io . cmd =<< getModuleEnv

moduleCmdResult :: M.ModuleRes a -> REPL a
moduleCmdResult (res,ws0) = do
  EnvBool yes <- getUser "warnDefaulting"
  let isDefaultWarn (T.DefaultingTo _ _) = True
      isDefaultWarn _ = False

      filterDefaults (M.TypeCheckWarnings xs) =
        case filter (not . isDefaultWarn . snd) xs of
          [] -> Nothing
          ys -> Just (M.TypeCheckWarnings ys)
      filterDefaults w = Just w

  let ws = if yes then ws0
                  else mapMaybe filterDefaults ws0
  io (mapM_ (print . pp) ws)
  case res of
    Right (a,me') -> setModuleEnv me' >> return a
    Left err      -> raise (ModuleSystemError err)

replCheckExpr :: P.Expr -> REPL (T.Expr,T.Schema)
replCheckExpr e = liftModuleCmd $ M.checkExpr e

-- | Check declarations as though they were defined at the top-level.
replCheckDecls :: [P.Decl] -> REPL [T.DeclGroup]
replCheckDecls ds = do
  npds <- liftModuleCmd $ M.noPat ds
  denv <- getDynEnv
  let dnames = M.namingEnv npds
  ne' <- M.travNamingEnv uniqify dnames
  let denv' = denv { M.deNames = ne' `M.shadowing` M.deNames denv }
      undo exn = do
        -- if typechecking fails, we want to revert changes to the
        -- dynamic environment and reraise
        setDynEnv denv
        raise exn
  setDynEnv denv'
  let topDecls = [ P.Decl (P.TopLevel P.Public d) | d <- npds ]
  catch (liftModuleCmd $ M.checkDecls topDecls) undo

replSpecExpr :: T.Expr -> REPL T.Expr
replSpecExpr e = liftModuleCmd $ S.specialize e

replEvalExpr :: P.Expr -> REPL (E.Value, T.Type)
replEvalExpr expr =
  do (def,sig) <- replCheckExpr expr

     let range = fromMaybe emptyRange (getLoc expr)
     (def1,ty) <-
        case defaultExpr range def sig of
          Nothing -> raise (EvalPolyError sig)
          Just (tys,def1) ->
            do let nms = T.addTNames (T.sVars sig) IntMap.empty
               io $ mapM_ (warnDefault nms) tys
               let su = T.listSubst [ (T.tpVar a, t) | (a,t) <- tys ]
               return (def1, T.apSubst su (T.sType sig))

     val <- liftModuleCmd (M.evalExpr def1)
     _ <- io $ rethrowEvalError $ X.evaluate val
     whenDebug (io (putStrLn (dump def1)))
     -- add "it" to the namespace
     bindItVariable ty def1
     return (val,ty)
  where
  warnDefault ns (x,t) =
        print $ text "Assuming" <+> ppWithNames ns x <+> text "=" <+> pp t

-- | Creates a fresh binding of "it" to the expression given, and adds
-- it to the current dynamic environment
bindItVariable :: T.Type -> T.Expr -> REPL ()
bindItVariable ty expr = do
  let it = T.QName Nothing (P.Name "it")
  freshIt <- uniqify it
  let dg = T.NonRecursive decl
      schema = T.Forall { T.sVars  = []
                        , T.sProps = []
                        , T.sType  = ty
                        }
      decl = T.Decl { T.dName       = freshIt
                    , T.dSignature  = schema
                    , T.dDefinition = expr
                    , T.dPragmas    = []
                    }
  liftModuleCmd (M.evalDecls [dg])
  denv <- getDynEnv
  let en = M.EFromBind (P.Located emptyRange freshIt)
      nenv' = M.singletonE it en `M.shadowing` M.deNames denv
  setDynEnv $ denv { M.deNames = nenv' }

replEvalDecl :: P.Decl -> REPL ()
replEvalDecl decl = do
  dgs <- replCheckDecls [decl]
  whenDebug (mapM_ (\dg -> (io (putStrLn (dump dg)))) dgs)
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
