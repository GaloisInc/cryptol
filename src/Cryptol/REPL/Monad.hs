-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}

module Cryptol.REPL.Monad (
    -- * REPL Monad
    REPL(..), runREPL
  , io
  , raise
  , stop
  , catch
  , rPutStrLn
  , rPutStr
  , rPrint

    -- ** Errors
  , REPLException(..)
  , rethrowEvalError

    -- ** Environment
  , getModuleEnv, setModuleEnv
  , getDynEnv, setDynEnv
  , uniqify
  , getTSyns, getNewtypes, getVars
  , whenDebug
  , getExprNames
  , getTypeNames
  , getPropertyNames
  , LoadedModule(..), getLoadedMod, setLoadedMod
  , setSearchPath, prependSearchPath
  , builtIns
  , getPrompt
  , shouldContinue
  , unlessBatch
  , asBatch
  , disableLet
  , enableLet
  , getLetEnabled
  , updateREPLTitle
  , setUpdateREPLTitle

    -- ** Config Options
  , EnvVal(..)
  , OptionDescr(..)
  , setUser, getUser, tryGetUser
  , userOptions
  , getUserSatNum

    -- ** Configurable Output
  , getPutStr
  , setPutStr

    -- ** Smoke Test
  , smokeTest
  , Smoke(..)

  ) where

import Cryptol.REPL.Trie

import Cryptol.Prims.Types(typeOf)
import Cryptol.Prims.Syntax(ECon(..),ppPrefix)
import Cryptol.Eval (EvalError)
import qualified Cryptol.ModuleSystem as M
import qualified Cryptol.ModuleSystem.Env as M
import qualified Cryptol.ModuleSystem.NamingEnv as M
import Cryptol.Parser (ParseError,ppError)
import Cryptol.Parser.NoInclude (IncludeError,ppIncludeError)
import Cryptol.Parser.NoPat (Error)
import qualified Cryptol.TypeCheck.AST as T
import qualified Cryptol.TypeCheck as T
import Cryptol.Utils.PP
import Cryptol.Utils.Panic (panic)
import qualified Cryptol.Parser.AST as P
import Cryptol.Symbolic (proverNames, lookupProver)

import Control.Monad (ap,unless,when)
import Data.Char (isSpace)
import Data.IORef
    (IORef,newIORef,readIORef,modifyIORef)
import Data.List (intercalate, isPrefixOf, unfoldr)
import Data.Maybe (catMaybes)
import Data.Typeable (Typeable)
import System.Directory (findExecutable)
import qualified Control.Exception as X
import qualified Data.Map as Map
import Text.Read (readMaybe)

import Data.SBV.Dynamic (sbvCheckSolverInstallation)

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative ((<$>), Applicative(..))
import Data.Monoid (Monoid(..))
#endif

-- REPL Environment ------------------------------------------------------------

data LoadedModule = LoadedModule
  { lName :: Maybe P.ModName -- ^ Focused module
  , lPath :: FilePath        -- ^ Focused file
  }

-- | REPL RW Environment.
data RW = RW
  { eLoadedMod   :: Maybe LoadedModule
  , eContinue    :: Bool
  , eIsBatch     :: Bool
  , eModuleEnv   :: M.ModuleEnv
  , eNameSupply  :: Int
  , eUserEnv     :: UserEnv
  , ePutStr      :: String -> IO ()
  , eLetEnabled  :: Bool
  , eUpdateTitle :: REPL ()
  }

-- | Initial, empty environment.
defaultRW :: Bool -> IO RW
defaultRW isBatch = do
  env <- M.initialModuleEnv
  return RW
    { eLoadedMod   = Nothing
    , eContinue    = True
    , eIsBatch     = isBatch
    , eModuleEnv   = env
    , eNameSupply  = 0
    , eUserEnv     = mkUserEnv userOptions
    , ePutStr      = putStr
    , eLetEnabled  = True
    , eUpdateTitle = return ()
    }

-- | Build up the prompt for the REPL.
mkPrompt :: RW -> String
mkPrompt rw
  | eIsBatch rw = ""
  | otherwise   = maybe "cryptol" pretty (lName =<< eLoadedMod rw) ++ "> "

-- REPL Monad ------------------------------------------------------------------

-- | REPL_ context with InputT handling.
newtype REPL a = REPL { unREPL :: IORef RW -> IO a }

-- | Run a REPL action with a fresh environment.
runREPL :: Bool -> REPL a -> IO a
runREPL isBatch m = do
  ref <- newIORef =<< defaultRW isBatch
  unREPL m ref

instance Functor REPL where
  {-# INLINE fmap #-}
  fmap f m = REPL (\ ref -> fmap f (unREPL m ref))

instance Applicative REPL where
  {-# INLINE pure #-}
  pure = return
  {-# INLINE (<*>) #-}
  (<*>) = ap

instance Monad REPL where
  {-# INLINE return #-}
  return x = REPL (\_ -> return x)

  {-# INLINE (>>=) #-}
  m >>= f = REPL $ \ref -> do
    x <- unREPL m ref
    unREPL (f x) ref


-- Exceptions ------------------------------------------------------------------

-- | REPL exceptions.
data REPLException
  = ParseError ParseError
  | FileNotFound FilePath
  | DirectoryNotFound FilePath
  | NoPatError [Error]
  | NoIncludeError [IncludeError]
  | EvalError EvalError
  | ModuleSystemError M.ModuleError
  | EvalPolyError T.Schema
  | TypeNotTestable T.Type
    deriving (Show,Typeable)

instance X.Exception REPLException

instance PP REPLException where
  ppPrec _ re = case re of
    ParseError e         -> ppError e
    FileNotFound path    -> sep [ text "File"
                                , text ("`" ++ path ++ "'")
                                , text"not found"
                                ]
    DirectoryNotFound path -> sep [ text "Directory"
                                  , text ("`" ++ path ++ "'")
                                  , text"not found or not a directory"
                                  ]
    NoPatError es        -> vcat (map pp es)
    NoIncludeError es    -> vcat (map ppIncludeError es)
    ModuleSystemError me -> pp me
    EvalError e          -> pp e
    EvalPolyError s      -> text "Cannot evaluate polymorphic value."
                         $$ text "Type:" <+> pp s
    TypeNotTestable t    -> text "The expression is not of a testable type."
                         $$ text "Type:" <+> pp t

-- | Raise an exception.
raise :: REPLException -> REPL a
raise exn = io (X.throwIO exn)


catch :: REPL a -> (REPLException -> REPL a) -> REPL a
catch m k = REPL (\ ref -> unREPL m ref `X.catch` \ e -> unREPL (k e) ref)

rethrowEvalError :: IO a -> IO a
rethrowEvalError m = run `X.catch` rethrow
  where
  run = do
    a <- m
    return $! a

  rethrow :: EvalError -> IO a
  rethrow exn = X.throwIO (EvalError exn)




-- Primitives ------------------------------------------------------------------

io :: IO a -> REPL a
io m = REPL (\ _ -> m)

getRW :: REPL RW
getRW  = REPL readIORef

modifyRW_ :: (RW -> RW) -> REPL ()
modifyRW_ f = REPL (\ ref -> modifyIORef ref f)

-- | Construct the prompt for the current environment.
getPrompt :: REPL String
getPrompt  = mkPrompt `fmap` getRW

-- | Set the name of the currently focused file, edited by @:e@ and loaded via
-- @:r@.
setLoadedMod :: LoadedModule -> REPL ()
setLoadedMod n = do
  modifyRW_ (\ rw -> rw { eLoadedMod = Just n })
  updateREPLTitle

getLoadedMod :: REPL (Maybe LoadedModule)
getLoadedMod  = eLoadedMod `fmap` getRW

setSearchPath :: [FilePath] -> REPL ()
setSearchPath path = do
  me <- getModuleEnv
  setModuleEnv $ me { M.meSearchPath = path }

prependSearchPath :: [FilePath] -> REPL ()
prependSearchPath path = do
  me <- getModuleEnv
  setModuleEnv $ me { M.meSearchPath = path ++ M.meSearchPath me }

shouldContinue :: REPL Bool
shouldContinue  = eContinue `fmap` getRW

stop :: REPL ()
stop  = modifyRW_ (\ rw -> rw { eContinue = False })

unlessBatch :: REPL () -> REPL ()
unlessBatch body = do
  rw <- getRW
  unless (eIsBatch rw) body

-- | Run a computation in batch mode, restoring the previous isBatch
-- flag afterwards
asBatch :: REPL () -> REPL ()
asBatch body = do
  wasBatch <- eIsBatch `fmap` getRW
  modifyRW_ $ (\ rw -> rw { eIsBatch = True })
  body
  modifyRW_ $ (\ rw -> rw { eIsBatch = wasBatch })

disableLet :: REPL ()
disableLet  = modifyRW_ (\ rw -> rw { eLetEnabled = False })

enableLet :: REPL ()
enableLet  = modifyRW_ (\ rw -> rw { eLetEnabled = True })

-- | Are let-bindings enabled in this REPL?
getLetEnabled :: REPL Bool
getLetEnabled = fmap eLetEnabled getRW

-- | Update the title
updateREPLTitle :: REPL ()
updateREPLTitle  = unlessBatch $ do
  rw <- getRW
  eUpdateTitle rw

-- | Set the function that will be called when updating the title
setUpdateREPLTitle :: REPL () -> REPL ()
setUpdateREPLTitle m = modifyRW_ (\rw -> rw { eUpdateTitle = m })

-- | Set the REPL's string-printer
setPutStr :: (String -> IO ()) -> REPL ()
setPutStr fn = modifyRW_ (\rw -> rw { ePutStr = fn })

-- | Get the REPL's string-printer
getPutStr :: REPL (String -> IO ())
getPutStr = fmap ePutStr getRW


-- | Use the configured output action to print a string
rPutStr :: String -> REPL ()
rPutStr str = do
  rw <- getRW
  io $ ePutStr rw str 

-- | Use the configured output action to print a string with a trailing newline
rPutStrLn :: String -> REPL ()
rPutStrLn str = rPutStr $ str ++ "\n"

-- | Use the configured output action to print something using its Show instance
rPrint :: Show a => a -> REPL ()
rPrint x = rPutStrLn (show x)

builtIns :: [(String,(ECon,T.Schema))]
builtIns = map mk [ minBound .. maxBound :: ECon ]
  where mk x = (show (ppPrefix x), (x, typeOf x))

-- | Only meant for use with one of getVars or getTSyns.
keepOne :: String -> [a] -> a
keepOne src as = case as of
  [a] -> a
  _   -> panic ("REPL: " ++ src) ["name clash in interface file"]

getVars :: REPL (Map.Map P.QName M.IfaceDecl)
getVars  = do
  me <- getModuleEnv
  denv <- getDynEnv
  -- the subtle part here is removing the #Uniq prefix from
  -- interactively-bound variables, and also excluding any that are
  -- shadowed and thus can no longer be referenced
  let decls = M.focusedEnv me
      edecls = M.ifDecls (M.deIfaceDecls denv)
      -- is this QName something the user might actually type?
      isShadowed (qn@(P.QName (Just (P.ModName ['#':_])) name), _) =
          case Map.lookup localName neExprs of
            Nothing -> False
            Just uniqueNames -> isNamed uniqueNames
        where localName = P.QName Nothing name
              isNamed us = any (== qn) (map M.qname us)
              neExprs = M.neExprs (M.deNames denv)
      isShadowed _ = False
      unqual ((P.QName _ name), ifds) = (P.QName Nothing name, ifds)
      edecls' = Map.fromList
              . map unqual
              . filter isShadowed
              $ Map.toList edecls
  return (keepOne "getVars" `fmap` (M.ifDecls decls `mappend` edecls'))

getTSyns :: REPL (Map.Map P.QName T.TySyn)
getTSyns  = do
  me <- getModuleEnv
  let decls = M.focusedEnv me
  return (keepOne "getTSyns" `fmap` M.ifTySyns decls)

getNewtypes :: REPL (Map.Map P.QName T.Newtype)
getNewtypes = do
  me <- getModuleEnv
  let decls = M.focusedEnv me
  return (keepOne "getNewtypes" `fmap` M.ifNewtypes decls)

-- | Get visible variable names.
getExprNames :: REPL [String]
getExprNames  = do as <- (map getName . Map.keys) `fmap` getVars
                   return (map fst builtIns ++ as)

-- | Get visible type signature names.
getTypeNames :: REPL [String]
getTypeNames  =
  do tss <- getTSyns
     nts <- getNewtypes
     return $ map getName $ Map.keys tss ++ Map.keys nts

getPropertyNames :: REPL [String]
getPropertyNames =
  do xs <- getVars
     return [ getName x | (x,d) <- Map.toList xs,
                T.PragmaProperty `elem` M.ifDeclPragmas d ]

getName :: P.QName -> String
getName  = show . pp

getModuleEnv :: REPL M.ModuleEnv
getModuleEnv  = eModuleEnv `fmap` getRW

setModuleEnv :: M.ModuleEnv -> REPL ()
setModuleEnv me = modifyRW_ (\rw -> rw { eModuleEnv = me })

getDynEnv :: REPL M.DynamicEnv
getDynEnv  = (M.meDynEnv . eModuleEnv) `fmap` getRW

setDynEnv :: M.DynamicEnv -> REPL ()
setDynEnv denv = do
  me <- getModuleEnv
  setModuleEnv (me { M.meDynEnv = denv })

-- | Given an existing qualified name, prefix it with a
-- relatively-unique string. We make it unique by prefixing with a
-- character @#@ that is not lexically valid in a module name.
uniqify :: P.QName -> REPL P.QName
uniqify (P.QName Nothing name) = do
  i <- eNameSupply `fmap` getRW
  modifyRW_ (\rw -> rw { eNameSupply = i+1 })
  let modname' = P.ModName [ '#' : ("Uniq_" ++ show i) ]
  return (P.QName (Just modname') name)
uniqify qn =
  panic "[REPL] uniqify" ["tried to uniqify a qualified name: " ++ pretty qn]

-- User Environment Interaction ------------------------------------------------

-- | User modifiable environment, for things like numeric base.
type UserEnv = Map.Map String EnvVal

data EnvVal
  = EnvString String
  | EnvProg   String [String]
  | EnvNum    !Int
  | EnvBool   Bool
    deriving (Show)

-- | Generate a UserEnv from a description of the options map.
mkUserEnv :: OptionMap -> UserEnv
mkUserEnv opts = Map.fromList $ do
  opt <- leaves opts
  return (optName opt, optDefault opt)

-- | Set a user option.
setUser :: String -> String -> REPL ()
setUser name val = case lookupTrie name userOptions of

  [opt] -> setUserOpt opt
  []    -> io (putStrLn ("Unknown env value `" ++ name ++ "`"))
  _     -> io (putStrLn ("Ambiguous env value `" ++ name ++ "`"))

  where
  setUserOpt opt = case optDefault opt of
    EnvString _ -> do r <- io (optCheck opt (EnvString val))
                      case r of
                        Just err -> io (putStrLn err)
                        Nothing  -> writeEnv (EnvString val)

    EnvProg _ _ ->
      case splitOptArgs val of
        prog:args -> do r <- io (optCheck opt (EnvProg prog args))
                        case r of
                          Just err -> io (putStrLn err)
                          Nothing  -> writeEnv (EnvProg prog args)
        []        -> io (putStrLn ("Failed to parse command for field, `" ++ name ++ "`"))

    EnvNum _ -> case reads val of
      [(x,_)] -> do r <- io (optCheck opt (EnvNum x))
                    case r of
                      Just err -> io (putStrLn err)
                      Nothing  -> writeEnv (EnvNum x)

      _       -> io (putStrLn ("Failed to parse number for field, `" ++ name ++ "`"))

    EnvBool _
      | any (`isPrefixOf` val) ["enable","on","yes"] ->
        writeEnv (EnvBool True)
      | any (`isPrefixOf` val) ["disable","off","no"] ->
        writeEnv (EnvBool False)
      | otherwise ->
        io (putStrLn ("Failed to parse boolean for field, `" ++ name ++ "`"))
    where

    writeEnv ev =
      do optEff opt ev
         modifyRW_ (\rw -> rw { eUserEnv = Map.insert name ev (eUserEnv rw) })

splitOptArgs :: String -> [String]
splitOptArgs  = unfoldr (parse "")
  where

  parse acc (c:cs) | isQuote c       = quoted (c:acc) cs
                   | not (isSpace c) = parse (c:acc) cs
                   | otherwise       = result acc cs
  parse acc []                       = result acc []

  quoted acc (c:cs) | isQuote c      = parse  (c:acc) cs
                    | otherwise      = quoted (c:acc) cs
  quoted acc []                      = result acc []

  result []  [] = Nothing
  result []  cs = parse [] (dropWhile isSpace cs)
  result acc cs = Just (reverse acc, dropWhile isSpace cs)

  isQuote :: Char -> Bool
  isQuote c = c `elem` ("'\"" :: String)


-- | Get a user option, using Maybe for failure.
tryGetUser :: String -> REPL (Maybe EnvVal)
tryGetUser name = do
  rw <- getRW
  return (Map.lookup name (eUserEnv rw))

-- | Get a user option, when it's known to exist.  Fail with panic when it
-- doesn't.
getUser :: String -> REPL EnvVal
getUser name = do
  mb <- tryGetUser name
  case mb of
    Just ev -> return ev
    Nothing -> panic "[REPL] getUser" ["option `" ++ name ++ "` does not exist"]

-- Environment Options ---------------------------------------------------------

type OptionMap = Trie OptionDescr

mkOptionMap :: [OptionDescr] -> OptionMap
mkOptionMap  = foldl insert emptyTrie
  where
  insert m d = insertTrie (optName d) d m

data OptionDescr = OptionDescr
  { optName    :: String
  , optDefault :: EnvVal
  , optCheck   :: EnvVal -> IO (Maybe String)
  , optHelp    :: String
  , optEff     :: EnvVal -> REPL ()
  }

simpleOpt :: String -> EnvVal -> (EnvVal -> IO (Maybe String)) -> String
          -> OptionDescr
simpleOpt optName optDefault optCheck optHelp =
  OptionDescr { optEff = \ _ -> return (), .. }

userOptions :: OptionMap
userOptions  = mkOptionMap
  [ simpleOpt "base" (EnvNum 16) checkBase
    "the base to display words at"
  , simpleOpt "debug" (EnvBool False) (const $ return Nothing)
    "enable debugging output"
  , simpleOpt "ascii" (EnvBool False) (const $ return Nothing)
    "display 7- or 8-bit words using ASCII notation."
  , simpleOpt "infLength" (EnvNum 5) checkInfLength
    "The number of elements to display for infinite sequences."
  , simpleOpt "tests" (EnvNum 100) (const $ return Nothing)
    "The number of random tests to try."
  , simpleOpt "satNum" (EnvString "1") checkSatNum
    "The maximum number of :sat solutions to display (\"all\" for no limit)."
  , simpleOpt "prover" (EnvString "cvc4") checkProver $
    "The external SMT solver for :prove and :sat (" ++ proverListString ++ ")."
  , simpleOpt "iteSolver" (EnvBool False) (const $ return Nothing)
    "Use smt solver to filter conditional branches in proofs."
  , simpleOpt "warnDefaulting" (EnvBool True) (const $ return Nothing)
    "Choose if we should display warnings when defaulting."
  , simpleOpt "warnShadowing" (EnvBool True) (const $ return Nothing)
    "Choose if we should display warnings when shadowing symbols."
  , simpleOpt "smtfile" (EnvString "-") (const $ return Nothing)
    "The file to use for SMT-Lib scripts (for debugging or offline proving)"
  , OptionDescr "mono-binds" (EnvBool True) (const $ return Nothing)
    "Whether or not to generalize bindings in a where-clause" $
    \case EnvBool b -> do me <- getModuleEnv
                          setModuleEnv me { M.meMonoBinds = b }
          _         -> return ()

  , OptionDescr "tc-solver" (EnvProg "cvc4" [ "--lang=smt2"
                                            , "--incremental"
                                            , "--rewrite-divk" ])
    (const (return Nothing)) -- TODO: check for the program in the path
    "The solver that will be used by the type checker" $
    \case EnvProg prog args -> do me <- getModuleEnv
                                  let cfg = M.meSolverConfig me
                                  setModuleEnv me { M.meSolverConfig =
                                                      cfg { T.solverPath = prog
                                                          , T.solverArgs = args } }
          _                 -> return ()

  , OptionDescr "tc-debug" (EnvNum 0)
    (const (return Nothing))
    "Enable type-checker debugging output" $
    \case EnvNum n -> do me <- getModuleEnv
                         let cfg = M.meSolverConfig me
                         setModuleEnv me { M.meSolverConfig = cfg{ T.solverVerbose = fromIntegral n } }
          _        -> return ()
  ]

-- | Check the value to the `base` option.
checkBase :: EnvVal -> IO (Maybe String)
checkBase val = case val of
  EnvNum n
    | n >= 2 && n <= 36 -> return Nothing
    | otherwise         -> return $ Just "base must fall between 2 and 36"
  _                     -> return $ Just "unable to parse a value for base"

checkInfLength :: EnvVal -> IO (Maybe String)
checkInfLength val = case val of
  EnvNum n
    | n >= 0    -> return Nothing
    | otherwise -> return $ Just "the number of elements should be positive"
  _ -> return $ Just "unable to parse a value for infLength"

checkProver :: EnvVal -> IO (Maybe String)
checkProver val = case val of
  EnvString s
    | s `notElem` proverNames     -> return $ Just $ "Prover must be " ++ proverListString
    | s `elem` ["offline", "any"] -> return Nothing
    | otherwise                   -> do let prover = lookupProver s
                                        available <- sbvCheckSolverInstallation prover
                                        unless available $
                                          putStrLn $ "Warning: " ++ s ++ " installation not found"
                                        return Nothing

  _ -> return $ Just "unable to parse a value for prover"

proverListString :: String
proverListString = concatMap (++ ", ") (init proverNames) ++ "or " ++ last proverNames

checkSatNum :: EnvVal -> IO (Maybe String)
checkSatNum val = case val of
  EnvString "all" -> return Nothing
  EnvString s ->
    case readMaybe s :: Maybe Int of
      Just n | n >= 1 -> return Nothing
      _               -> return $ Just "must be an integer > 0 or \"all\""
  _ -> return $ Just "unable to parse a value for satNum"

getUserSatNum :: REPL (Maybe Int)
getUserSatNum = do
  EnvString s <- getUser "satNum"
  case s of
    "all"                     -> return Nothing
    _ | Just n <- readMaybe s -> return (Just n)
    _                         -> panic "REPL.Monad.getUserSatNum"
                                   [ "invalid satNum option" ]

-- Environment Utilities -------------------------------------------------------

whenDebug :: REPL () -> REPL ()
whenDebug m = do
  EnvBool b <- getUser "debug"
  when b m

-- Smoke Testing ---------------------------------------------------------------

smokeTest :: REPL [Smoke]
smokeTest = catMaybes <$> sequence tests
  where
    tests = [ cvc4exists ]

type SmokeTest = REPL (Maybe Smoke)

data Smoke
  = CVC4NotFound
  deriving (Show, Eq)

instance PP Smoke where
  ppPrec _ smoke =
    case smoke of
      CVC4NotFound -> text . intercalate " " $ [
          "[error] cvc4 is required to run Cryptol, but was not found in the"
        , "system path. See the Cryptol README for more on how to install cvc4."
        ]

cvc4exists :: SmokeTest
cvc4exists = do
  mPath <- io $ findExecutable "cvc4"
  case mPath of
    Nothing -> return (Just CVC4NotFound)
    Just _  -> return Nothing



