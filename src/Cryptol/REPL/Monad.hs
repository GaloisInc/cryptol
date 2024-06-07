-- |
-- Module      :  Cryptol.REPL.Monad
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Cryptol.REPL.Monad (
    -- * REPL Monad
    REPL(..), runREPL
  , io
  , raise
  , stop
  , catch
  , finally
  , rPutStrLn
  , rPutStr
  , rPrint

    -- ** Errors
  , REPLException(..)
  , rethrowEvalError

    -- ** Environment
  , getFocusedEnv
  , getModuleEnv, setModuleEnv
  , getDynEnv, setDynEnv
  , getCallStacks
  , getTCSolver
  , resetTCSolver
  , uniqify, freshName
  , whenDebug
  , getEvalOptsAction
  , getPPValOpts
  , getExprNames
  , getTypeNames
  , getPropertyNames
  , getModNames
  , LoadedModule(..), getLoadedMod, setLoadedMod, clearLoadedMod
  , setEditPath, getEditPath, clearEditPath
  , setSearchPath, prependSearchPath
  , getPrompt
  , shouldContinue
  , unlessBatch
  , asBatch
  , validEvalContext
  , updateREPLTitle
  , isolated
  , setUpdateREPLTitle
  , withRandomGen
  , setRandomGen
  , getRandomGen

    -- ** Config Options
  , EnvVal(..)
  , OptionDescr(..)
  , setUser, getUser, getKnownUser, tryGetUser
  , userOptions
  , userOptionsWithAliases
  , getUserSatNum
  , getUserShowProverStats
  , getUserProverValidate
  , parsePPFloatFormat
  , parseFieldOrder
  , getProverConfig
  , parseSearchPath

    -- ** Configurable Output
  , getPutStr
  , getLogger
  , setLogger
  , setPutStr

    -- ** Smoke Test
  , smokeTest
  , Smoke(..)

  ) where

import Cryptol.REPL.Trie

import Cryptol.Eval (EvalErrorEx, Unsupported, WordTooWide,EvalOpts(..))
import qualified Cryptol.ModuleSystem as M
import qualified Cryptol.ModuleSystem.Env as M
import qualified Cryptol.ModuleSystem.Name as M
import qualified Cryptol.ModuleSystem.NamingEnv as M
import Cryptol.Parser (ParseError,ppError)
import Cryptol.Parser.NoInclude (IncludeError,ppIncludeError)
import Cryptol.Parser.NoPat (Error)
import Cryptol.Parser.Position (emptyRange, Range(from))
import qualified Cryptol.TypeCheck.AST as T
import qualified Cryptol.TypeCheck as T
import qualified Cryptol.TypeCheck.Solver.SMT as SMT
import qualified Cryptol.IR.FreeVars as T
import qualified Cryptol.Utils.Ident as I
import Cryptol.Utils.PP
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.Logger(Logger, logPutStr, funLogger)
import qualified Cryptol.Parser.AST as P
import Cryptol.Symbolic (SatNum(..))
import Cryptol.Symbolic.SBV (SBVPortfolioException)
import Cryptol.Symbolic.What4 (W4Exception)
import qualified Cryptol.Symbolic.SBV as SBV (proverNames, setupProver, defaultProver, SBVProverConfig)
import qualified Cryptol.Symbolic.What4 as W4 (proverNames, setupProver, W4ProverConfig)



import Control.Monad (ap,unless,when)
import Control.Monad.Base
import qualified Control.Monad.Catch as Ex
import Control.Monad.IO.Class
import Control.Monad.Trans.Control
import Data.Char (isSpace, toLower)
import Data.IORef
    (IORef,newIORef,readIORef,atomicModifyIORef)
import Data.List (intercalate, isPrefixOf, unfoldr, sortBy)
import Data.Maybe (catMaybes)
import Data.Ord (comparing)
import Data.Tuple (swap)
import Data.Typeable (Typeable)
import System.Directory (findExecutable)
import System.FilePath (splitSearchPath, searchPathSeparator)
import qualified Control.Exception as X
import qualified Data.Map as Map
import qualified Data.Set as Set
import Text.Read (readMaybe)

import Data.SBV (SBVException)
import qualified System.Random.TF as TF

import Prelude ()
import Prelude.Compat

-- REPL Environment ------------------------------------------------------------

-- | This indicates what the user would like to work on.
data LoadedModule = LoadedModule
  { lName :: Maybe P.ModName  -- ^ Working on this module.
  , lPath :: M.ModulePath     -- ^ Working on this file.
  }

-- | REPL RW Environment.
data RW = RW
  { eLoadedMod   :: Maybe LoadedModule
    -- ^ This is the name of the currently "focused" module.
    -- This is what we reload (:r)

  , eEditFile :: Maybe FilePath
    -- ^ This is what we edit (:e)

  , eContinue    :: Bool
    -- ^ Should we keep going when we encounter an error, or give up.

  , eIsBatch     :: Bool
    -- ^ Are we in batch mode.

  , eModuleEnv   :: M.ModuleEnv
    -- ^ The current environment of all things loaded.

  , eUserEnv     :: UserEnv
    -- ^ User settings

  , eLogger      :: Logger
    -- ^ Use this to send messages to the user

  , eCallStacks :: Bool

  , eUpdateTitle :: REPL ()
    -- ^ Execute this every time we load a module.
    -- This is used to change the title of terminal when loading a module.

  , eProverConfig :: Either SBV.SBVProverConfig W4.W4ProverConfig

  , eTCConfig :: T.SolverConfig
    -- ^ Solver configuration to be used for typechecking

  , eTCSolver :: Maybe SMT.Solver
    -- ^ Solver instance to be used for typechecking

  , eTCSolverRestarts :: !Int
    -- ^ Counts how many times we've restarted the solver.
    -- Used as a kind of id for the current solver, which helps avoid
    -- a race condition where the callback of a dead solver runs after
    -- a new one has been started.

  , eRandomGen :: TF.TFGen
    -- ^ Random number generator for things like QC and dumpTests
  }


-- | Initial, empty environment.
defaultRW :: Bool -> Bool -> Logger -> IO RW
defaultRW isBatch callStacks l = do
  env <- M.initialModuleEnv
  rng <- TF.newTFGen
  let searchPath = M.meSearchPath env
  let solverConfig = T.defaultSolverConfig searchPath
  return RW
    { eLoadedMod   = Nothing
    , eEditFile    = Nothing
    , eContinue    = True
    , eIsBatch     = isBatch
    , eModuleEnv   = env
    , eUserEnv     = mkUserEnv userOptions
    , eLogger      = l
    , eCallStacks  = callStacks
    , eUpdateTitle = return ()
    , eProverConfig = Left SBV.defaultProver
    , eTCConfig    = solverConfig
    , eTCSolver    = Nothing
    , eTCSolverRestarts = 0
    , eRandomGen = rng
    }

-- | Build up the prompt for the REPL.
mkPrompt :: RW -> String
mkPrompt rw
  | eIsBatch rw = ""
  | detailedPrompt = withEdit ++ "> "
  | otherwise      = modLn ++ "> "
  where
  detailedPrompt = id False

  modLn   =
    case lName =<< eLoadedMod rw of
      Nothing -> show (pp I.preludeName)
      Just m
        | M.isLoadedParamMod m loaded -> modName ++ "(parameterized)"
        | M.isLoadedInterface m loaded -> modName ++ "(interface)"
        | otherwise -> modName
        where modName = pretty m
              loaded = M.meLoadedModules (eModuleEnv rw)

  withFocus =
    case eLoadedMod rw of
      Nothing -> modLn
      Just m ->
        case (lName m, lPath m) of
          (Nothing, M.InFile f) -> ":r to reload " ++ show f ++ "\n" ++ modLn
          _ -> modLn

  withEdit =
    case eEditFile rw of
      Nothing -> withFocus
      Just e
        | Just (M.InFile f) <- lPath <$> eLoadedMod rw
        , f == e -> withFocus
        | otherwise -> ":e to edit " ++ e ++ "\n" ++ withFocus



-- REPL Monad ------------------------------------------------------------------

-- | REPL_ context with InputT handling.
newtype REPL a = REPL { unREPL :: IORef RW -> IO a }

-- | Run a REPL action with a fresh environment.
runREPL :: Bool -> Bool -> Logger -> REPL a -> IO a
runREPL isBatch callStacks l m = do
  Ex.bracket
    (newIORef =<< defaultRW isBatch callStacks l)
    (unREPL resetTCSolver)
    (unREPL m)

instance Functor REPL where
  {-# INLINE fmap #-}
  fmap f m = REPL (\ ref -> fmap f (unREPL m ref))

instance Applicative REPL where
  {-# INLINE pure #-}
  pure x = REPL (\_ -> pure x)
  {-# INLINE (<*>) #-}
  (<*>) = ap

instance Monad REPL where
  {-# INLINE return #-}
  return = pure

  {-# INLINE (>>=) #-}
  m >>= f = REPL $ \ref -> do
    x <- unREPL m ref
    unREPL (f x) ref

instance MonadIO REPL where
  liftIO = io

instance MonadBase IO REPL where
  liftBase = liftIO

instance MonadBaseControl IO REPL where
  type StM REPL a = a
  liftBaseWith f = REPL $ \ref ->
    f $ \m -> unREPL m ref
  restoreM x = return x

instance M.FreshM REPL where
  liftSupply f = modifyRW $ \ RW { .. } ->
    let (a,s') = f (M.meSupply eModuleEnv)
     in (RW { eModuleEnv = eModuleEnv { M.meSupply = s' }, .. },a)

instance Ex.MonadThrow REPL where
  throwM e = liftIO $ X.throwIO e

instance Ex.MonadCatch REPL where
  catch op handler = control $ \runInBase -> Ex.catch (runInBase op) (runInBase . handler)

instance Ex.MonadMask REPL where
  mask op = REPL $ \ref -> Ex.mask $ \u -> unREPL (op (q u)) ref
    where q u (REPL b) = REPL (\ref -> u (b ref))

  uninterruptibleMask op = REPL $ \ref ->
    Ex.uninterruptibleMask $ \u -> unREPL (op (q u)) ref
    where q u (REPL b) = REPL (\ref -> u (b ref))

  generalBracket acq rls op = control $ \runInBase ->
    Ex.generalBracket (runInBase acq)
    (\saved -> \e -> runInBase (restoreM saved >>= \a -> rls a e))
    (\saved -> runInBase (restoreM saved >>= op))

-- Exceptions ------------------------------------------------------------------

-- | REPL exceptions.
data REPLException
  = ParseError ParseError
  | FileNotFound FilePath
  | DirectoryNotFound FilePath
  | NoPatError [Error]
  | NoIncludeError [IncludeError]
  | EvalError EvalErrorEx
  | TooWide WordTooWide
  | Unsupported Unsupported
  | ModuleSystemError NameDisp M.ModuleError
  | EvalPolyError T.Schema
  | InstantiationsNotFound T.Schema
  | TypeNotTestable T.Type
  | EvalInParamModule [T.TParam] [M.Name]
  | SBVError String
  | SBVException SBVException
  | SBVPortfolioException SBVPortfolioException
  | W4Exception W4Exception
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
    ModuleSystemError ns me -> fixNameDisp ns (pp me)
    EvalError e          -> pp e
    Unsupported e        -> pp e
    TooWide e            -> pp e
    EvalPolyError s      -> text "Cannot evaluate polymorphic value."
                         $$ text "Type:" <+> pp s
    InstantiationsNotFound s -> text "Cannot find instantiations for some type variables."
                             $$ text "Type:" <+> pp s
    TypeNotTestable t    -> text "The expression is not of a testable type."
                         $$ text "Type:" <+> pp t
    EvalInParamModule as xs -> nest 2 $ vsep $
      [ text "Expression depends on definitions from a parameterized module:" ]
      ++ map pp as
      ++ map pp xs
    SBVError s           -> text "SBV error:" $$ text s
    SBVException e       -> text "SBV exception:" $$ text (show e)
    SBVPortfolioException e -> text "SBV exception:" $$ text (show e)
    W4Exception e        -> text "What4 exception:" $$ text (show e)

-- | Raise an exception.
raise :: REPLException -> REPL a
raise exn = io (X.throwIO exn)


catch :: REPL a -> (REPLException -> REPL a) -> REPL a
catch m k = REPL (\ ref -> rethrowEvalError (unREPL m ref) `X.catch` \ e -> unREPL (k e) ref)

finally :: REPL a -> REPL b -> REPL a
finally m1 m2 = REPL (\ref -> unREPL m1 ref `X.finally` unREPL m2 ref)


rethrowEvalError :: IO a -> IO a
rethrowEvalError m =
    run `X.catch` rethrow
        `X.catch` rethrowTooWide
        `X.catch` rethrowUnsupported
  where
  run = do
    a <- m
    return $! a

  rethrow :: EvalErrorEx -> IO a
  rethrow exn = X.throwIO (EvalError exn)

  rethrowTooWide :: WordTooWide -> IO a
  rethrowTooWide exn = X.throwIO (TooWide exn)

  rethrowUnsupported :: Unsupported -> IO a
  rethrowUnsupported exn = X.throwIO (Unsupported exn)


-- Primitives ------------------------------------------------------------------


io :: IO a -> REPL a
io m = REPL (\ _ -> m)

getRW :: REPL RW
getRW  = REPL readIORef

modifyRW :: (RW -> (RW,a)) -> REPL a
modifyRW f = REPL (\ ref -> atomicModifyIORef ref f)

modifyRW_ :: (RW -> RW) -> REPL ()
modifyRW_ f = REPL (\ ref -> atomicModifyIORef ref (\x -> (f x, ())))

-- | Construct the prompt for the current environment.
getPrompt :: REPL String
getPrompt  = mkPrompt `fmap` getRW

getCallStacks :: REPL Bool
getCallStacks = eCallStacks <$> getRW

-- This assumes that we are not starting solvers in parallel, otherwise
-- there are a bunch of race conditions here.
getTCSolver :: REPL SMT.Solver
getTCSolver =
  do rw <- getRW
     case eTCSolver rw of
       Just s -> return s
       Nothing ->
         do ref <- REPL (\ref -> pure ref)
            let now = eTCSolverRestarts rw + 1
                upd new = if eTCSolverRestarts new == now
                             then new { eTCSolver = Nothing }
                             else new
                onExit = atomicModifyIORef ref (\s -> (upd s, ()))
            s <- io (SMT.startSolver onExit (eTCConfig rw))
            modifyRW_ (\rw' -> rw'{ eTCSolver = Just s
                                  , eTCSolverRestarts = now })
            return s


resetTCSolver :: REPL ()
resetTCSolver =
  do mtc <- eTCSolver <$> getRW
     case mtc of
       Nothing -> return ()
       Just s  ->
         do io (SMT.stopSolver s)
            modifyRW_ (\rw -> rw{ eTCSolver = Nothing })

-- Get the setting we should use for displaying values.
getPPValOpts :: REPL PPOpts
getPPValOpts =
  do base       <- getKnownUser "base"
     ascii      <- getKnownUser "ascii"
     infLength  <- getKnownUser "infLength"

     fpBase     <- getKnownUser "fpBase"
     fpFmtTxt   <- getKnownUser "fpFormat"
     fieldOrder <- getKnownUser "fieldOrder"
     let fpFmt = case parsePPFloatFormat fpFmtTxt of
                   Just f  -> f
                   Nothing -> panic "getPPOpts"
                                      [ "Failed to parse fp-format" ]

     return PPOpts { useBase       = base
                   , useAscii      = ascii
                   , useInfLength  = infLength
                   , useFPBase     = fpBase
                   , useFPFormat   = fpFmt
                   , useFieldOrder = fieldOrder
                   }

getEvalOptsAction :: REPL (IO EvalOpts)
getEvalOptsAction = REPL $ \rwRef -> pure $
  do ppOpts <- unREPL getPPValOpts rwRef
     l      <- unREPL getLogger rwRef
     return EvalOpts { evalPPOpts = ppOpts, evalLogger = l }

clearLoadedMod :: REPL ()
clearLoadedMod = do modifyRW_ (\rw -> rw { eLoadedMod = upd <$> eLoadedMod rw })
                    updateREPLTitle
  where upd x = x { lName = Nothing }

-- | Set the name of the currently focused file, loaded via @:r@.
setLoadedMod :: LoadedModule -> REPL ()
setLoadedMod n = do
  modifyRW_ (\ rw -> rw { eLoadedMod = Just n })
  updateREPLTitle

getLoadedMod :: REPL (Maybe LoadedModule)
getLoadedMod  = eLoadedMod `fmap` getRW



-- | Set the path for the ':e' command.
-- Note that this does not change the focused module (i.e., what ":r" reloads)
setEditPath :: FilePath -> REPL ()
setEditPath p = modifyRW_ $ \rw -> rw { eEditFile = Just p }

getEditPath :: REPL (Maybe FilePath)
getEditPath = eEditFile <$> getRW

clearEditPath :: REPL ()
clearEditPath = modifyRW_ $ \rw -> rw { eEditFile = Nothing }

setSearchPath :: [FilePath] -> REPL ()
setSearchPath path = do
  me <- getModuleEnv
  setModuleEnv $ me { M.meSearchPath = path }
  setUserDirect "path" (EnvString (renderSearchPath path))

prependSearchPath :: [FilePath] -> REPL ()
prependSearchPath path = do
  me <- getModuleEnv
  let path' = path ++ M.meSearchPath me
  setModuleEnv $ me { M.meSearchPath = path' }
  setUserDirect "path" (EnvString (renderSearchPath path'))

getProverConfig :: REPL (Either SBV.SBVProverConfig W4.W4ProverConfig)
getProverConfig = eProverConfig <$> getRW

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
asBatch :: REPL a -> REPL a
asBatch body = do
  wasBatch <- eIsBatch `fmap` getRW
  modifyRW_ $ (\ rw -> rw { eIsBatch = True })
  a <- body
  modifyRW_ $ (\ rw -> rw { eIsBatch = wasBatch })
  return a

isolated :: REPL a -> REPL a
isolated body = do
  rw <- getRW
  body `finally` modifyRW_ (const rw)

-- | Is evaluation enabled? If the currently focused module is parameterized,
-- then we cannot evaluate.
validEvalContext :: T.FreeVars a => a -> REPL ()
validEvalContext a =
  do me <- eModuleEnv <$> getRW
     let (badTs, bad) = M.loadedParamModDeps (M.meLoadedModules me) a
     unless (Set.null bad && Set.null badTs) $
       raise (EvalInParamModule (Set.toList badTs) (Set.toList bad))

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
setPutStr fn = modifyRW_ $ \rw -> rw { eLogger = funLogger fn }

-- | Get the REPL's string-printer
getPutStr :: REPL (String -> IO ())
getPutStr =
  do rw <- getRW
     return (logPutStr (eLogger rw))

getLogger :: REPL Logger
getLogger = eLogger <$> getRW

setLogger :: Logger -> REPL ()
setLogger logger = modifyRW_ $ \rw -> rw { eLogger = logger }

-- | Use the configured output action to print a string
rPutStr :: String -> REPL ()
rPutStr str = do
  f <- getPutStr
  io (f str)

-- | Use the configured output action to print a string with a trailing newline
rPutStrLn :: String -> REPL ()
rPutStrLn str = rPutStr $ str ++ "\n"

-- | Use the configured output action to print something using its Show instance
rPrint :: Show a => a -> REPL ()
rPrint x = rPutStrLn (show x)

getFocusedEnv :: REPL M.ModContext
getFocusedEnv  = M.focusedEnv <$> getModuleEnv

-- | Get visible variable names.
-- This is used for command line completition.
getExprNames :: REPL [String]
getExprNames =
  do fNames <- M.mctxNames <$> getFocusedEnv
     return (map (show . pp) (Map.keys (M.namespaceMap M.NSValue fNames)))

-- | Get visible type signature names.
-- This is used for command line completition.
getTypeNames :: REPL [String]
getTypeNames  =
  do fNames <- M.mctxNames <$> getFocusedEnv
     return (map (show . pp) (Map.keys (M.namespaceMap M.NSType fNames)))

-- | Return a list of property names, sorted by position in the file.
getPropertyNames :: REPL ([(M.Name,M.IfaceDecl)],NameDisp)
getPropertyNames =
  do fe <- getFocusedEnv
     let xs = M.ifDecls (M.mctxDecls fe)
         ps = sortBy (comparing (from . M.nameLoc . fst))
              [ (x,d) | (x,d) <- Map.toList xs,
                    T.PragmaProperty `elem` M.ifDeclPragmas d ]

     return (ps, M.mctxNameDisp fe)

getModNames :: REPL [I.ModName]
getModNames =
  do me <- getModuleEnv
     return (map T.mName (M.loadedModules me))

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

getRandomGen :: REPL TF.TFGen
getRandomGen = eRandomGen <$> getRW

setRandomGen :: TF.TFGen -> REPL ()
setRandomGen rng = modifyRW_ (\s -> s { eRandomGen = rng })

withRandomGen :: (TF.TFGen -> REPL (a, TF.TFGen)) -> REPL a
withRandomGen repl =
  do  g <- getRandomGen
      (result, g') <- repl g
      setRandomGen g'
      pure result

-- | Given an existing qualified name, prefix it with a
-- relatively-unique string. We make it unique by prefixing with a
-- character @#@ that is not lexically valid in a module name.
uniqify :: M.Name -> REPL M.Name

uniqify name =
  case M.nameInfo name of
    M.GlobalName s og ->
      M.liftSupply (M.mkDeclared (M.nameNamespace name)
                  (I.ogModule og) s
                  (M.nameIdent name) (M.nameFixity name) (M.nameLoc name))

    M.LocalName {} ->
      panic "[REPL] uniqify" ["tried to uniqify a parameter: " ++ pretty name]


-- uniqify (P.QName Nothing name) = do
--   i <- eNameSupply `fmap` getRW
--   modifyRW_ (\rw -> rw { eNameSupply = i+1 })
--   let modname' = P.mkModName [ '#' : ("Uniq_" ++ show i) ]
--   return (P.QName (Just modname') name)

-- uniqify qn =
--   panic "[REPL] uniqify" ["tried to uniqify a qualified name: " ++ pretty qn]


-- | Generate a fresh name using the given index. The name will reside within
-- the "<interactive>" namespace.
freshName :: I.Ident -> M.NameSource -> REPL M.Name
freshName i sys =
  M.liftSupply (M.mkDeclared I.NSValue mpath sys i Nothing emptyRange)
  where mpath = M.TopModule I.interactiveName


parseSearchPath :: String -> [String]
parseSearchPath path = path'
#if defined(mingw32_HOST_OS) || defined(__MINGW32__)
      -- Windows paths search from end to beginning
      where path' = reverse (splitSearchPath path)
#else
      where path' = splitSearchPath path
#endif

renderSearchPath :: [String] -> String
renderSearchPath pathSegs = path
#if defined(mingw32_HOST_OS) || defined(__MINGW32__)
      -- Windows paths search from end to beginning
      where path = intercalate [searchPathSeparator] (reverse pathSegs)
#else
      where path = intercalate [searchPathSeparator] pathSegs
#endif

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
-- Returns 'True' on success
setUser :: String -> String -> REPL Bool
setUser name val = case lookupTrieExact name userOptionsWithAliases of

  [opt] -> setUserOpt opt
  []    -> False <$ rPutStrLn ("Unknown env value `" ++ name ++ "`")
  _     -> False <$ rPutStrLn ("Ambiguous env value `" ++ name ++ "`")

  where
  setUserOpt opt = case optDefault opt of
    EnvString _ -> doCheck (EnvString val)

    EnvProg _ _ ->
      case splitOptArgs val of
        prog:args -> doCheck (EnvProg prog args)
        [] -> False <$ rPutStrLn ("Failed to parse command for field, `" ++ name ++ "`")

    EnvNum _ -> case reads val of
      [(x,_)] -> doCheck (EnvNum x)
      _ -> False <$ rPutStrLn ("Failed to parse number for field, `" ++ name ++ "`")

    EnvBool _
      | any (`isPrefixOf` val) ["enable", "on", "yes", "true"] ->
        True <$ writeEnv (EnvBool True)
      | any (`isPrefixOf` val) ["disable", "off", "no", "false"] ->
        True <$ writeEnv (EnvBool False)
      | otherwise ->
        False <$ rPutStrLn ("Failed to parse boolean for field, `" ++ name ++ "`")
    where
    doCheck v = do (r,ws) <- optCheck opt v
                   case r of
                     Just err -> False <$ rPutStrLn err
                     Nothing  -> do mapM_ rPutStrLn ws
                                    writeEnv v
                                    pure True
    writeEnv ev =
      do optEff opt ev
         modifyRW_ (\rw -> rw { eUserEnv = Map.insert (optName opt) ev (eUserEnv rw) })

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

setUserDirect :: String -> EnvVal -> REPL ()
setUserDirect optName val = do
  modifyRW_ (\rw -> rw { eUserEnv = Map.insert optName val (eUserEnv rw) })

getKnownUser :: IsEnvVal a => String -> REPL a
getKnownUser x = fromEnvVal <$> getUser x

class IsEnvVal a where
  fromEnvVal :: EnvVal -> a

instance IsEnvVal Bool where
  fromEnvVal x = case x of
                   EnvBool b -> b
                   _         -> badIsEnv "Bool"

instance IsEnvVal Int where
  fromEnvVal x = case x of
                   EnvNum b -> b
                   _         -> badIsEnv "Num"

instance IsEnvVal (String,[String]) where
  fromEnvVal x = case x of
                   EnvProg b bs -> (b,bs)
                   _            -> badIsEnv "Prog"

instance IsEnvVal String where
  fromEnvVal x = case x of
                   EnvString b -> b
                   _           -> badIsEnv "String"

instance IsEnvVal FieldOrder where
  fromEnvVal x = case x of
                   EnvString s | Just o <- parseFieldOrder s
                     -> o
                   _ -> badIsEnv "display` or `canonical"

badIsEnv :: String -> a
badIsEnv x = panic "fromEnvVal" [ "[REPL] Expected a `" ++ x ++ "` value." ]


getUserShowProverStats :: REPL Bool
getUserShowProverStats = getKnownUser "proverStats"

getUserProverValidate :: REPL Bool
getUserProverValidate = getKnownUser "proverValidate"

-- Environment Options ---------------------------------------------------------

type OptionMap = Trie OptionDescr

mkOptionMap :: [OptionDescr] -> OptionMap
mkOptionMap  = foldl insert emptyTrie
  where
  insert m d = insertTrie (optName d) d m

-- | Returns maybe an error, and some warnings
type Checker = EnvVal -> REPL (Maybe String, [String])

noCheck :: Checker
noCheck _ = return (Nothing, [])

noWarns :: Maybe String -> REPL (Maybe String, [String])
noWarns mb = return (mb, [])

data OptionDescr = OptionDescr
  { optName    :: String
  , optAliases :: [String]
  , optDefault :: EnvVal
  , optCheck   :: Checker
  , optHelp    :: String
  , optEff     :: EnvVal -> REPL ()
  }

simpleOpt :: String -> [String] -> EnvVal -> Checker -> String -> OptionDescr
simpleOpt optName optAliases optDefault optCheck optHelp =
  OptionDescr { optEff = \ _ -> return (), .. }

userOptionsWithAliases :: OptionMap
userOptionsWithAliases = foldl insert userOptions (leaves userOptions)
  where
  insert m d = foldl (\m' n -> insertTrie n d m') m (optAliases d)

userOptions :: OptionMap
userOptions  = mkOptionMap
  [ simpleOpt "base" [] (EnvNum 16) checkBase
    "The base to display words at (2, 8, 10, or 16)."
  , simpleOpt "debug" [] (EnvBool False) noCheck
    "Enable debugging output."
  , simpleOpt "ascii" [] (EnvBool False) noCheck
    "Whether to display 7- or 8-bit words using ASCII notation."
  , simpleOpt "infLength" ["inf-length"] (EnvNum 5) checkInfLength
    "The number of elements to display for infinite sequences."
  , simpleOpt "tests" [] (EnvNum 100) noCheck
    "The number of random tests to try with ':check'."
  , simpleOpt "satNum" ["sat-num"] (EnvString "1") checkSatNum
    "The maximum number of :sat solutions to display (\"all\" for no limit)."
  , simpleOpt "prover" [] (EnvString "z3") checkProver $
    "The external SMT solver for ':prove' and ':sat'\n(" ++ proverListString ++ ")."
  , simpleOpt "warnDefaulting" ["warn-defaulting"] (EnvBool False) noCheck
    "Choose whether to display warnings when defaulting."
  , simpleOpt "warnShadowing" ["warn-shadowing"] (EnvBool True) noCheck
    "Choose whether to display warnings when shadowing symbols."
  , simpleOpt "warnPrefixAssoc" ["warn-prefix-assoc"] (EnvBool True) noCheck
    "Choose whether to display warnings when expression association has changed due to new prefix operator fixities."
  , simpleOpt "warnUninterp" ["warn-uninterp"] (EnvBool True) noCheck
    "Choose whether to issue a warning when uninterpreted functions are used to implement primitives in the symbolic simulator."
  , simpleOpt "warnNonExhaustiveConstraintGuards" ["warn-nonexhaustive-constraintguards"] (EnvBool True) noCheck
    "Choose whether to issue a warning when a use of constraint guards is not determined to be exhaustive."
  , simpleOpt "smtFile" ["smt-file"] (EnvString "-") noCheck
    "The file to use for SMT-Lib scripts (for debugging or offline proving).\nUse \"-\" for stdout."
  , OptionDescr "path" [] (EnvString "") noCheck
    "The search path for finding named Cryptol modules." $
    \case EnvString path ->
            do let segs = parseSearchPath path
               me <- getModuleEnv
               setModuleEnv me { M.meSearchPath = segs }
          _ -> return ()

  , OptionDescr "monoBinds" ["mono-binds"] (EnvBool True) noCheck
    "Whether or not to generalize bindings in a 'where' clause." $
    \case EnvBool b -> do me <- getModuleEnv
                          setModuleEnv me { M.meMonoBinds = b }
          _         -> return ()

  , OptionDescr "tcSolver" ["tc-solver"] (EnvProg "z3" [ "-smt2", "-in" ])
    noCheck  -- TODO: check for the program in the path
    "The solver that will be used by the type checker." $
    \case EnvProg prog args -> do modifyRW_ (\rw -> rw { eTCConfig = (eTCConfig rw)
                                                                      { T.solverPath = prog
                                                                      , T.solverArgs = args
                                                                      }})
                                  resetTCSolver
          _                 -> return ()

  , OptionDescr "tcDebug" ["tc-debug"] (EnvNum 0)
    noCheck
    (unlines
      [ "Enable type-checker debugging output:"
      , "  *  0  no debug output"
      , "  *  1  show type-checker debug info"
      , "  * >1  show type-checker debug info and interactions with SMT solver"]) $
    \case EnvNum n -> do changed <- modifyRW (\rw -> ( rw{ eTCConfig = (eTCConfig rw){ T.solverVerbose = n } }
                                                     , n /= T.solverVerbose (eTCConfig rw)
                                                     ))
                         when changed resetTCSolver
          _        -> return ()
  , OptionDescr "coreLint" ["core-lint"] (EnvBool False)
    noCheck
    "Enable sanity checking of type-checker." $
      let setIt x = do me <- getModuleEnv
                       setModuleEnv me { M.meCoreLint = x }
      in \case EnvBool True  -> setIt M.CoreLint
               EnvBool False -> setIt M.NoCoreLint
               _             -> return ()

  , OptionDescr "evalForeign" ["eval-foreign"] defaultEvalForeignOpt
    checkEvalForeign
    (unlines
      [ "How to evaluate 'foreign' bindings:"
      , "  * always  Always call the foreign implementation with the FFI and"
      , "            report an error on module load if it is unavailable."
      , "  * prefer  Call the foreign implementation with the FFI by default,"
      , "            and when unavailable, fall back to the cryptol"
      , "            implementation if present and report runtime error"
      , "            otherwise."
      , "  * never   Never use the FFI. Always call the cryptol implementation"
      , "            if present, and report runtime error otherwise."
      , "Note: changes take effect on module reload."
      ]) $
    \case EnvString s
            | Just p <- lookup s evalForeignOptMap -> do
              me <- getModuleEnv
              setModuleEnv me { M.meEvalForeignPolicy = p }
          _ -> pure ()

  , simpleOpt "hashConsing" ["hash-consing"] (EnvBool True) noCheck
    "Enable hash-consing in the What4 symbolic backends."

  , simpleOpt "proverStats" ["prover-stats"] (EnvBool True) noCheck
    "Enable prover timing statistics."

  , simpleOpt "proverValidate" ["prover-validate"] (EnvBool False) noCheck
    "Validate :sat examples and :prove counter-examples for correctness."

  , simpleOpt "showExamples" ["show-examples"] (EnvBool True) noCheck
    "Print the (counter) example after :sat or :prove"

  , simpleOpt "fpBase" ["fp-base"] (EnvNum 16) checkBase
    "The base to display floating point numbers at (2, 8, 10, or 16)."

  , simpleOpt "fpFormat" ["fp-format"] (EnvString "free") checkPPFloatFormat
    $ unlines
    [ "Specifies the format to use when showing floating point numbers:"
    , "  * free      show using as many digits as needed"
    , "  * free+exp  like `free` but always show exponent"
    , "  * .NUM      show NUM (>=1) digits after floating point"
    , "  * NUM       show using NUM (>=1) significant digits"
    , "  * NUM+exp   like NUM but always show exponent"
    ]

  , simpleOpt "ignoreSafety" ["ignore-safety"] (EnvBool False) noCheck
    "Ignore safety predicates when performing :sat or :prove checks"

  , simpleOpt "fieldOrder" ["field-order"] (EnvString "display") checkFieldOrder
    $ unlines
    [ "The order that record fields are displayed in."
    , "  * display      try to match the order they were written in the source code"
    , "  * canonical    use a predictable, canonical order"
    ]

  , simpleOpt "timeMeasurementPeriod" ["time-measurement-period"] (EnvNum 10)
    checkTimeMeasurementPeriod
    $ unlines
    [ "The period of time in seconds to spend collecting measurements when"
    , "  running :time."
    , "This is a lower bound and the actual time taken might be higher if the"
    , "  evaluation takes a long time."
    ]

  , simpleOpt "timeQuiet" ["time-quiet"] (EnvBool False) noCheck
    "Suppress output of :time command and only bind result to `it`."
  ]


parsePPFloatFormat :: String -> Maybe PPFloatFormat
parsePPFloatFormat s =
  case s of
    "free"     -> Just $ FloatFree AutoExponent
    "free+exp" -> Just $ FloatFree ForceExponent
    '.' : xs   -> FloatFrac <$> readMaybe xs
    _ | (as,res) <- break (== '+') s
      , Just n   <- readMaybe as
      , Just e   <- case res of
                      "+exp" -> Just ForceExponent
                      ""     -> Just AutoExponent
                      _      -> Nothing
        -> Just (FloatFixed n e)
    _  -> Nothing

checkPPFloatFormat :: Checker
checkPPFloatFormat val =
  case val of
    EnvString s | Just _ <- parsePPFloatFormat s -> noWarns Nothing
    _ -> noWarns $ Just "Failed to parse `fp-format`"

parseFieldOrder :: String -> Maybe FieldOrder
parseFieldOrder "canonical" = Just CanonicalOrder
parseFieldOrder "display" = Just DisplayOrder
parseFieldOrder _ = Nothing

checkFieldOrder :: Checker
checkFieldOrder val =
  case val of
    EnvString s | Just _ <- parseFieldOrder s -> noWarns Nothing
    _ -> noWarns $ Just "Failed to parse field-order (expected one of \"canonical\" or \"display\")"

-- | Check the value to the `base` option.
checkBase :: Checker
checkBase val = case val of
  EnvNum n
    | n `elem` [2,8,10,16] -> noWarns Nothing
    | otherwise            -> noWarns $ Just "base must be 2, 8, 10, or 16"
  _                     -> noWarns $ Just "unable to parse a value for base"

checkInfLength :: Checker
checkInfLength val = case val of
  EnvNum n
    | n >= 0    -> noWarns Nothing
    | otherwise -> noWarns $ Just "the number of elements should be positive"
  _ -> noWarns $ Just "unable to parse a value for infLength"

checkProver :: Checker
checkProver val = case val of
  EnvString (map toLower -> s)
    | s `elem` W4.proverNames ->
      io (W4.setupProver s) >>= \case
        Left msg -> noWarns (Just msg)
        Right (ws, cfg) ->
          do modifyRW_ (\rw -> rw{ eProverConfig = Right cfg })
             return (Nothing, ws)
    | s `elem` SBV.proverNames ->
      io (SBV.setupProver s) >>= \case
        Left msg -> noWarns (Just msg)
        Right (ws, cfg) ->
          do modifyRW_ (\rw -> rw{ eProverConfig = Left cfg })
             return (Nothing, ws)

    | otherwise ->
      noWarns $ Just $ "Prover must be " ++ proverListString

  _ -> noWarns $ Just "unable to parse a value for prover"

allProvers :: [String]
allProvers = SBV.proverNames ++ W4.proverNames

proverListString :: String
proverListString = concatMap (++ ", ") (init allProvers) ++ "or " ++ last allProvers

checkSatNum :: Checker
checkSatNum val = case val of
  EnvString "all" -> noWarns Nothing
  EnvString s ->
    case readMaybe s :: Maybe Int of
      Just n | n >= 1 -> noWarns Nothing
      _               -> noWarns $ Just "must be an integer > 0 or \"all\""
  _ -> noWarns $ Just "unable to parse a value for satNum"

getUserSatNum :: REPL SatNum
getUserSatNum = do
  s <- getKnownUser "satNum"
  case s of
    "all"                     -> return AllSat
    _ | Just n <- readMaybe s -> return (SomeSat n)
    _                         -> panic "REPL.Monad.getUserSatNum"
                                   [ "invalid satNum option" ]

checkEvalForeign :: Checker
checkEvalForeign (EnvString s)
  | Just _ <- lookup s evalForeignOptMap = noWarns Nothing
checkEvalForeign _ = noWarns $ Just $ "evalForeign must be one of: "
  ++ intercalate ", " (map fst evalForeignOptMap)

evalForeignOptMap :: [(String, M.EvalForeignPolicy)]
evalForeignOptMap =
  [ ("always", M.AlwaysEvalForeign)
  , ("prefer", M.PreferEvalForeign)
  , ("never", M.NeverEvalForeign)
  ]

defaultEvalForeignOpt :: EnvVal
defaultEvalForeignOpt =
  case lookup M.defaultEvalForeignPolicy (map swap evalForeignOptMap) of
    Just s -> EnvString s
    Nothing -> panic "defaultEvalForeignOpt"
      ["cannot find option value matching default EvalForeignPolicy"]

checkTimeMeasurementPeriod :: Checker
checkTimeMeasurementPeriod (EnvNum n)
  | n >= 1 = noWarns Nothing
  | otherwise = noWarns $
    Just "timeMeasurementPeriod must be a positive integer"
checkTimeMeasurementPeriod _ = noWarns $
  Just "unable to parse value for timeMeasurementPeriod"

-- Environment Utilities -------------------------------------------------------

whenDebug :: REPL () -> REPL ()
whenDebug m = do
  b <- getKnownUser "debug"
  when b m

-- Smoke Testing ---------------------------------------------------------------

smokeTest :: REPL [Smoke]
smokeTest = catMaybes <$> sequence tests
  where
    tests = [ z3exists ]

type SmokeTest = REPL (Maybe Smoke)

data Smoke
  = Z3NotFound
  deriving (Show, Eq)

instance PP Smoke where
  ppPrec _ smoke =
    case smoke of
      Z3NotFound -> text . intercalate " " $ [
          "[error] z3 is required to run Cryptol, but was not found in the"
        , "system path. See the Cryptol README for more on how to install z3."
        ]

z3exists :: SmokeTest
z3exists = do
  mPath <- io $ findExecutable "z3"
  case mPath of
    Nothing -> return (Just Z3NotFound)
    Just _  -> return Nothing
