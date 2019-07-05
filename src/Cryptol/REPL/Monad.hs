-- |
-- Module      :  Cryptol.REPL.Monad
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleInstances #-}

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
  , uniqify, freshName
  , getTSyns, getNewtypes, getVars
  , whenDebug
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
  , disableLet
  , enableLet
  , getLetEnabled
  , validEvalContext
  , updateREPLTitle
  , setUpdateREPLTitle

    -- ** Config Options
  , EnvVal(..)
  , OptionDescr(..)
  , setUser, getUser, getKnownUser, tryGetUser
  , userOptions
  , getUserSatNum
  , getUserShowProverStats
  , getUserProverValidate

    -- ** Configurable Output
  , getPutStr
  , getLogger
  , setPutStr

    -- ** Smoke Test
  , smokeTest
  , Smoke(..)

  ) where

import Cryptol.REPL.Trie

import Cryptol.Eval (EvalError)
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
import qualified Cryptol.IR.FreeVars as T
import qualified Cryptol.Utils.Ident as I
import Cryptol.Utils.PP
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.Logger(Logger, logPutStr, funLogger)
import qualified Cryptol.Parser.AST as P
import Cryptol.Symbolic (proverNames, lookupProver, SatNum(..))

import Control.Monad (ap,unless,when)
import Control.Monad.Base
import Control.Monad.IO.Class
import Control.Monad.Trans.Control
import Data.Char (isSpace)
import Data.IORef
    (IORef,newIORef,readIORef,modifyIORef,atomicModifyIORef)
import Data.List (intercalate, isPrefixOf, unfoldr, sortBy)
import Data.Maybe (catMaybes)
import Data.Ord (comparing)
import Data.Typeable (Typeable)
import System.Directory (findExecutable)
import qualified Control.Exception as X
import qualified Data.Map as Map
import qualified Data.Set as Set
import Text.Read (readMaybe)

import Data.SBV.Dynamic (sbvCheckSolverInstallation)

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

  , eLetEnabled  :: Bool
    -- ^ Should we allow `let` on the command line

  , eUpdateTitle :: REPL ()
    -- ^ Execute this every time we load a module.
    -- This is used to change the title of terminal when loading a module.
  }

-- | Initial, empty environment.
defaultRW :: Bool -> Logger -> IO RW
defaultRW isBatch l = do
  env <- M.initialModuleEnv
  return RW
    { eLoadedMod   = Nothing
    , eEditFile    = Nothing
    , eContinue    = True
    , eIsBatch     = isBatch
    , eModuleEnv   = env
    , eUserEnv     = mkUserEnv userOptions
    , eLogger      = l
    , eLetEnabled  = True
    , eUpdateTitle = return ()
    }

-- | Build up the prompt for the REPL.
mkPrompt :: RW -> String
mkPrompt rw
  | eIsBatch rw = ""
  | detailedPrompt = withEdit ++ "> "
  | otherwise      = modLn ++ "> "
  where
  detailedPrompt = False

  modLn   =
    case lName =<< eLoadedMod rw of
      Nothing -> show (pp I.preludeName)
      Just m
        | M.isLoadedParamMod m (M.meLoadedModules (eModuleEnv rw)) ->
                 modName ++ "(parameterized)"
        | otherwise -> modName
        where modName = pretty m

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
runREPL :: Bool -> Logger -> REPL a -> IO a
runREPL isBatch l m = do
  ref <- newIORef =<< defaultRW isBatch l
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

-- Exceptions ------------------------------------------------------------------

-- | REPL exceptions.
data REPLException
  = ParseError ParseError
  | FileNotFound FilePath
  | DirectoryNotFound FilePath
  | NoPatError [Error]
  | NoIncludeError [IncludeError]
  | EvalError EvalError
  | ModuleSystemError NameDisp M.ModuleError
  | EvalPolyError T.Schema
  | TypeNotTestable T.Type
  | EvalInParamModule [M.Name]
  | SBVError String
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
    EvalPolyError s      -> text "Cannot evaluate polymorphic value."
                         $$ text "Type:" <+> pp s
    TypeNotTestable t    -> text "The expression is not of a testable type."
                         $$ text "Type:" <+> pp t
    EvalInParamModule xs ->
      text "Expression depends on definitions from a parameterized module:"
        $$ nest 2 (vcat (map pp xs))
    SBVError s           -> text "SBV error:" $$ text s

-- | Raise an exception.
raise :: REPLException -> REPL a
raise exn = io (X.throwIO exn)


catch :: REPL a -> (REPLException -> REPL a) -> REPL a
catch m k = REPL (\ ref -> rethrowEvalError (unREPL m ref) `X.catch` \ e -> unREPL (k e) ref)

finally :: REPL a -> REPL b -> REPL a
finally m1 m2 = REPL (\ref -> unREPL m1 ref `X.finally` unREPL m2 ref)


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

modifyRW :: (RW -> (RW,a)) -> REPL a
modifyRW f = REPL (\ ref -> atomicModifyIORef ref f)

modifyRW_ :: (RW -> RW) -> REPL ()
modifyRW_ f = REPL (\ ref -> modifyIORef ref f)

-- | Construct the prompt for the current environment.
getPrompt :: REPL String
getPrompt  = mkPrompt `fmap` getRW

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
asBatch :: REPL a -> REPL a
asBatch body = do
  wasBatch <- eIsBatch `fmap` getRW
  modifyRW_ $ (\ rw -> rw { eIsBatch = True })
  a <- body
  modifyRW_ $ (\ rw -> rw { eIsBatch = wasBatch })
  return a

disableLet :: REPL ()
disableLet  = modifyRW_ (\ rw -> rw { eLetEnabled = False })

enableLet :: REPL ()
enableLet  = modifyRW_ (\ rw -> rw { eLetEnabled = True })

-- | Are let-bindings enabled in this REPL?
getLetEnabled :: REPL Bool
getLetEnabled = fmap eLetEnabled getRW

-- | Is evaluation enabled.  If the currently focused module is
-- parameterized, then we cannot evalute.
validEvalContext :: T.FreeVars a => a -> REPL ()
validEvalContext a =
  do me <- eModuleEnv <$> getRW
     let ds      = T.freeVars a
         badVals = foldr badName Set.empty (T.valDeps ds)
         bad     = foldr badName badVals (T.tyDeps ds)

         badName nm bs =
           case M.nameInfo nm of
             M.Declared m _
               | M.isLoadedParamMod m (M.meLoadedModules me) -> Set.insert nm bs
             _ -> bs

     unless (Set.null bad) $
       raise (EvalInParamModule (Set.toList bad))



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

getFocusedEnv :: REPL (M.IfaceParams,M.IfaceDecls,M.NamingEnv,NameDisp)
getFocusedEnv  = do
  me <- getModuleEnv
  -- dyNames is a NameEnv that removes the #Uniq prefix from interactively-bound
  -- variables.
  let (dyDecls,dyNames,dyDisp) = M.dynamicEnv me
  let (fParams,fDecls,fNames,fDisp) = M.focusedEnv me
  return ( fParams
         , dyDecls `mappend` fDecls
         , dyNames `M.shadowing` fNames
         , dyDisp `mappend` fDisp)

  -- -- the subtle part here is removing the #Uniq prefix from
  -- -- interactively-bound variables, and also excluding any that are
  -- -- shadowed and thus can no longer be referenced
  -- let (fDecls,fNames,fDisp) = M.focusedEnv me
  --     edecls = M.ifDecls dyDecls
  --     -- is this QName something the user might actually type?
  --     isShadowed (qn@(P.QName (Just (P.unModName -> ['#':_])) name), _) =
  --         case Map.lookup localName neExprs of
  --           Nothing -> False
  --           Just uniqueNames -> isNamed uniqueNames
  --       where localName = P.QName Nothing name
  --             isNamed us = any (== qn) (map M.qname us)
  --             neExprs = M.neExprs (M.deNames (M.meDynEnv me))
  --     isShadowed _ = False
  --     unqual ((P.QName _ name), ifds) = (P.QName Nothing name, ifds)
  --     edecls' = Map.fromList
  --             . map unqual
  --             . filter isShadowed
  --             $ Map.toList edecls
  -- return (decls `mappend` mempty { M.ifDecls = edecls' }, names `mappend` dyNames)

getVars :: REPL (Map.Map M.Name M.IfaceDecl)
getVars  = do
  (_,decls,_,_) <- getFocusedEnv
  return (M.ifDecls decls)

getTSyns :: REPL (Map.Map M.Name T.TySyn)
getTSyns  = do
  (_,decls,_,_) <- getFocusedEnv
  return (M.ifTySyns decls)

getNewtypes :: REPL (Map.Map M.Name T.Newtype)
getNewtypes = do
  (_,decls,_,_) <- getFocusedEnv
  return (M.ifNewtypes decls)

-- | Get visible variable names.
getExprNames :: REPL [String]
getExprNames =
  do (_,_, fNames, _) <- getFocusedEnv
     return (map (show . pp) (Map.keys (M.neExprs fNames)))

-- | Get visible type signature names.
getTypeNames :: REPL [String]
getTypeNames  =
  do (_,_, fNames, _) <- getFocusedEnv
     return (map (show . pp) (Map.keys (M.neTypes fNames)))

-- | Return a list of property names, sorted by position in the file.
getPropertyNames :: REPL ([M.Name],NameDisp)
getPropertyNames =
  do (_,decls,_,names) <- getFocusedEnv
     let xs = M.ifDecls decls
         ps = sortBy (comparing (from . M.nameLoc))
            $ [ x | (x,d) <- Map.toList xs, T.PragmaProperty `elem` M.ifDeclPragmas d ]

     return (ps, names)

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


-- | Given an existing qualified name, prefix it with a
-- relatively-unique string. We make it unique by prefixing with a
-- character @#@ that is not lexically valid in a module name.
uniqify :: M.Name -> REPL M.Name

uniqify name =
  case M.nameInfo name of
    M.Declared ns s ->
      M.liftSupply (M.mkDeclared ns s (M.nameIdent name) (M.nameFixity name) (M.nameLoc name))

    M.Parameter ->
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
  M.liftSupply (M.mkDeclared I.interactiveName sys i Nothing emptyRange)


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
setUser name val = case lookupTrieExact name userOptions of

  [opt] -> setUserOpt opt
  []    -> rPutStrLn ("Unknown env value `" ++ name ++ "`")
  _     -> rPutStrLn ("Ambiguous env value `" ++ name ++ "`")

  where
  setUserOpt opt = case optDefault opt of
    EnvString _ -> doCheck (EnvString val)

    EnvProg _ _ ->
      case splitOptArgs val of
        prog:args -> doCheck (EnvProg prog args)
        [] -> rPutStrLn ("Failed to parse command for field, `" ++ name ++ "`")

    EnvNum _ -> case reads val of
      [(x,_)] -> doCheck (EnvNum x)
      _ -> rPutStrLn ("Failed to parse number for field, `" ++ name ++ "`")

    EnvBool _
      | any (`isPrefixOf` val) ["enable", "on", "yes", "true"] ->
        writeEnv (EnvBool True)
      | any (`isPrefixOf` val) ["disable", "off", "no", "false"] ->
        writeEnv (EnvBool False)
      | otherwise ->
        rPutStrLn ("Failed to parse boolean for field, `" ++ name ++ "`")
    where
    doCheck v = do (r,ws) <- io (optCheck opt v)
                   case r of
                     Just err -> rPutStrLn err
                     Nothing  -> do mapM_ rPutStrLn ws
                                    writeEnv v
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

badIsEnv :: String -> a
badIsEnv x = panic "fromEnvVal" [ "[REPL] Expected a `" ++ x ++ "` value." ]


getUserShowProverStats :: REPL Bool
getUserShowProverStats = getKnownUser "prover-stats"

getUserProverValidate :: REPL Bool
getUserProverValidate = getKnownUser "prover-validate"

-- Environment Options ---------------------------------------------------------

type OptionMap = Trie OptionDescr

mkOptionMap :: [OptionDescr] -> OptionMap
mkOptionMap  = foldl insert emptyTrie
  where
  insert m d = insertTrie (optName d) d m

-- | Returns maybe an error, and some warnings
type Checker = EnvVal -> IO (Maybe String, [String])

noCheck :: Checker
noCheck _ = return (Nothing, [])

noWarns :: Maybe String -> IO (Maybe String, [String])
noWarns mb = return (mb, [])

data OptionDescr = OptionDescr
  { optName    :: String
  , optDefault :: EnvVal
  , optCheck   :: Checker
  , optHelp    :: String
  , optEff     :: EnvVal -> REPL ()
  }

simpleOpt :: String -> EnvVal -> Checker -> String -> OptionDescr
simpleOpt optName optDefault optCheck optHelp =
  OptionDescr { optEff = \ _ -> return (), .. }

userOptions :: OptionMap
userOptions  = mkOptionMap
  [ simpleOpt "base" (EnvNum 16) checkBase
    "The base to display words at (2, 8, 10, or 16)."
  , simpleOpt "debug" (EnvBool False) noCheck
    "Enable debugging output."
  , simpleOpt "ascii" (EnvBool False) noCheck
    "Whether to display 7- or 8-bit words using ASCII notation."
  , simpleOpt "infLength" (EnvNum 5) checkInfLength
    "The number of elements to display for infinite sequences."
  , simpleOpt "tests" (EnvNum 100) noCheck
    "The number of random tests to try with ':check'."
  , simpleOpt "satNum" (EnvString "1") checkSatNum
    "The maximum number of :sat solutions to display (\"all\" for no limit)."
  , simpleOpt "prover" (EnvString "z3") checkProver $
    "The external SMT solver for ':prove' and ':sat'\n(" ++ proverListString ++ ")."
  , simpleOpt "warnDefaulting" (EnvBool True) noCheck
    "Choose whether to display warnings when defaulting."
  , simpleOpt "warnShadowing" (EnvBool True) noCheck
    "Choose whether to display warnings when shadowing symbols."
  , simpleOpt "smtfile" (EnvString "-") noCheck
    "The file to use for SMT-Lib scripts (for debugging or offline proving).\nUse \"-\" for stdout."
  , OptionDescr "mono-binds" (EnvBool True) noCheck
    "Whether or not to generalize bindings in a 'where' clause." $
    \case EnvBool b -> do me <- getModuleEnv
                          setModuleEnv me { M.meMonoBinds = b }
          _         -> return ()

  , OptionDescr "tc-solver" (EnvProg "z3" [ "-smt2", "-in" ])
    noCheck  -- TODO: check for the program in the path
    "The solver that will be used by the type checker." $
    \case EnvProg prog args -> do me <- getModuleEnv
                                  let cfg = M.meSolverConfig me
                                  setModuleEnv me { M.meSolverConfig =
                                                      cfg { T.solverPath = prog
                                                          , T.solverArgs = args } }
          _                 -> return ()

  , OptionDescr "tc-debug" (EnvNum 0)
    noCheck
    "Enable type-checker debugging output." $
    \case EnvNum n -> do me <- getModuleEnv
                         let cfg = M.meSolverConfig me
                         setModuleEnv me { M.meSolverConfig = cfg{ T.solverVerbose = fromIntegral n } }
          _        -> return ()
  , OptionDescr "core-lint" (EnvBool False)
    noCheck
    "Enable sanity checking of type-checker." $
      let setIt x = do me <- getModuleEnv
                       setModuleEnv me { M.meCoreLint = x }
      in \case EnvBool True  -> setIt M.CoreLint
               EnvBool False -> setIt M.NoCoreLint
               _             -> return ()

  , simpleOpt "prover-stats" (EnvBool True) noCheck
    "Enable prover timing statistics."

  , simpleOpt "prover-validate" (EnvBool False) noCheck
    "Validate :sat examples and :prove counter-examples for correctness."

  , simpleOpt "show-examples" (EnvBool True) noCheck
    "Print the (counter) example after :sat or :prove"
  ]


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
  EnvString s
    | s `notElem` proverNames ->
      noWarns $ Just $ "Prover must be " ++ proverListString
    | s `elem` ["offline", "any"] -> noWarns Nothing
    | otherwise ->
      do let prover = lookupProver s
         available <- sbvCheckSolverInstallation prover
         let ws = if available
                     then []
                     else ["Warning: " ++ s ++ " installation not found"]
         return (Nothing, ws)

  _ -> noWarns $ Just "unable to parse a value for prover"

proverListString :: String
proverListString = concatMap (++ ", ") (init proverNames) ++ "or " ++ last proverNames

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

