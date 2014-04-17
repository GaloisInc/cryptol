-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2014 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE DeriveDataTypeable #-}
module Notebook where

import REPL.Command (loadPrelude,findNbCommand,parseCommand,runCommand,replParse,liftModuleCmd)
import REPL.Monad (REPL(..) ,runREPL, lName, lPath)
import qualified REPL.Monad as REPL

import qualified Cryptol.ModuleSystem as M
import Cryptol.Parser (defaultConfig, parseModule, Config(..), ParseError)
import qualified Cryptol.Parser.AST as P
import Cryptol.Parser.Names (allNamesD, tnamesNT)
import Cryptol.Parser.Position (Located(..), emptyRange)
import qualified Cryptol.TypeCheck.AST as T
import Cryptol.Utils.PP (PP(..), pp, hang, text)

import Control.Applicative ((<$>))
import qualified Control.Exception as X
import Control.Monad (forever)
import Data.IORef (IORef, newIORef, readIORef, modifyIORef)
import Data.List (isPrefixOf)
import qualified Data.Set as Set
import Data.Typeable (Typeable)
import System.IO (hFlush, stdout)

-- Notebook Environment --------------------------------------------------------

-- | All of the top-level declarations along with all of the names
-- that they define. We need to associate the names in order to remove
-- declarations from the module context when they're overwritten.
type NamedDecls = [([P.QName], P.TopDecl)]

data RW = RW
  { eNamedDecls :: NamedDecls
  }

-- | The default environment is simple now but might get more
-- complicated, so it's made in IO.
defaultRW :: IO RW
defaultRW = return RW { eNamedDecls = [] }

-- Notebook Monad --------------------------------------------------------------

-- | The Notebook is just a REPL augmented with an incrementally-built module.
newtype NB a = NB { unNB :: IORef RW -> REPL a }

instance Functor NB where
  {-# INLINE fmap #-}
  fmap f m = NB (\ref -> fmap f (unNB m ref))

instance Monad NB where
  {-# INLINE return #-}
  return x = NB (\_ -> return x)

  {-# INLINE (>>=) #-}
  m >>= f = NB $ \ref -> do
    x <- unNB m ref
    unNB (f x) ref

-- | Run a NB action with a fresh environment.
runNB :: NB a -> IO a
runNB m = do
  ref <- newIORef =<< defaultRW
  runREPL True $ unNB m ref

-- | Lift a REPL action into the NB monad.
liftREPL :: REPL a -> NB a
liftREPL m = NB (\_ -> m)

-- Primitives ------------------------------------------------------------------

io :: IO a -> NB a
io m = liftREPL (REPL.io m)

getRW :: NB RW
getRW  = NB (\ref -> REPL.io (readIORef ref))

modifyRW_ :: (RW -> RW) -> NB ()
modifyRW_ f = NB (\ref -> REPL.io (modifyIORef ref f))

getTopDecls :: NB NamedDecls
getTopDecls = eNamedDecls `fmap` getRW

setTopDecls :: NamedDecls -> NB ()
setTopDecls nds = modifyRW_ (\rw -> rw { eNamedDecls = nds })

modifyTopDecls :: (NamedDecls -> NamedDecls) -> NB NamedDecls
modifyTopDecls f = do
  nds <- f `fmap` getTopDecls
  setTopDecls nds
  return nds

-- Exceptions ------------------------------------------------------------------

-- | Notebook exceptions.
data NBException
  = REPLException REPL.REPLException
  | AutoParseError ParseError
    deriving (Show, Typeable)

instance X.Exception NBException

instance PP NBException where
  ppPrec _ nbe = case nbe of
    REPLException exn -> pp exn
    AutoParseError exn ->
        hang (text "[error] Failed to parse cell as a module or as interactive input")
           4 (pp exn)

-- | Raise an exception
raise :: NBException -> NB a
raise exn = io (X.throwIO exn)

-- | Catch an exception
catch :: NB a -> (NBException -> NB a) -> NB a
catch m k = NB (\ref ->
              REPL (\replRef -> unREPL (unNB m ref) replRef
                                `X.catches`
                                -- catch a REPLException or a NBException
                                [ X.Handler $ \e -> unREPL (unNB (k (REPLException e)) ref) replRef
                                , X.Handler $ \e -> unREPL (unNB (k e) ref) replRef
                                ]))

-- | Try running a possibly-excepting computation
try :: NB a -> NB (Either NBException a)
try m = catch (Right `fmap` m) (return . Left)

-- | Try running the given action, printing any exceptions that arise.
runExns :: NB () -> NB ()
runExns m = m `catch` \x -> io $ print $ pp x

-- Module Manipulation ---------------------------------------------------------

nbName :: P.Located P.ModName
nbName = Located { srcRange = emptyRange
                 , thing    = P.ModName ["Notebook"]
                 }

-- | Distill a module into a list of decls along with the names
-- defined by those decls.
modNamedDecls :: P.Module -> NamedDecls
modNamedDecls m = [(tdNames td, td) | td <- P.mDecls m]

-- | Build a module of the given name using the given list of
-- declarations.
moduleFromDecls :: P.Located P.ModName -> NamedDecls -> P.Module
moduleFromDecls name nds =
  P.Module { P.mName = name
           , P.mImports = []
           , P.mDecls = map snd nds
           }

-- | In @updateNamedDecls old new = result@, @result@ is a
-- right-biased combination of @old@ and @new@ with the following
-- semantics:
-- 
-- If a name @x@ is defined in @old@ and not @new@, or in @new@ and
-- not @old@, all declarations of @x@ are in @result@.
-- 
-- If a name @x@ is defined in both @old@ and @new@, /none/ of the
-- declarations of @x@ from @old@ are in @result@, and all
-- declarations of @x@ from @new@ are in @result@.
updateNamedDecls :: NamedDecls -> NamedDecls -> NamedDecls
updateNamedDecls old new = filteredOld ++ new
  where newNames = Set.fromList $ concat $ map fst new
        containsNewName = any (\x -> Set.member x newNames)
        filteredOld = filter (\(xs,_) -> not (containsNewName xs)) old


-- | The names defined by a top level declaration
tdNames :: P.TopDecl -> [P.QName]
tdNames (P.Decl d)      = map P.thing $ allNamesD $ P.tlValue d
tdNames (P.TDNewtype d) = map P.thing $ fst $ tnamesNT $ P.tlValue d
tdNames (P.Include _)   = []

removeIncludes :: P.Module -> P.Module
removeIncludes m = m { P.mDecls = decls' }
  where decls' = filter (not . isInclude) $ P.mDecls m
        isInclude (P.Include _) = True
        isInclude _             = False

removeImports :: P.Module -> P.Module
removeImports m = m { P.mImports = [] }
