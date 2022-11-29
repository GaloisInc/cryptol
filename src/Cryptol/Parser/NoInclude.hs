-- |
-- Module      :  Cryptol.Parser.NoInclude
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE BlockArguments #-}
module Cryptol.Parser.NoInclude
  ( removeIncludesModule
  , IncludeError(..), ppIncludeError
  ) where

import qualified Control.Applicative as A
import Control.DeepSeq
import qualified Control.Exception as X
import qualified Control.Monad.Fail as Fail

import Data.Set(Set)
import qualified Data.Set as Set
import Data.ByteString (ByteString)
import Data.Either (partitionEithers)
import Data.Text(Text)
import qualified Data.Text.Encoding as T (decodeUtf8')
import Data.Text.Encoding.Error (UnicodeException)
import GHC.Generics (Generic)
import MonadLib
import System.Directory (makeAbsolute)
import System.FilePath (takeDirectory,(</>),isAbsolute)

import Cryptol.Utils.PP hiding ((</>))
import Cryptol.Parser (parseProgramWith)
import Cryptol.Parser.AST
import Cryptol.Parser.LexerUtils (Config(..),defaultConfig)
import Cryptol.Parser.ParserUtils
import Cryptol.Parser.Unlit (guessPreProc)

removeIncludesModule ::
  (FilePath -> IO ByteString) ->
  FilePath ->
  Module PName ->
  IO (Either [IncludeError] (Module PName, Set FilePath))
removeIncludesModule reader modPath m =
  runNoIncM reader modPath (noIncludeModule m)

data IncludeError
  = IncludeFailed (Located FilePath)
  | IncludeDecodeFailed (Located FilePath) UnicodeException
  | IncludeParseError ParseError
  | IncludeCycle [Located FilePath]
    deriving (Show, Generic, NFData)

ppIncludeError :: IncludeError -> Doc
ppIncludeError ie = case ie of

  IncludeFailed lp -> (char '`' <.> text (thing lp) <.> char '`')
                  <+> text "included at"
                  <+> pp (srcRange lp)
                  <+> text "was not found"

  IncludeDecodeFailed lp err -> (char '`' <.> text (thing lp) <.> char '`')
                            <+> text "included at"
                            <+> pp (srcRange lp)
                            <+> text "contains invalid UTF-8."
                            <+> text "Details:"
                            $$  nest 2 (vcat (map text (lines (X.displayException err))))

  IncludeParseError pe -> ppError pe

  IncludeCycle is -> text "includes form a cycle:"
                  $$ nest 2 (vcat (map (pp . srcRange) is))


newtype NoIncM a = M
  { unM :: ReaderT Env
         ( ExceptionT [IncludeError]
         ( StateT Deps
           IO
         )) a }

type Deps = Set FilePath

data Env = Env { envSeen       :: [Located FilePath]
                 -- ^ Files that have been loaded

               , envIncPath    :: FilePath
                 -- ^ The path that includes are relative to

               , envFileReader :: FilePath -> IO ByteString
                 -- ^ How to load files
               }


runNoIncM ::
  (FilePath -> IO ByteString) ->
  FilePath ->
  NoIncM a -> IO (Either [IncludeError] (a,Deps))
runNoIncM reader sourcePath m =
  do incPath <- getIncPath sourcePath
     (mb,s) <- runM (unM m)
                  Env { envSeen = []
                      , envIncPath = incPath
                      , envFileReader = reader
                      }
                  Set.empty
     pure
       do ok <- mb
          pure (ok,s)

tryNoIncM :: NoIncM a -> NoIncM (Either [IncludeError] a)
tryNoIncM m = M (try (unM m))

-- | Get the absolute directory name of a file that contains cryptol source.
getIncPath :: FilePath -> IO FilePath
getIncPath file = makeAbsolute (takeDirectory file)

-- | Run a 'NoIncM' action with a different include path.  The argument is
-- expected to be the path of a file that contains cryptol source, and will be
-- adjusted with getIncPath.
withIncPath :: FilePath -> NoIncM a -> NoIncM a
withIncPath path (M body) = M $
  do incPath <- inBase (getIncPath path)
     env     <- ask
     local env { envIncPath = incPath } body

-- | Adjust an included file with the current include path.
fromIncPath :: FilePath -> NoIncM FilePath
fromIncPath path
  | isAbsolute path = return path
  | otherwise       = M
    do Env { .. } <- ask
       return (envIncPath </> path)

addDep :: FilePath -> NoIncM ()
addDep path = M
  do s <- get
     let s1 = Set.insert path s
     s1 `seq` set s1


instance Functor NoIncM where
  fmap = liftM

instance A.Applicative NoIncM where
  pure x = M (pure x)
  (<*>) = ap

instance Monad NoIncM where
  return   = pure
  m >>= f  = M (unM m >>= unM . f)

instance Fail.MonadFail NoIncM where
  fail x = M (fail x)

-- | Raise an 'IncludeFailed' error.
includeFailed :: Located FilePath -> NoIncM a
includeFailed path = M (raise [IncludeFailed path])

-- | Push a path on the stack of included files, and run an action.  If the path
-- is already on the stack, an include cycle has happened, and an error is
-- raised.
pushPath :: Located FilePath -> NoIncM a -> NoIncM a
pushPath path m = M $ do
  Env { .. } <- ask
  let alreadyIncluded l = thing path == thing l
  when (any alreadyIncluded envSeen) (raise [IncludeCycle envSeen])
  local Env { envSeen = path:envSeen, .. } (unM m)

-- | Lift an IO operation, with a way to handle the exception that it might
-- throw.
failsWith :: X.Exception e => IO a -> (e -> NoIncM a) -> NoIncM a
failsWith m k = M $ do
  e <- inBase (X.try m)
  case e of
    Right a  -> return a
    Left exn -> unM (k exn)

-- | Like 'mapM', but tries to collect as many errors as possible before
-- failing.
collectErrors :: (a -> NoIncM b) -> [a] -> NoIncM [b]
collectErrors f ts = do
  es <- mapM (tryNoIncM . f) ts
  let (ls,rs) = partitionEithers es
      errs    = concat ls
  unless (null errs) (M (raise errs))
  return rs

-- | Remove includes from a module.
noIncludeModule :: ModuleG mname PName -> NoIncM (ModuleG mname PName)
noIncludeModule m =
  do newDef <- case mDef m of
                 NormalModule ds         -> NormalModule <$> doDecls ds
                 FunctorInstance f as is -> pure (FunctorInstance f as is)
                 InterfaceModule s       -> pure (InterfaceModule s)
     pure m { mDef = newDef }
  where
  doDecls    = fmap concat . collectErrors noIncTopDecl

-- | Remove includes from a program.
noIncludeProgram :: Program PName -> NoIncM (Program PName)
noIncludeProgram (Program tds) =
  (Program . concat) `fmap` collectErrors noIncTopDecl tds

-- | Substitute top-level includes with the declarations from the files they
-- reference.
noIncTopDecl :: TopDecl PName -> NoIncM [TopDecl PName]
noIncTopDecl td = case td of
  Decl _     -> pure [td]
  DPrimType {} -> pure [td]
  TDNewtype _-> pure [td]
  DParamDecl {} -> pure [td]
  DInterfaceConstraint {} -> pure [td]
  Include lf -> resolveInclude lf
  DModule tl ->
    case tlValue tl of
      NestedModule m ->
        do m1 <- noIncludeModule m
           pure [ DModule tl { tlValue = NestedModule m1 } ]
  DImport {} -> pure [td]
  DModParam {} -> pure [td]

-- | Resolve the file referenced by a include into a list of top-level
-- declarations.
resolveInclude :: Located FilePath -> NoIncM [TopDecl PName]
resolveInclude lf = pushPath lf $ do
  source <- readInclude lf
  let cfg = defaultConfig { cfgSource = thing lf
                          , cfgPreProc = guessPreProc (thing lf)
                          }
  case parseProgramWith cfg source of

    Right prog -> do
      Program ds <-
        do path <- fromIncPath (thing lf)
           withIncPath path (noIncludeProgram prog)
      return ds

    Left err -> M (raise [IncludeParseError err])

-- | Read a file referenced by an include.
readInclude :: Located FilePath -> NoIncM Text
readInclude path = do
  readBytes   <- envFileReader <$> M ask
  file        <- fromIncPath (thing path)
  addDep file
  sourceBytes <- readBytes file `failsWith` handler
  sourceText  <- X.evaluate (T.decodeUtf8' sourceBytes) `failsWith` handler
  case sourceText of
    Left encodingErr -> M (raise [IncludeDecodeFailed path encodingErr])
    Right txt -> return txt
  where
  handler :: X.IOException -> NoIncM a
  handler _ = includeFailed path
