{-# Language BlockArguments #-}
{-# Language Trustworthy #-}
module Cryptol.TypeCheck.Module where

import Data.Map(Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad(unless,forM_)

import Cryptol.Utils.PP
import Text.Show.Pretty(ppShow)

import Cryptol.Utils.Panic(xxxTODO)
import Cryptol.Utils.Ident(Ident,Namespace(..))
import Cryptol.Parser.Position (Range,Located(..), thing)
import qualified Cryptol.Parser.AST as P
import Cryptol.ModuleSystem.Name(nameIdent)
import Cryptol.ModuleSystem.Exports(exportedDecls)
import Cryptol.ModuleSystem.Interface
          ( IfaceG(..), IfaceModParam(..), IfaceDecls(..), IfaceNames(..)
          , IfaceParams(..)
          , filterIfaceDecls
          )
import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Error
import Cryptol.TypeCheck.Monad

import Debug.Trace

doFunctorInst ::
  Located (P.ImpName Name)    {- ^ Functor being instantiation -} ->
  P.ModuleInstanceArgs Name   {- ^ Instance arguments -} ->
  Map Name Name               {- ^ Basic instantiation -} ->
  InferM ()
doFunctorInst f as inst =
  do mf    <- lookupFunctor (thing f)
     argIs <- checkArity (srcRange f) mf as
     ren   <- mapM_ checkArg argIs

     pure () -- xxxTODO "doFunctorInst"


-- | Validate a functor application, just checking the argument names
checkArity ::
  Range             {- ^ Location for reporting errors -} ->
  ModuleG ()        {- ^ The functor being instantiated -} ->
  P.ModuleInstanceArgs Name {- ^ The arguments -} ->
  InferM [ (Range, IfaceModParam, IfaceG ()) ]
  {- ^ Associates functor parameters with the interfaces of the
       instantiating modules -}
checkArity r mf args =
  case args of

    P.DefaultInstArg arg ->
      let i = Located { srcRange = srcRange arg
                      , thing    = head (Map.keys ps0)
                      }
      in checkArgs [] ps0 [ P.ModuleInstanceArg i arg ]

    P.NamedInstArgs as -> checkArgs [] ps0 as

  where
  ps0 = mParams mf

  checkArgs done ps as =
    case as of

      [] -> do forM_ (Map.keys ps) \p ->
                 recordErrorLoc (Just r) (FunctorInstanceMissingArgument p)
               pure done

      P.ModuleInstanceArg ll lm : more ->
        case Map.lookup (thing ll) ps of
          Just i ->
            do mo <- lookupModule (thing lm)
               checkArgs ((srcRange lm, i, mo) : done)
                         (Map.delete (thing ll) ps) more
          Nothing ->
            do recordErrorLoc (Just (srcRange ll))
                              (FunctorInstanceBadArgument (thing ll))
               checkArgs done ps more


checkArg :: (Range, IfaceModParam, IfaceG ()) -> InferM (Map Name Name)
checkArg (r,expect,actual) =
  do traceM (ppShow actual)
     tys <- mapM (checkParamType r tyMap) (Map.toList (ifParamTypes params))
     pure (Map.fromList tys)

  where
  params = ifmpParameters expect

  localNames = ifsDefines (ifNames actual)
  isLocal x  = x `Set.member` localNames
  decls      = filterIfaceDecls isLocal (ifPublic actual)

  -- Available type names
  tyMap      = Map.unions [ nameMapToIdentMap' kindOf (ifTySyns decls)
                          , nameMapToIdentMap' kindOf (ifNewtypes decls)
                          , nameMapToIdentMap' kindOf (ifAbstractTypes decls)
                          ]

  -- Available value names
  valMap     = nameMapToIdentMap (ifDecls decls)

checkParamType ::
  Range                 {- ^ Location for error reporting -} ->
  Map Ident (Name,Kind) {- ^ Actual types -} ->
  (Name,ModTParam)      {- ^ Type parameter -} ->
  InferM (Name,Name)    {- ^ Mapping from parameter name to actual name -}
checkParamType r tyMap (name,mp) =
  let i       = nameIdent name
      expectK = mtpKind mp
  in
  case Map.lookup i tyMap of
    Nothing ->
      do recordErrorLoc (Just r) (FunctorInstanceMissingName NSType i)
         pure (name,name)
    Just (actualName,actualK) ->
      do unless (expectK == actualK)
           (recordErrorLoc (Just r)
                           (KindMismatch (Just (TVFromModParam name))
                                                  expectK actualK))
         pure (name, actualName)

nameMapToIdentMap :: Map Name a -> Map Ident Name
nameMapToIdentMap m = Map.fromList [ (nameIdent n, n) | n <- Map.keys m ]

nameMapToIdentMap' :: (a -> b) -> Map Name a -> Map Ident (Name,b)
nameMapToIdentMap' f m =
  Map.fromList [ (nameIdent n, (n,f v)) | (n,v) <- Map.toList m ]


