{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
module CryptolServer.Call
  ( Expression(..)
  , Encoding(..)
  , LetBinding(..)
  , call
  , CallParams(..)
  ) where

import Control.Lens hiding ((.=))
import Control.Monad (unless)
import Control.Monad.IO.Class
import Data.Aeson as JSON hiding (Encoding, Value, decode)
import qualified Data.Aeson as JSON
import qualified Data.Set as Set
import Data.Text (Text)

import Cryptol.IR.FreeVars (freeVars, tyDeps, valDeps)
import Cryptol.ModuleSystem (checkExpr, evalExpr, getPrimMap, meLoadedModules)
import Cryptol.ModuleSystem.Env (isLoadedParamMod, meSolverConfig)
import Cryptol.ModuleSystem.Name (NameInfo(Declared), nameInfo)
import Cryptol.Parser.AST (Expr(..), PName(..))
import Cryptol.TypeCheck.AST (sType)
import Cryptol.TypeCheck.Solve (defaultReplExpr)
import Cryptol.TypeCheck.Subst (apSubst, listParamSubst)
import Cryptol.Utils.Ident
import Cryptol.Utils.PP (pretty)
import qualified Cryptol.TypeCheck.Solver.SMT as SMT

import Argo

import CryptolServer
import CryptolServer.Exceptions
import CryptolServer.Data.Expression
import CryptolServer.Data.Type

call :: CallParams -> Method ServerState JSON.Value
call (CallParams fun rawArgs) =
  do args <- traverse getExpr rawArgs
     let appExpr = mkEApp (EVar (UnQual (mkIdent fun))) args
     (_expr, ty, schema) <- runModuleCmd (checkExpr appExpr)
     evalAllowed ty
     evalAllowed schema
     me <- view moduleEnv <$> getState
     let cfg = meSolverConfig me
     perhapsDef <- liftIO $ SMT.withSolver cfg (\s -> defaultReplExpr s ty schema)
     case perhapsDef of
       Nothing -> error "TODO" -- TODO: What should happen here?
       Just (tys, checked) ->
         do noDefaults tys
            let su = listParamSubst tys
            let theType = apSubst su (sType schema)
            res <- runModuleCmd (evalExpr checked)
            prims <- runModuleCmd getPrimMap
            val <- observe $ readBack prims theType res
            return (JSON.object [ "value" .= val
                                , "type string" .= pretty theType
                                , "type" .= JSONType mempty theType
                                ])
  where
    noDefaults [] = return ()
    noDefaults xs@(_:_) =
      raise (unwantedDefaults xs)

    evalAllowed x =
      do me <- view moduleEnv <$> getState
         let ds      = freeVars x
             badVals = foldr badName Set.empty (valDeps ds)
             bad     = foldr badName badVals (tyDeps ds)
             badName nm bs =
               case nameInfo nm of
                 Declared m _
                   | isLoadedParamMod m (meLoadedModules me) -> Set.insert nm bs
                 _ -> bs
         unless (Set.null bad) $
           raise (evalInParamMod (Set.toList bad))


data CallParams
  = CallParams Text [Expression]

instance FromJSON CallParams where
  parseJSON =
    withObject "params for \"call\"" $
    \o -> CallParams <$> o .: "function" <*> o .: "arguments"
