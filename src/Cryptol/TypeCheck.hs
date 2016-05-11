-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
{-# LANGUAGE PatternGuards #-}

module Cryptol.TypeCheck
  ( tcModule
  , tcExpr
  , tcDecls
  , InferInput(..)
  , InferOutput(..)
  , SolverConfig(..)
  , NameSeeds
  , nameSeeds
  , Error(..)
  , Warning(..)
  , ppWarning
  , ppError
  ) where

import           Cryptol.ModuleSystem.Name (liftSupply,mkDeclared)
import qualified Cryptol.Parser.AST as P
import           Cryptol.Parser.Position(Range,emptyRange)
import           Cryptol.TypeCheck.AST
import           Cryptol.TypeCheck.Depends (FromDecl)
import           Cryptol.TypeCheck.Monad
                   ( runInferM
                   , InferInput(..)
                   , InferOutput(..)
                   , NameSeeds
                   , nameSeeds
                   , lookupVar
                   )
import           Cryptol.TypeCheck.Infer (inferModule, inferBinds, inferDs)
import           Cryptol.TypeCheck.InferTypes(Error(..),Warning(..),VarType(..), SolverConfig(..))
import           Cryptol.TypeCheck.Solve(simplifyAllConstraints)
import           Cryptol.Utils.Ident (packModName,packIdent)
import           Cryptol.Utils.PP
import           Cryptol.Utils.Panic(panic)
import           Cryptol.Utils.Color (errorAtMsg)

tcModule :: P.Module Name -> InferInput -> IO (InferOutput Module)
tcModule m inp = runInferM inp
               $ do x <- inferModule m
                    simplifyAllConstraints
                    return x

tcExpr :: P.Expr Name -> InferInput -> IO (InferOutput (Expr,Schema))
tcExpr e0 inp = runInferM inp
                $ do x <- go emptyRange e0
                     simplifyAllConstraints
                     return x

  where
  go loc expr =
    case expr of
      P.ELocated e loc' -> go loc' e
      P.EVar x  ->
        do res <- lookupVar x
           case res of
             ExtVar s    -> return (EVar x, s)
             CurSCC e' t -> panic "Cryptol.TypeCheck.tcExpr"
                             [ "CurSCC outside binder checkig:"
                             , show e'
                             , show t
                             ]
      _ -> do fresh <- liftSupply (mkDeclared (packModName ["<expr>"]) (packIdent "(expression)") Nothing loc)
              res   <- inferBinds True False
                [ P.Bind
                    { P.bName      = P.Located { P.srcRange = loc, P.thing = fresh }
                    , P.bParams    = []
                    , P.bDef       = P.Located (inpRange inp) (P.DExpr expr)
                    , P.bPragmas   = []
                    , P.bSignature = Nothing
                    , P.bMono      = False
                    , P.bInfix     = False
                    , P.bFixity    = Nothing
                    , P.bDoc       = Nothing
                    } ]

              case res of
                [d] | DExpr e <- dDefinition d -> return (e, dSignature d)
                    | otherwise                ->
                       panic "Cryptol.TypeCheck.tcExpr"
                          [ "Expected an expression in definition"
                          , show d ]

                _   -> panic "Cryptol.TypeCheck.tcExpr"
                          ( "Multiple declarations when check expression:"
                          : map show res
                          )

tcDecls :: FromDecl d => [d] -> InferInput -> IO (InferOutput [DeclGroup])
tcDecls ds inp = runInferM inp $ inferDs ds $ \dgs -> do
                   simplifyAllConstraints
                   return dgs

ppWarning :: (Range,Warning) -> Doc
ppWarning (r,w) = text "[warning] at" <+> pp r <> colon $$ nest 2 (pp w)

ppError :: (Range,Error) -> Doc
ppError (r,w) = text errorAtMsg <+> pp r <> colon $$ nest 2 (pp w)


