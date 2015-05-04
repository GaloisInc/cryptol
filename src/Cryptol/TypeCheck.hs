-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

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

import qualified Cryptol.Parser.AST as P
import           Cryptol.Parser.Position(Range)
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
import           Cryptol.Prims.Types(typeOf)
import           Cryptol.TypeCheck.Infer (inferModule, inferBinds, inferDs)
import           Cryptol.TypeCheck.InferTypes(Error(..),Warning(..),VarType(..), SolverConfig(..))
import           Cryptol.TypeCheck.Solve(simplifyAllConstraints)
import           Cryptol.Utils.PP
import           Cryptol.Utils.Panic(panic)

tcModule :: P.Module -> InferInput -> IO (InferOutput Module)
tcModule m inp = runInferM inp
               $ do x <- inferModule m
                    simplifyAllConstraints
                    return x

tcExpr :: P.Expr -> InferInput -> IO (InferOutput (Expr,Schema))
tcExpr e0 inp = runInferM inp
                $ do x <- go e0
                     simplifyAllConstraints
                     return x

  where
  go expr =
    case expr of
      P.ELocated e _ -> go e
      P.ECon ec -> return (ECon ec, typeOf ec)
      P.EVar x  ->
        do res <- lookupVar x
           case res of
             ExtVar s    -> return (EVar x, s)
             CurSCC e' t -> panic "Cryptol.TypeCheck.tcExpr"
                             [ "CurSCC outside binder checkig:"
                             , show e'
                             , show t
                             ]
      _ -> do res <- inferBinds True False
                [ P.Bind
                    { P.bName      = P.Located (inpRange inp)
                                   $ mkUnqual (P.Name "(expression)")
                    , P.bParams    = []
                    , P.bDef       = expr
                    , P.bPragmas   = []
                    , P.bSignature = Nothing
                    , P.bMono      = False
                    } ]

              case res of
                [d] -> return (dDefinition d, dSignature d)
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
ppError (r,w) = text "[error] at" <+> pp r <> colon $$ nest 2 (pp w)


