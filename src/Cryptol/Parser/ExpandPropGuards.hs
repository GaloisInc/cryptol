-- |
-- Module      :  Cryptol.Parser.PropGuards
-- Copyright   :  (c) 2022 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Expands PropGuards into a top-level definition for each case, and rewrites
-- the body of each case to be an appropriate call to the respectively generated
-- function.
--

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Cryptol.Parser.ExpandPropGuards where

import Cryptol.Parser.AST
import Cryptol.Parser.Position (Range(..), emptyRange, start, at)
import Cryptol.Parser.Names (namesP)
import Cryptol.Utils.PP
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.RecordMap

import           MonadLib hiding (mapM)
import           Data.Maybe (maybeToList)
import qualified Data.Map as Map
import           Data.Text (Text)

import GHC.Generics (Generic)
import Control.DeepSeq

-- | Monad

type ExpandPropGuardsM a = Either Error a

runExpandPropGuardsM :: ExpandPropGuardsM a -> Either Error a
runExpandPropGuardsM m = m

-- | Class
class ExpandPropGuards a where
  expandPropGuards :: a -> ExpandPropGuardsM a

data Error = NoSignature (Located PName)
  deriving (Show,Generic, NFData)

-- | Instances

instance ExpandPropGuards (Program PName) where
  expandPropGuards (Program decls) = Program <$> expandPropGuards decls

instance ExpandPropGuards [TopDecl PName] where
  expandPropGuards topDecls = concat <$> traverse f topDecls 
    where 
      f :: TopDecl PName -> ExpandPropGuardsM [TopDecl PName]
      f (Decl topLevelDecl) = fmap lift <$> expandPropGuards [tlValue topLevelDecl]
        where lift decl = Decl $ topLevelDecl { tlValue = decl }
      f topDecl = pure [topDecl]

instance ExpandPropGuards [Decl PName] where 
  expandPropGuards decls = concat <$> traverse f decls 
    where 
      f (DBind bind) = fmap DBind <$> expandPropGuards [bind]
      f decl = pure [decl]

instance ExpandPropGuards [Bind PName] where
  expandPropGuards binds = concat <$> traverse f binds
    where 
      f bind = case thing $ bDef bind of 
        DPropGuards guards -> do
          Forall params props t rng <-
            case bSignature bind of
              Just schema -> pure schema 
              Nothing -> Left . NoSignature $ bName bind
          let
            g :: ([Prop PName], Expr PName) -> ExpandPropGuardsM (Bind PName)
            g (props', e) = pure bind
              { -- include guarded props in signature
                bSignature = Just $ Forall params (props <> props') t rng
                -- keeps same location at original bind 
                -- i.e. "on top of" original bind
              , bDef = (bDef bind) {thing = DExpr e}
              }
          mapM g guards
        _ -> pure [bind]
