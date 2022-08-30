{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

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
module Cryptol.Parser.ExpandPropGuards where

-- import Cryptol.Parser.Position (Range(..), emptyRange, start, at)
-- import Cryptol.Parser.Names (namesP)

-- import Cryptol.Utils.Ident (mkIdent)

-- import Cryptol.Utils.RecordMap

import Control.DeepSeq
import Cryptol.Parser.AST
import Cryptol.Utils.PP
import Cryptol.Utils.Panic (panic)
import Data.Text (pack)
import GHC.Generics (Generic)

-- | Monad
type ExpandPropGuardsM a = Either Error a

runExpandPropGuardsM :: ExpandPropGuardsM a -> Either Error a
runExpandPropGuardsM m = m

-- | Class
class ExpandPropGuards a where
  expandPropGuards :: a -> ExpandPropGuardsM a

-- | Error
data Error = NoSignature (Located PName)
  deriving (Show, Generic, NFData)

instance PP Error where
  ppPrec _ err = case err of
    NoSignature x ->
      text "At" <+> pp (srcRange x) <.> colon
        <+> text "Declarations using constraint guards currently require an explicit type signature."

-- | Instances
instance ExpandPropGuards (Program PName) where
  expandPropGuards (Program decls) = Program <$> expandPropGuards decls

instance ExpandPropGuards (Module PName) where
  expandPropGuards m = do
    mDecls' <- expandPropGuards (mDecls m)
    pure m {mDecls = mDecls'}

instance ExpandPropGuards [TopDecl PName] where
  expandPropGuards topDecls = concat <$> traverse goTopDecl topDecls
    where
      goTopDecl :: TopDecl PName -> ExpandPropGuardsM [TopDecl PName]
      goTopDecl (Decl topLevelDecl) = fmap mu <$> expandPropGuards [tlValue topLevelDecl]
        where
          mu decl = Decl $ topLevelDecl {tlValue = decl}
      goTopDecl topDecl = pure [topDecl]

instance ExpandPropGuards [Decl PName] where
  expandPropGuards decls = concat <$> traverse goDBind decls
    where
      goDBind (DBind bind) = fmap DBind <$> expandPropGuards [bind]
      goDBind decl = pure [decl]

instance ExpandPropGuards [Bind PName] where
  expandPropGuards binds = concat <$> traverse goBind binds
    where
      goBind :: Bind PName -> Either Error [Bind PName]
      goBind bind = case thing $ bDef bind of
        DPropGuards guards -> do
          Forall params props t rng <-
            case bSignature bind of
              Just schema -> pure schema
              Nothing -> Left . NoSignature $ bName bind
          let goGuard :: ([Prop PName], Expr PName) -> ExpandPropGuardsM (([Prop PName], Expr PName), Bind PName)
              goGuard (props', e) = do
                bName' <- newName (bName bind) props'
                -- call to generated function
                let e' = foldr EApp (EVar $ thing bName') (patternToExpr <$> bParams bind)
                pure
                  ( (props', e'),
                    bind
                      { bName = bName',
                        -- include guarded props in signature
                        bSignature = Just $ Forall params (props <> props') t rng,
                        -- keeps same location at original bind
                        -- i.e. "on top of" original bind
                        bDef = (bDef bind) {thing = DExpr e}
                      }
                  )
          (guards', binds') <- unzip <$> mapM goGuard guards
          pure $
            bind {bDef = DPropGuards guards' <$ bDef bind} :
            binds'
        _ -> pure [bind]

patternToExpr :: Pattern PName -> Expr PName
patternToExpr (PVar locName) = EVar (thing locName)
patternToExpr _ = panic "patternToExpr" ["Unimplemented: patternToExpr of anything other than PVar"]

newName :: Located PName -> [Prop PName] -> ExpandPropGuardsM (Located PName)
newName locName props =
  pure case thing locName of
    Qual modName ident ->
      let txt = identText ident
          txt' = pack $ show $ pp props
       in Qual modName (mkIdent $ txt <> txt') <$ locName
    UnQual ident ->
      let txt = identText ident
          txt' = pack $ show $ pp props
       in UnQual (mkIdent $ txt <> txt') <$ locName
    NewName _ _ -> panic "mkName" ["During expanding prop guards, tried to make new name from NewName case of PName"]
