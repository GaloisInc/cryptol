{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

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

-- | Error
data Error = NoSignature (Located PName)
  deriving (Show, Generic, NFData)

instance PP Error where
  ppPrec _ err = case err of
    NoSignature x ->
      text "At" <+> pp (srcRange x) <.> colon
        <+> text "Declarations using constraint guards require an explicit type signature."

expandPropGuards :: ModuleG mname PName -> ExpandPropGuardsM (ModuleG mname PName)
expandPropGuards m =
  do def <- expandModuleDef (mDef m)
     pure m { mDef = def }

expandModuleDef :: ModuleDefinition PName -> ExpandPropGuardsM (ModuleDefinition PName)
expandModuleDef m =
  case m of
    NormalModule ds    -> NormalModule . concat <$> mapM expandTopDecl ds
    FunctorInstance {} -> pure m
    InterfaceModule {} -> pure m

expandTopDecl :: TopDecl PName -> ExpandPropGuardsM [TopDecl PName]
expandTopDecl topDecl =
  case topDecl of
    Decl topLevelDecl ->
      do ds <- expandDecl (tlValue topLevelDecl)
         pure [ Decl topLevelDecl { tlValue = d } | d <- ds ]

    DModule tl | NestedModule m <- tlValue tl ->
      do m1 <- expandPropGuards m
         pure [DModule tl { tlValue = NestedModule m1 }]

    _ -> pure [topDecl]

expandDecl :: Decl PName -> ExpandPropGuardsM [Decl PName]
expandDecl decl =
  case decl of
    DBind bind -> do bs <- expandBind bind
                     pure (map DBind bs)
    _          -> pure [decl]

expandBind :: Bind PName -> ExpandPropGuardsM [Bind PName]
expandBind bind =
  case thing (bDef bind) of
    DPropGuards guards -> do
      Forall params props t rng <-
        case bSignature bind of
          Just schema -> pure schema
          Nothing -> Left . NoSignature $ bName bind
      let goGuard ::
            PropGuardCase PName ->
            ExpandPropGuardsM (PropGuardCase PName, Bind PName)
          goGuard (PropGuardCase props' e) = do
            bName' <- newName (bName bind) (thing <$> props')
            -- call to generated function
            tParams <- case bSignature bind of
              Just (Forall tps _ _ _) -> pure tps
              Nothing -> Left $ NoSignature (bName bind)
            typeInsts <-
              (\(TParam n _ _) -> Right . PosInst $ TUser n [])
                `traverse` tParams
            let e' = foldl EApp (EAppT (EVar $ thing bName') typeInsts) (patternToExpr <$> bParams bind)
            pure
              ( PropGuardCase props' e',
                bind
                  { bName = bName',
                    -- include guarded props in signature
                    bSignature = Just (Forall params
                                         (props <> map thing props')
                                         t rng),
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
patternToExpr _ =
  panic "patternToExpr"
    ["Unimplemented: patternToExpr of anything other than PVar"]

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
    NewName _ _ ->
      panic "mkName"
        [ "During expanding prop guards"
        , "tried to make new name from NewName case of PName"
        ]
