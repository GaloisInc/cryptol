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
-- Mintiner  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Expands PropGuards into a top-level definition for each case, and rewrites
-- the body of each case to be an appropriate call to the respectively generated
-- function.
module Cryptol.Parser.ExpandPropGuards where

import Data.Maybe(fromMaybe)
import Control.DeepSeq
import Cryptol.Parser.Position(emptyRange)
import Cryptol.Parser.AST
import Cryptol.Utils.PP
import Cryptol.Utils.Panic (panic)
import Data.Foldable (traverse_)
import Data.Text (pack)
import GHC.Generics (Generic)

-- | Monad
type ExpandPropGuardsM a = Either Error a

runExpandPropGuardsM :: ExpandPropGuardsM a -> Either Error a
runExpandPropGuardsM m = m

-- | Errors that can happen while expanding constraint guards.
data Error = NoSignature (Located PName)
             -- ^ A declaration using constraints guard lacks an explicit type
             -- signature, which is a requirement.
           | NestedConstraintGuard (Located PName)
             -- ^ Constraint guards appear somewhere other than the top level,
             -- which is not allowed.
  deriving (Show, Generic, NFData)

instance PP Error where
  ppPrec _ err = case err of
    NoSignature x ->
      hang
        (text "At" <+> pp (srcRange x) <.> colon)
        2
        (vcat [ text "Declaration" <+> backticks (pp (thing x)) <+>
                text "lacks a type signature."
              , text "Declarations using constraint guards require an" <+>
                text "explicit type signature."
              ])
    NestedConstraintGuard x ->
      hang
        (text "At" <+> pp (srcRange x) <.> colon)
        2
        (vcat [ text "Local declaration" <+> backticks (pp (thing x)) <+>
                text "may not use constraint guards."
              , text "Constraint guards may only appear at the top-level of" <+>
                text "a module."
              ])

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
    DBind bind ->
      do bs <- expandBind bind
         pure (map DBind bs)
    DLocated d rng ->
      do ds <- expandDecl d
         pure $ map (`DLocated` rng) ds
    _ ->
      pure [decl]

expandBind :: Bind PName -> ExpandPropGuardsM [Bind PName]
expandBind bind =
  case thing (bDef bind) of
    DImpl (DPropGuards guards) -> expand (DImpl . DPropGuards) guards
    DForeign cc (Just (DPropGuards guards)) -> expand (DForeign cc . Just . DPropGuards) guards
    _ ->
      do checkNestedGuardsInBind bind
         pure [bind]

  where
  expand def guards = do
    Forall params props t rng <-
      case bSignature bind of
        Just schema -> pure (thing schema)
        Nothing -> Left . NoSignature $ bName bind
    let goGuard ::
          PropGuardCase PName ->
          ExpandPropGuardsM (PropGuardCase PName, Bind PName)
        goGuard (PropGuardCase props' e) = do
          checkNestedGuardsInExpr e
          bName' <- newName (bName bind) (thing <$> props')
          -- call to generated function
          tParams <- case thing <$> bSignature bind of
            Just (Forall tps _ _ _) -> pure tps
            Nothing -> Left $ NoSignature (bName bind)
          typeInsts <-
            (\tp ->
               let loc = fromMaybe emptyRange (tpRange tp) in
               Right (PosInst (TUser (Located loc (tpName tp)) [])))
              `traverse` tParams
          let e' = foldl EApp (EAppT (EVar $ thing bName') typeInsts) (patternToExpr <$> bindParams bind)
          pure
            ( PropGuardCase props' e',
              bind
                { bName = bName',
                  -- include guarded props in signature
                  bSignature = Just Located 
                                  { srcRange = maybe (srcRange (bName bind)) srcRange (bSignature bind),
                                    thing = Forall params
                                        (props <> map thing props')
                                        t rng },
                  -- keeps same location at original bind
                  -- i.e. "on top of" original bind
                  bDef = (bDef bind) {thing = exprDef e}
                }
            )
    (guards', binds') <- unzip <$> mapM goGuard guards
    pure $
      bind {bDef = def guards' <$ bDef bind} :
      binds'

-- | Check for nested uses of constraint guards in an expression (e.g.,
-- in a local definition bound with @where@).
checkNestedGuardsInExpr :: Expr PName -> ExpandPropGuardsM ()
checkNestedGuardsInExpr expr =
  case expr of
    EVar {} ->
      pure ()
    ELit {} ->
      pure ()
    EGenerate e ->
      checkNestedGuardsInExpr e
    ETuple es ->
      traverse_ checkNestedGuardsInExpr es
    ERecord r ->
      traverse_ (checkNestedGuardsInExpr . snd) r
    ESel e _ ->
      checkNestedGuardsInExpr e
    EUpd mbE upds ->
      do traverse_ checkNestedGuardsInExpr mbE
         traverse_ checkNestedGuardsInUpdField upds
    EList es ->
      traverse_ checkNestedGuardsInExpr es
    EFromTo {} ->
      pure ()
    EFromToBy {} ->
      pure ()
    EFromToDownBy {} ->
      pure ()
    EFromToLessThan {} ->
      pure ()
    EInfFrom _ mbE ->
      traverse_ checkNestedGuardsInExpr mbE
    EComp e mss ->
      do checkNestedGuardsInExpr e
         traverse_ (traverse_ checkNestedGuardsInMatch) mss
    EApp e1 e2 ->
      do checkNestedGuardsInExpr e1
         checkNestedGuardsInExpr e2
    EAppT e _ ->
      checkNestedGuardsInExpr e
    EIf e1 e2 e3 ->
      do checkNestedGuardsInExpr e1
         checkNestedGuardsInExpr e2
         checkNestedGuardsInExpr e3
    EWhere e ds ->
      do checkNestedGuardsInExpr e
         traverse_ checkNestedGuardsInDecl ds
    ETyped e _ ->
      checkNestedGuardsInExpr e
    ETypeVal _ ->
      pure ()
    EFun _ _ e ->
      checkNestedGuardsInExpr e
    ELocated e _ ->
      checkNestedGuardsInExpr e
    ESplit e ->
      checkNestedGuardsInExpr e
    EParens e ->
      checkNestedGuardsInExpr e
    EInfix e1 _ _ e2 ->
      do checkNestedGuardsInExpr e1
         checkNestedGuardsInExpr e2
    EPrefix _ e ->
      checkNestedGuardsInExpr e
    ECase e ca ->
      do checkNestedGuardsInExpr e
         traverse_ checkNestedGuardsInCaseAlt ca
  where
    checkNestedGuardsInUpdField :: UpdField PName -> ExpandPropGuardsM ()
    checkNestedGuardsInUpdField (UpdField _ _ e) =
      checkNestedGuardsInExpr e

    checkNestedGuardsInMatch :: Match PName -> ExpandPropGuardsM ()
    checkNestedGuardsInMatch match =
      case match of
        Match _ e ->
          checkNestedGuardsInExpr e
        MatchLet b ->
          checkNestedGuardsInBind b

    checkNestedGuardsInCaseAlt :: CaseAlt PName -> ExpandPropGuardsM ()
    checkNestedGuardsInCaseAlt (CaseAlt _ e) =
      checkNestedGuardsInExpr e

-- | Check for nested uses of constraint guards in a local declaration.
checkNestedGuardsInDecl :: Decl PName -> ExpandPropGuardsM ()
checkNestedGuardsInDecl decl =
  case decl of
    DSignature {} -> pure ()
    DPatBind _ e  -> checkNestedGuardsInExpr e
    DBind b       -> checkNestedGuardsInBind b
    DRec bs       -> traverse_ checkNestedGuardsInBind bs
    DFixity {}    -> pure ()
    DPragma {}    -> pure ()
    DType {}      -> pure ()
    DProp {}      -> pure ()
    DLocated d _  -> checkNestedGuardsInDecl d

-- | Check for nested uses of constraint guards in a local bind.
checkNestedGuardsInBind :: Bind PName -> ExpandPropGuardsM ()
checkNestedGuardsInBind bind =
  case thing (bDef bind) of
    DPrim         -> pure ()
    DImpl bi      -> checkNestedGuardsInBindImpl bi
    DForeign _ mbBi -> traverse_ checkNestedGuardsInBindImpl mbBi
  where
    nestedConstraintGuards :: ExpandPropGuardsM ()
    nestedConstraintGuards = Left . NestedConstraintGuard $ bName bind

    checkNestedGuardsInBindImpl :: BindImpl PName -> ExpandPropGuardsM ()
    checkNestedGuardsInBindImpl bi =
      case bi of
        DPropGuards _ ->
          nestedConstraintGuards
        DExpr e ->
          checkNestedGuardsInExpr e

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
    UnQual' ident ns ->
      let txt = identText ident
          txt' = pack $ show $ pp props
       in UnQual' (mkIdent $ txt <> txt') ns <$ locName
    NewName _ _ ->
      panic "mkName"
        [ "During expanding prop guards"
        , "tried to make new name from NewName case of PName"
        ]
