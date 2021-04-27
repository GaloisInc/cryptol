{-# Language OverloadedStrings #-}
module Cryptol.TypeCheck.CheckModuleInstance (checkModuleInstance) where

import           Data.Map ( Map )
import qualified Data.Map as Map
import           Control.Monad(unless)

import Cryptol.Parser.Position(Located(..))
import qualified Cryptol.Parser.AST as P
import Cryptol.ModuleSystem.Name (nameIdent, nameLoc)
import Cryptol.ModuleSystem.InstantiateModule(instantiateModule)
import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Monad
import Cryptol.TypeCheck.Infer
import Cryptol.TypeCheck.Subst
import Cryptol.TypeCheck.Error
import Cryptol.Utils.Panic


-- | Check that the instance provides what the functor needs.
checkModuleInstance :: Module {- ^ type-checked functor -} ->
                       Module {- ^ type-checked instance -} ->
                       InferM (Name->Name,Module)
                       -- ^ Renaming,Instantiated module
checkModuleInstance func inst
  | not (null (mSubModules func) && null (mSubModules inst)) =
    do recordError $ TemporaryError
         "Cannot combine nested modules with old-style parameterized modules"
       pure (id,func) -- doesn't matter?
  | otherwise =
  do tMap <- checkTyParams func inst
     vMap <- checkValParams func tMap inst
     (ren, ctrs, m) <- instantiateModule func (mName inst) tMap vMap
     let toG p = Goal { goal = thing p
                      , goalRange = srcRange p
                      , goalSource = CtModuleInstance (mName inst)
                      }
     addGoals (map toG ctrs)
     return ( ren
            , Module { mName = mName m
                   , mExports = mExports m
                   , mImports = mImports inst ++ mImports m
                                -- Note that this is just here to record
                                -- the full dependencies, the actual imports
                                -- might be ambiguous, but that shouldn't
                                -- matters as names have been already resolved
                   , mTySyns      = Map.union (mTySyns inst) (mTySyns m)
                   , mNewtypes    = Map.union (mNewtypes inst) (mNewtypes m)
                   , mPrimTypes   = Map.union (mPrimTypes inst) (mPrimTypes m)
                   , mParamTypes       = mParamTypes inst
                   , mParamConstraints = mParamConstraints inst
                   , mParamFuns        = mParamFuns inst
                   , mDecls            = mDecls inst ++ mDecls m

                   , mSubModules = mempty
                   , mFunctors   = mempty
                   , mSignatures = mempty
                   }
              )

-- | Check that the type parameters of the functors all have appropriate
-- definitions.
checkTyParams :: Module -> Module -> InferM (Map TParam Type)
checkTyParams func inst =
  Map.fromList <$> mapM checkTParamDefined (Map.elems (mParamTypes func))

  where
  -- Maps to lookup things by identifier (i.e., lexical name)
  -- rather than using the name unique.
  identMap f m = Map.fromList [ (f x, ts) | (x,ts) <- Map.toList m ]
  tySyns       = identMap nameIdent (mTySyns inst)
  newTys       = identMap nameIdent (mNewtypes inst)
  tParams      = Map.fromList [ (tpId x, x) | x0 <- Map.elems (mParamTypes inst)
                                            , let x = mtpParam x0 ]

  tpName' x    = case tpName x of
                   Just n -> n
                   Nothing -> panic "inferModuleInstance.tpId" ["Missing name"]

  tpId         = nameIdent . tpName'

  -- Find a definition for a given type parameter
  checkTParamDefined tp0 =
    let tp = mtpParam tp0
        x = tpId tp
    in case Map.lookup x tySyns of
         Just ts -> checkTySynDef tp ts
         Nothing ->
           case Map.lookup x newTys of
             Just nt -> checkNewTyDef tp nt
             Nothing ->
               case Map.lookup x tParams of
                 Just tp1 -> checkTP tp tp1
                 Nothing ->
                   do let x' = Located { thing = x,
                                         srcRange = nameLoc (tpName' tp) }
                      recordError (MissingModTParam x')
                      return (tp, TVar (TVBound tp)) -- hm, maybe just stop!

  -- Check that a type parameter defined as a type synonym is OK
  checkTySynDef tp ts =
    do let k1 = kindOf tp
           k2 = kindOf ts
       unless (k1 == k2) (recordError (KindMismatch Nothing k1 k2))

       let nm  = tsName ts
           src = CtPartialTypeFun nm
       mapM_ (newGoal src) (tsConstraints ts)

       return (tp, TUser nm [] (tsDef ts))

  -- Check that a type parameter defined a newtype is OK
  -- This one is a bit weird: since the newtype is deinfed in the
  -- instantiation, it will not be exported, and so won't be usable
  -- in type signatures, directly.   This could be worked around
  -- if the parametrized module explictly exported a parameter via
  -- a type synonym like this: `type T = p`, where `p` is one of
  -- the parametersm and the declartion for `T` is public.
  checkNewTyDef tp nt =
    do let k1 = kindOf tp
           k2 = kindOf nt
       unless (k1 == k2) (recordError (KindMismatch Nothing k1 k2))

       let nm = ntName nt
           src = CtPartialTypeFun nm
       mapM_ (newGoal src) (ntConstraints nt)

       return (tp, TNewtype nt [])

  -- Check that a type parameter defined as another type parameter is OK
  checkTP tp tp1 =
    do let k1 = kindOf tp
           k2 = kindOf tp1
       unless (k1 == k2) (recordError (KindMismatch Nothing k1 k2))

       return (tp, TVar (TVBound tp1))




checkValParams :: Module          {- ^ Parameterized module -} ->
                  Map TParam Type {- ^ Type instantiations -} ->
                  Module          {- ^ Instantiation module -} ->
                  InferM (Map Name Expr)
                  -- ^ Definitions for the parameters
checkValParams func tMap inst =
  Map.fromList <$> mapM checkParam (Map.elems (mParamFuns func))
  where
  valMap = Map.fromList (defByParam ++ defByDef)

  defByDef = [ (nameIdent (dName d), (dName d, dSignature d))
                          | dg <- mDecls inst, d <- groupDecls dg ]

  defByParam = [ (nameIdent x, (x, mvpType s)) |
                                    (x,s) <- Map.toList (mParamFuns inst) ]

  su = listParamSubst (Map.toList tMap)

  checkParam pr =
    let x = mvpName pr
        sP = mvpType pr
    in
    case Map.lookup (nameIdent x) valMap of
      Just (n,sD) -> do e <- makeValParamDef n sD (apSubst su sP)
                        return (x,e)
      Nothing -> do recordError (MissingModVParam
                                 Located { thing = nameIdent x
                                         , srcRange = nameLoc x })
                    return (x, panic "checkValParams" ["Should not use this"])



-- | Given a parameter definition, compute an appropriate instantiation
-- that will match the actual schema for the parameter.
makeValParamDef :: Name   {- ^ Definition of parameter -} ->
                   Schema {- ^ Schema for parameter definition -} ->
                   Schema {- ^ Schema for parameter -} ->
                   InferM Expr {- ^ Expression to use for param definition -}

makeValParamDef x sDef pDef =
  withVar x sDef $ do ~(DExpr e) <- dDefinition <$> checkSigB bnd (pDef,[])
                      return e
  where
  bnd = P.Bind { P.bName      = loc x
               , P.bParams    = []
               , P.bDef       = loc (P.DExpr (P.EVar x))

                -- unused
               , P.bSignature = Nothing
               , P.bInfix     = False
               , P.bFixity    = Nothing
               , P.bPragmas   = []
               , P.bMono      = False
               , P.bDoc       = Nothing
               , P.bExport    = Public
               }
  loc a = P.Located { P.srcRange = nameLoc x, P.thing = a }



