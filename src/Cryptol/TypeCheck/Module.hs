{-# Language BlockArguments, ImplicitParams #-}
module Cryptol.TypeCheck.Module (doFunctorInst) where

import Data.List(partition)
import Data.Text(Text)
import Data.Map(Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad(unless,forM_)


import Cryptol.Utils.Panic(panic)
import Cryptol.Utils.Ident(Ident,Namespace(..),isInfixIdent)
import Cryptol.Parser.Position (Range,Located(..), thing)
import qualified Cryptol.Parser.AST as P
import Cryptol.ModuleSystem.Name(nameIdent)
import Cryptol.ModuleSystem.Interface
          ( IfaceG(..), IfaceDecls(..), IfaceNames(..), IfaceDecl(..)
          , filterIfaceDecls
          )
import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Error
import Cryptol.TypeCheck.Subst(Subst,listParamSubst,apSubst,mergeDistinctSubst)
import Cryptol.TypeCheck.Solve(proveImplication)
import Cryptol.TypeCheck.Monad
import Cryptol.TypeCheck.Instantiate(instantiateWith)
import Cryptol.TypeCheck.ModuleInstance
import Cryptol.TypeCheck.ModuleBacktickInstance(MBQual, doBacktickInstance)

doFunctorInst ::
  Located (P.ImpName Name)    {- ^ Name for the new module -} ->
  Located (P.ImpName Name)    {- ^ Functor being instantiated -} ->
  P.ModuleInstanceArgs Name   {- ^ Instance arguments -} ->
  Map Name Name
  {- ^ Instantitation.  These is the renaming for the functor that arises from
       generativity (i.e., it is something that will make the names "fresh").
  -} ->
  Maybe Text                  {- ^ Documentation -} ->
  InferM (Maybe TCTopEntity)
doFunctorInst m f as inst doc =
  inRange (srcRange m)
  do mf    <- lookupFunctor (thing f)
     argIs <- checkArity (srcRange f) mf as
     m2 <- do as2 <- mapM checkArg argIs
              let (tySus,decls) = unzip [ (su,ds) | DefinedInst su ds <- as2 ]
              let ?tSu = mergeDistinctSubst tySus
                  ?vSu = inst
              let m1   = moduleInstance mf
                  m2   = m1 { mName             = m
                            , mDoc              = Nothing
                            , mParamTypes       = mempty
                            , mParamFuns        = mempty
                            , mParamConstraints = mempty
                            , mParams           = mempty
                            , mDecls = map NonRecursive (concat decls) ++
                                      mDecls m1
                            }
              let (tps,tcs,vps) =
                      unzip3 [ (xs,cs,fs) | ParamInst xs cs fs <- as2 ]
                  tpSet  = Set.unions tps
                  tpSet' = Set.map snd (Set.unions tps)
                  emit p = Set.null (freeParams (thing p)
                                                `Set.intersection` tpSet')

                  (emitPs,delayPs) = partition emit (mParamConstraints m1)

              forM_ emitPs \lp ->
                newGoals (CtModuleInstance (srcRange lp)) [thing lp]

              doBacktickInstance tpSet
                                 (map thing delayPs ++ concat tcs)
                                 (Map.unions vps)
                                 m2

     case thing m of
       P.ImpTop mn    -> newModuleScope mn (mExports m2)
       P.ImpNested mn -> newSubmoduleScope mn doc (mExports m2)

     mapM_ addTySyn     (Map.elems (mTySyns m2))
     mapM_ addNewtype   (Map.elems (mNewtypes m2))
     mapM_ addPrimType  (Map.elems (mPrimTypes m2))
     addSignatures      (mSignatures m2)
     addSubmodules      (mSubmodules m2)
     addFunctors        (mFunctors m2)
     mapM_ addDecls     (mDecls m2)

     case thing m of
       P.ImpTop {}    -> Just <$> endModule
       P.ImpNested {} -> endSubmodule >> pure Nothing


data ActualArg =
    UseParameter ModParam     -- ^ Instantiate using this parameter
  | UseModule (IfaceG ())     -- ^ Instantiate using this module
  | AddDeclParams             -- ^ Instantiate by adding parameters




{- | Validate a functor application, just checking the argument names.
The result associates a module parameter with the concrete way it should
be instantiated, which could be:

  * `Left` instanciate using another parameter that is in scope
  * `Right` instanciate using a module, with the given interface
-}
checkArity ::
  Range             {- ^ Location for reporting errors -} ->
  ModuleG ()        {- ^ The functor being instantiated -} ->
  P.ModuleInstanceArgs Name {- ^ The arguments -} ->
  InferM [(Range, ModParam, ActualArg)]
  {- ^ Associates functor parameters with the interfaces of the
       instantiating modules -}
checkArity r mf args =
  case args of

    P.DefaultInstArg arg ->
      let i = Located { srcRange = srcRange arg
                      , thing    = head (Map.keys ps0)
                      }
      in checkArgs [] ps0 [ P.ModuleInstanceNamedArg i arg ]

    P.NamedInstArgs as -> checkArgs [] ps0 as

    P.DefaultInstAnonArg {} -> panic "checkArity" [ "DefaultInstAnonArg" ]
  where
  ps0 = mParams mf

  checkArgs done ps as =
    case as of

      [] -> do forM_ (Map.keys ps) \p ->
                 recordErrorLoc (Just r) (FunctorInstanceMissingArgument p)
               pure done

      P.ModuleInstanceNamedArg ll lm : more ->
        case Map.lookup (thing ll) ps of
          Just i ->
            do arg <- case thing lm of
                        P.ModuleArg m -> Just . UseModule <$> lookupModule m
                        P.ParameterArg p ->
                           do mb <- lookupModParam p
                              case mb of
                                Nothing ->
                                   do inRange (srcRange lm)
                                              (recordError (MissingModParam p))
                                      pure Nothing
                                Just a -> pure (Just (UseParameter a))
                        P.AddParams -> pure (Just AddDeclParams)
               let next = case arg of
                            Nothing -> done
                            Just a  -> (srcRange lm, i, a) : done
               checkArgs next (Map.delete (thing ll) ps) more

          Nothing ->
            do recordErrorLoc (Just (srcRange ll))
                              (FunctorInstanceBadArgument (thing ll))
               checkArgs done ps more


data ArgInst = DefinedInst Subst [Decl] -- ^ Argument that defines the params
             | ParamInst (Set (MBQual TParam)) [Prop] (Map (MBQual Name) Type)
               -- ^ Argument that add parameters
               -- The type parameters are in their module type parameter
               -- form (i.e., tpFlav is TPModParam)



{- | Check the argument to a functor parameter.
Returns:

  * A substitution which will replace the parameter types with
    the concrete types that were provided

  * Some declarations that define the parameters in terms of the provided
    values.

  * XXX: Extra parameters for instantiation by adding params
-}
checkArg ::
  (Range, ModParam, ActualArg) -> InferM ArgInst
checkArg (r,expect,actual') =
  case actual' of
    AddDeclParams   -> paramInst
    UseParameter {} -> definedInst
    UseModule {}    -> definedInst

  where
  paramInst =
    do let as = Set.fromList
                   (map (qual . mtpParam) (Map.elems (mpnTypes params)))
           cs = map thing (mpnConstraints params)
           check = checkSimpleParameterValue r (mpName expect)
           qual a = (mpQual expect, a)
       fs <- Map.mapMaybeWithKey (\_ v -> v) <$> mapM check (mpnFuns params)
       pure (ParamInst as cs (Map.mapKeys qual fs))

  definedInst =
    do tRens <- mapM (checkParamType r tyMap) (Map.toList (mpnTypes params))
       let renSu = listParamSubst (concat tRens)

       {- Note: the constraints from the signature are already added to the
          constraints for the functor and they are checked all at once in
          doFunctorInst -}


       vDecls <- concat <$>
                  mapM (checkParamValue r vMap)
                       [ s { mvpType = apSubst renSu (mvpType s) }
                       | s <- Map.elems (mpnFuns params) ]

       pure (DefinedInst renSu vDecls)


  params = mpParameters expect

  -- Things provided by the argument module
  tyMap :: Map Ident (Kind, Type)
  vMap  :: Map Ident (Name, Schema)
  (tyMap,vMap) =
    case actual' of
      UseParameter mp ->
        ( nameMapToIdentMap fromTP (mpnTypes ps)
        , nameMapToIdentMap fromVP (mpnFuns ps)
        )
        where
        ps        = mpParameters mp
        fromTP tp = (mtpKind tp, TVar (TVBound (mtpParam tp)))
        fromVP vp = (mvpName vp, mvpType vp)

      UseModule actual ->
        ( Map.unions [ nameMapToIdentMap fromTS      (ifTySyns decls)
                     , nameMapToIdentMap fromNewtype (ifNewtypes decls)
                     , nameMapToIdentMap fromPrimT   (ifAbstractTypes decls)
                     ]

        , nameMapToIdentMap fromD (ifDecls decls)
        )

        where
        localNames      = ifsPublic (ifNames actual)
        isLocal x       = x `Set.member` localNames

        -- Things defined by the argument module
        decls           = filterIfaceDecls isLocal (ifDefines actual)

        fromD d         = (ifDeclName d, ifDeclSig d)
        fromTS ts       = (kindOf ts, tsDef ts)
        fromNewtype nt  = (kindOf nt, TNewtype nt [])
        fromPrimT pt    = (kindOf pt, TCon (abstractTypeTC pt) [])

      AddDeclParams -> panic "checkArg" ["AddDeclParams"]



nameMapToIdentMap :: (a -> b) -> Map Name a -> Map Ident b
nameMapToIdentMap f m =
  Map.fromList [ (nameIdent n, f v) | (n,v) <- Map.toList m ]




-- | Check a type parameter to a module.
checkParamType ::
  Range                 {- ^ Location for error reporting -} ->
  Map Ident (Kind,Type) {- ^ Actual types -} ->
  (Name,ModTParam)      {- ^ Type parameter -} ->
  InferM [(TParam,Type)]  {- ^ Mapping from parameter name to actual type -}
checkParamType r tyMap (name,mp) =
  let i       = nameIdent name
      expectK = mtpKind mp
  in
  case Map.lookup i tyMap of
    Nothing ->
      do recordErrorLoc (Just r) (FunctorInstanceMissingName NSType i)
         pure []
    Just (actualK,actualT) ->
      do unless (expectK == actualK)
           (recordErrorLoc (Just r)
                           (KindMismatch (Just (TVFromModParam name))
                                                  expectK actualK))
         pure [(mtpParam mp, actualT)]

-- | Check a value parameter to a module.
checkParamValue ::
  Range                   {- ^ Location for error reporting -} ->
  Map Ident (Name,Schema) {- ^ Actual values -} ->
  ModVParam               {- ^ The parameter we are checking -} ->
  InferM [Decl]           {- ^ Mapping from parameter name to definition -}
checkParamValue r vMap mp =
  let name     = mvpName mp
      i        = nameIdent name
      expectT  = mvpType mp
  in case Map.lookup i vMap of
       Nothing ->
         do recordErrorLoc (Just r) (FunctorInstanceMissingName NSValue i)
            pure []
       Just actual ->
         do e <- mkParamDef r (name,expectT) actual
            let d = Decl { dName        = name
                         , dSignature   = expectT
                         , dDefinition  = DExpr e
                         , dPragmas     = []
                         , dInfix       = isInfixIdent (nameIdent name)
                         , dFixity      = mvpFixity mp
                         , dDoc         = mvpDoc mp
                         }

            pure [d]



checkSimpleParameterValue ::
  Range                       {- ^ Location for error reporting -} ->
  Ident                       {- ^ Name of functor parameter -} ->
  ModVParam                   {- ^ Module parameter -} ->
  InferM (Maybe Type)  {- ^ Type to add to things, `Nothing` on err -}
checkSimpleParameterValue r i mp =
  case (sVars sch, sProps sch) of
    ([],[]) -> pure (Just (sType sch))
    _ ->
      do recordErrorLoc (Just r)
            (FunctorInstanceBadBacktick
               (BIPolymorphicArgument i (nameIdent (mvpName mp))))
         pure Nothing
  where
  sch = mvpType mp


{- | Make an "adaptor" that instantiates the paramter into the form expected
by the functor.  If the actual type is:

> {x} P => t

and the provided type is:

> f : {y} Q => s

The result, if successful would be:

  /\x \{P}. f @a {Q}

To do this we need to find types `a` to instantiate `y`, and prove that:
  {x} P => Q[a/y] /\ s = t
-}

mkParamDef ::
  Range           {- ^ Location of instantiation for error reporting -} ->
  (Name,Schema)   {- ^ Name and type of parameter -} ->
  (Name,Schema)   {- ^ Name and type of actual argument -} ->
  InferM Expr
mkParamDef r (pname,wantedS) (arg,actualS) =
  do (e,todo) <- collectGoals
          $ withTParams (sVars wantedS)
            do (e,t) <- instantiateWith pname(EVar arg) actualS []
               props <- unify WithSource { twsType   = sType wantedS
                                         , twsSource = TVFromModParam arg
                                         , twsRange  = Just r
                                         }
                        t
               newGoals (CtModuleInstance r) props
               pure e
     su <- proveImplication False
                            (Just pname)
                            (sVars wantedS)
                            (sProps wantedS)
                            todo
     let res  = foldr ETAbs     res1            (sVars wantedS)
         res1 = foldr EProofAbs (apSubst su e)  (sProps wantedS)

     applySubst res




