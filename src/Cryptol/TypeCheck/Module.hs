{-# Language BlockArguments, ImplicitParams #-}
module Cryptol.TypeCheck.Module (doFunctorInst) where

import Data.List(partition,unzip4)
import Data.Text(Text)
import Data.Map(Map)
import qualified Data.Map as Map
import qualified Data.Map.Merge.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad(unless,forM_,mapAndUnzipM)


import Cryptol.Utils.Panic(panic)
import Cryptol.Utils.Ident(Ident,Namespace(..),ModPath,isInfixIdent)
import Cryptol.Parser.Position (Range,Located(..), thing)
import qualified Cryptol.Parser.AST as P
import Cryptol.ModuleSystem.Binds(newFunctorInst)
import Cryptol.ModuleSystem.Name(nameIdent)
import Cryptol.ModuleSystem.NamingEnv
          (NamingEnv(..), modParamNamingEnv, shadowing, without)
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
  NamingEnv
  {- ^ Names in the enclosing scope of the instantiated module -} ->
  Maybe Text                  {- ^ Documentation -} ->
  InferM (Maybe TCTopEntity)
doFunctorInst m f as instMap0 enclosingInScope doc =
  inRange (srcRange m)
  do mf    <- lookupFunctor (thing f)
     argIs <- checkArity (srcRange f) mf as
     m2 <- do let mpath = P.impNameModPath (thing m)
              as2 <- mapM (checkArg mpath) argIs
              let (tySus,paramTySyns,decls,paramInstMaps) =
                    unzip4 [ (su,ts,ds,im) | DefinedInst su ts ds im <- as2 ]
              instMap <- addMissingTySyns mpath mf instMap0
              let ?tVarSu = mergeDistinctSubst tySus
                  ?nameSu = instMap <> mconcat paramInstMaps
              let m1   = moduleInstance mf
                  m2   = m1 { mName             = m
                            , mDoc              = Nothing
                            , mParamTypes       = mempty
                            , mParamFuns        = mempty
                            , mParamConstraints = mempty
                            , mParams           = mempty
                            , mTySyns = mconcat paramTySyns <> mTySyns m1
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

     -- An instantiation doesn't really have anything "in scope" per se, but
     -- here we compute what would be in scope as if you hand wrote the
     -- instantiation by copy-pasting the functor then substituting the
     -- parameters. That is, it would be whatever is in scope in the functor,
     -- together with any names in the enclosing scope if this is a nested
     -- module, with the functor's names taking precedence. This is used to
     -- determine what is in scope at the REPL when the instantiation is loaded
     -- and focused.
     --
     -- The exception is when instantiating with _, in which case we must delete
     -- the module parameters from the naming environment.
     let inScope0 = mInScope m2 `without`
           mconcat [ modParamNamingEnv mp | (_, mp, AddDeclParams) <- argIs ]
         inScope = inScope0 `shadowing` enclosingInScope

     case thing m of
       P.ImpTop mn    -> newModuleScope mn (mExports m2) inScope
       P.ImpNested mn -> newSubmoduleScope mn doc (mExports m2) inScope

     mapM_ addTySyn     (Map.elems (mTySyns m2))
     mapM_ addNominal   (Map.elems (mNominalTypes m2))
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
be instantiated.
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
      let p0 = case Map.keys ps0 of
                 p':_ -> p'
                 [] -> panic "checkArity" ["functor with no parameters"]
          i = Located { srcRange = srcRange arg
                      , thing    = p0
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


data ArgInst = -- | Argument that defines the params
               DefinedInst Subst
                 (Map Name TySyn)
                 -- ^ Type synonyms created from the functor's type parameters
                 [Decl]
                 -- ^ Bindings for value parameters
                 (Map Name Name)
                 -- ^ Map from the functor's parameter names to the new names
                 --   created for the instantiation

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
  ModPath -> (Range, ModParam, ActualArg) -> InferM ArgInst
checkArg mpath (r,expect,actual') =
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
    do (tRens, tSyns, tInstMaps) <- unzip3 <$>
         mapM (checkParamType mpath r tyMap) (Map.toList (mpnTypes params))
       let renSu = listParamSubst (concat tRens)

       {- Note: the constraints from the signature are already added to the
          constraints for the functor and they are checked all at once in
          doFunctorInst -}


       (vDecls, vInstMaps) <-
         mapAndUnzipM (checkParamValue mpath r vMap)
           [ s { mvpType = apSubst renSu (mvpType s) }
           | s <- Map.elems (mpnFuns params) ]

       pure $ DefinedInst renSu (mconcat tSyns)
         (concat vDecls) (mconcat tInstMaps <> mconcat vInstMaps)


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
                     , nameMapToIdentMap fromNominal (ifNominalTypes decls)
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
        fromNominal nt  = (kindOf nt, TNominal nt [])

      AddDeclParams -> panic "checkArg" ["AddDeclParams"]



nameMapToIdentMap :: (a -> b) -> Map Name a -> Map Ident b
nameMapToIdentMap f m =
  Map.fromList [ (nameIdent n, f v) | (n,v) <- Map.toList m ]




-- | Check a type parameter to a module.
checkParamType ::
  ModPath                    {- ^ The new module we are creating -} ->
  Range                      {- ^ Location for error reporting -} ->
  Map Ident (Kind,Type)      {- ^ Actual types -} ->
  (Name,ModTParam)           {- ^ Type parameter -} ->
  InferM ([(TParam,Type)], Map Name TySyn, Map Name Name)
    {- ^ Mapping from parameter name to actual type (for type substitution),
         type synonym map from a fresh type name to the actual type
           (only so that the type can be referred to in the REPL;
            type synonyms are fully inlined into types at this point),
         and a map from the old type name to the fresh type name
           (for instantiation) -}
checkParamType mpath r tyMap (name,mp) =
  let i       = nameIdent name
      expectK = mtpKind mp
  in
  case Map.lookup i tyMap of
    Nothing ->
      do recordErrorLoc (Just r) (FunctorInstanceMissingName NSType i)
         pure ([], Map.empty, Map.empty)
    Just (actualK,actualT) ->
      do unless (expectK == actualK)
           (recordErrorLoc (Just r)
                           (KindMismatch (Just (TVFromModParam name))
                                                  expectK actualK))
         name' <- newFunctorInst mpath name
         let tySyn = TySyn { tsName = name'
                           , tsParams = []
                           , tsConstraints = []
                           , tsDef = actualT
                           , tsDoc = mtpDoc mp }
         pure ( [(mtpParam mp, actualT)]
              , Map.singleton name' tySyn
              , Map.singleton name name'
              )

-- | Check a value parameter to a module.
checkParamValue ::
  ModPath                 {- ^ The new module we are creating -} ->
  Range                   {- ^ Location for error reporting -} ->
  Map Ident (Name,Schema) {- ^ Actual values -} ->
  ModVParam               {- ^ The parameter we are checking -} ->
  InferM ([Decl], Map Name Name)
  {- ^ Decl mapping a new name to the actual value,
       and a map from the value param name in the functor to the new name
         (for instantiation) -}
checkParamValue mpath r vMap mp =
  let name     = mvpName mp
      i        = nameIdent name
      expectT  = mvpType mp
  in case Map.lookup i vMap of
       Nothing ->
         do recordErrorLoc (Just r) (FunctorInstanceMissingName NSValue i)
            pure ([], Map.empty)
       Just actual ->
         do e <- mkParamDef r (name,expectT) actual
            name' <- newFunctorInst mpath name
            let d = Decl { dName        = name'
                         , dSignature   = expectT
                         , dDefinition  = DExpr e
                         , dPragmas     = []
                         , dInfix       = isInfixIdent (nameIdent name')
                         , dFixity      = mvpFixity mp
                         , dDoc         = mvpDoc mp
                         }

            pure ([d], Map.singleton name name')



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


-- | The instMap we get from the renamer will not contain the fresh names for
-- certain things in the functor generated in the typechecking stage, if we are
-- instantiating a functor that is in the same file, since renaming and
-- typechecking happens together with the instantiation. In particular, if the
-- functor's interface has type synonyms, they will only get copied over into
-- the functor in the typechecker, so the renamer will not see them. Here we
-- make the fresh names for those missing type synonyms and add them to the
-- instMap.
addMissingTySyns ::
  ModPath                  {- ^ The new module we are creating -} ->
  ModuleG ()               {- ^ The functor -} ->
  Map Name Name            {- ^ instMap we get from renamer -} ->
  InferM (Map Name Name)   {- ^ the complete instMap -}
addMissingTySyns mpath f = Map.mergeA
  (Map.traverseMissing \name _ -> newFunctorInst mpath name)
  Map.preserveMissing
  (Map.zipWithMatched \_ _ name' -> name')
  (mTySyns f)
