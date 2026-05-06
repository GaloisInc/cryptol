{-# Language BlockArguments, ImplicitParams #-}
module Cryptol.TypeCheck.Module (doFunctorInst) where

import Data.List(partition)
import Data.Text(Text)
import Data.Map(Map)
import Data.Maybe (maybeToList)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad(unless,forM_,mapAndUnzipM)


import Cryptol.Utils.Panic(panic)
import Cryptol.Utils.Ident(Ident,Namespace(..),isInfixIdent)
import Cryptol.Parser.Position (Range,Located(..), thing)
import qualified Cryptol.Parser.AST as P
import Cryptol.ModuleSystem.Name(nameIdent,nameNamespace,nameFixity)
import Cryptol.ModuleSystem.NamingEnv
          (NamingEnv(..), modParamNamesNamingEnv, shadowing, without, mapNamingEnv)
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
  P.ModuleInstance Name
  {- ^ Instantiation.  Filled in by the renamer.
       Contains the renaming for the functor that arises from
       generativity (i.e., it is something that will make the names "fresh"),
       and virtual submodule names for functor parameters.
  -} ->
  NamingEnv
  {- ^ Names in the enclosing scope of the instantiated module -} ->
  Maybe Text                  {- ^ Documentation for the module being generated -} ->
  InferM (Maybe TCTopEntity)
doFunctorInst m f as modInst enclosingInScope doc =
  inRange (srcRange m)
  do let instMap = P.modInstMap modInst
     mf    <- lookupFunctor (thing f)
     argIs <- checkArity (srcRange f) mf as
     m2 <- do as2 <- mapM (checkArg instMap) argIs
              let (tySus,paramTySyns,decls) =
                    unzip3 [ (su,ts,ds) | DefinedInst su ts ds <- as2 ]
              let ?tVarSu = mergeDistinctSubst tySus
                  ?nameSu = instMap
              let m1   = moduleInstance mf
                  m2   = m1 { mName             = m
                            , mDoc              = mempty
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
     -- the module parameters from the naming environment, but we should
     -- still add type synonyms.
     let ren x = case Map.lookup x instMap of
                   Just x' -> x'
                   Nothing -> panic "doFunctorInst" ["Missing module parameter"]
         inScope0 = mInScope m2 `without`
           mapNamingEnv ren (
             mconcat [ modParamNamesNamingEnv nms
                     | (_, mp, AddDeclParams) <- argIs 
                     , let nms = (mpParameters mp) { mpnTySyn = mempty }
                     ])
         inScope = inScope0 `shadowing` enclosingInScope

     -- Combine the docstrings of:
     -- * The functor being instantiated
     -- * The module being generated
     let newDoc = maybeToList doc <> mDoc mf

     case thing m of
       P.ImpTop mn    -> newModuleScope newDoc mn (mExports m2) inScope
       P.ImpNested mn -> newSubmoduleScope mn newDoc (mExports m2) inScope

     mapM_ addTySyn     (Map.elems (mTySyns m2))
     mapM_ addNominal   (Map.elems (mNominalTypes m2))
     addSignatures      (mSignatures m2)
     addFunctors        (mFunctors m2)
     mapM_ addDecls     (mDecls m2)

     (vpmSubs, vpmNested) <-
       makeVirtParamModDefs (P.modInstVirtParamMods modInst)
     addSubmodules      (mSubmodules m2 `Map.union` vpmSubs)
     setNested          (mNested m2 `Set.union` vpmNested)

     case thing m of
       P.ImpTop {}    -> Just <$> endModule
       P.ImpNested {} -> endSubmodule >> pure Nothing


-- | Generate forwarding definitions for virtual parameter submodules
-- (e.g., @M::I::x@).  For each virtual parameter module we create value
-- forwarding decls (@defName = paramName@) and type synonym aliases.
-- Returns the submodule map and nested name set to be registered by the caller.
makeVirtParamModDefs ::
  [P.VirtParamMod Name] -> InferM (Map Name Submodule, Set Name)
makeVirtParamModDefs vpmods =
  do forM_ vpmods \ps ->
       forM_ (Map.toList (P.vpmDefs ps)) \(defName, paramName) ->
         case nameNamespace defName of
           NSValue ->
             do vt <- lookupVar paramName
                let schema = case vt of
                      ExtVar s -> s
                      CurSCC {} -> bad "CurSCC for parameter variable"
                    body = fwdDef schema paramName
                addDecls $ NonRecursive Decl
                  { dName       = defName
                  , dSignature  = schema
                  , dDefinition = DExpr body
                  , dPragmas    = []
                  , dInfix      = isInfixIdent (nameIdent defName)
                  , dFixity     = nameFixity defName
                  , dDoc        = Nothing
                  }
           NSType ->
             do ts <- lookupTSyn paramName
                case ts of
                  Just origSyn ->
                    addTySyn origSyn { tsName = defName }
                  Nothing -> bad "Missing type synonym for parameter"
           ns -> bad ("Unexpected namespace for parameter: " ++ show ns)

     let submodules = Map.fromList
           [ (P.vpmName ps, Submodule
               { smIface = IfaceNames
                   { ifsName    = P.vpmName ps
                   , ifsNested  = mempty
                   , ifsDefines = Map.keysSet (P.vpmDefs ps)
                   , ifsPublic  = Map.keysSet (P.vpmDefs ps)
                   , ifsDoc     = mempty
                   }
               , smInScope = mempty
               , smVirtual = True
               })
           | ps <- vpmods
           ]
         nested = Set.fromList [ P.vpmName ps | ps <- vpmods ]

     pure (submodules, nested)
  where
  bad msg = panic "makeVirtParamModDefs" [msg]

  fwdDef (Forall tps props _) name =
    foldr ETAbs (foldr EProofAbs call props) tps
    where
    call = foldl (\e _ -> EProofApp e) tyApp props
    tyApp = foldl ETApp (EVar name) (map (TVar . TVBound) tps)


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

             | ParamInst (Set (MBQual TParam)) [Prop] (Map (MBQual Name) Type)
               -- ^ Argument that add parameters
               -- The type parameters are in their module type parameter
               -- form (i.e., tpFlav is TPModParam)



{- | Check the argument to a functor parameter. -}
checkArg :: Map Name Name -> (Range, ModParam, ActualArg) -> InferM ArgInst
checkArg instMap (r,expect,actual') =
  case actual' of
    AddDeclParams   -> paramInst
    UseParameter {} -> definedInst
    UseModule {}    -> definedInst

  where
  paramInst =
    do let (as,su) = prepParamTypeBacktick instMap (Map.elems (mpnTypes params))
           cs = map (apSubst su . thing) (mpnConstraints params)
           check = checkParamValueBacktick instMap su r (mpName expect)
           qual a = (mpQual expect, a)
       fs <- concat <$> mapM check (Map.elems (mpnFuns params))
       let funs = Map.fromList [ (qual f, t) | (f,t) <- fs ]
       pure (ParamInst (Set.fromList (map qual as)) cs funs)

  definedInst =
    do (tRens, tSyns) <-
         mapAndUnzipM (checkParamType instMap r tyMap) (Map.toList (mpnTypes params))
       let renSu = listParamSubst (concat tRens)

       {- Note: the constraints from the signature are already added to the
          constraints for the functor and they are checked all at once in
          doFunctorInst -}


       vDecls <-
         mapM (checkParamValue instMap r vMap)
           [ s { mvpType = apSubst renSu (mvpType s) }
           | s <- Map.elems (mpnFuns params) ]

       pure $ DefinedInst renSu (mconcat tSyns) (concat vDecls)


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
  Map Name Name              {- ^ Renaming -} ->
  Range                      {- ^ Location for error reporting -} ->
  Map Ident (Kind,Type)      {- ^ Actual types -} ->
  (Name,ModTParam)           {- ^ Type parameter -} ->
  InferM ([(TParam,Type)], Map Name TySyn)
    {- ^ Mapping from parameter name to actual type (for type substitution),
         type synonym map from a fresh type name to the actual type
           (only so that the type can be referred to in the REPL;
            type synonyms are fully inlined into types at this point),
         and a map from the old type name to the fresh type name
           (for instantiation) -}
checkParamType instMap r tyMap (name,mp) =
  let i       = nameIdent name
      expectK = mtpKind mp
  in
  case Map.lookup i tyMap of
    Nothing ->
      do recordErrorLoc (Just r) (FunctorInstanceMissingName NSType i)
         pure ([], Map.empty)
    Just (actualK,actualT) ->
      do unless (expectK == actualK)
           (recordErrorLoc (Just r)
                           (KindMismatch (Just (TVFromModParam name))
                                                  expectK actualK))
         let name' = case Map.lookup name instMap of
                       Just nm -> nm
                       Nothing -> panic "checkParamType" [ "missing name" ]
         let tySyn = TySyn { tsName = name'
                           , tsParams = []
                           , tsConstraints = []
                           , tsDef = actualT
                           , tsDoc = mtpDoc mp }
         pure ( [(mtpParam mp, actualT)]
              , Map.singleton name' tySyn
              )

-- | Check a value parameter to a module.
checkParamValue ::
  Map Name Name           {- ^ Name instance map -} ->
  Range                   {- ^ Location for error reporting -} ->
  Map Ident (Name,Schema) {- ^ Actual values -} ->
  ModVParam               {- ^ The parameter we are checking -} ->
  InferM [Decl]
  {- ^ Decl mapping a new name to the actual value,
       and a map from the value param name in the functor to the new name
         (for instantiation) -}
checkParamValue instMap r vMap mp =
  let name     = mvpName mp
      i        = nameIdent name
      expectT  = mvpType mp
  in case Map.lookup i vMap of
       Nothing ->
         do recordErrorLoc (Just r) (FunctorInstanceMissingName NSValue i)
            pure []
       Just actual ->
         do e <- mkParamDef r (name,expectT) actual
            let name' = case Map.lookup name instMap of
                          Just nm -> nm
                          Nothing -> panic "checkParamValue" ["Missing name"]
            let d = Decl { dName        = name'
                         , dSignature   = expectT
                         , dDefinition  = DExpr e
                         , dPragmas     = []
                         , dInfix       = isInfixIdent (nameIdent name')
                         , dFixity      = mvpFixity mp
                         , dDoc         = mvpDoc mp
                         }

            pure [d]


--------------------------------------------------------------------------------
-- "Backtick" instantiation
--------------------------------------------------------------------------------

-- | Compute the names of the type parameters for a backtick import.
-- The `ModTParam` arguments are those from the functor, so we need to
-- apply the instantiation renaming to them, so that it can be consistently
-- used when instantiation
prepParamTypeBacktick :: Map Name Name -> [ModTParam] -> ([TParam], Subst)
prepParamTypeBacktick nameInst mps = (newTPs, su)
  where
  su     = listParamSubst (oldTPs `zip` map (TVar . TVBound) newTPs)
  newTPs = map renP mps
  oldTPs = map mtpParam mps
  renP p =
    case Map.lookup (mtpName p) nameInst of
      Just nm -> mtpParam p { mtpName = nm }
      Nothing -> panic "prepParamTypeBacktick" ["Missing parameter"]


-- | Check that the type o
checkParamValueBacktick ::
  Map Name Name               {- ^ Instantiation map -} ->
  Subst                       {- ^ Renaming subsitution -} ->
  Range                       {- ^ Location for error reporting -} ->
  Ident                       {- ^ Name of functor parameter -} ->
  ModVParam                   {- ^ Module parameter -} ->
  InferM [(Name, Type)]       {- ^ Name to use, and it's type.  [] on error -}
checkParamValueBacktick instMap su r i mp =
  case (sVars sch, sProps sch) of
    ([],ps) | all pIsTrue ps -> pure [(newNm,apSubst su (sType sch))]
    _ ->
      do recordErrorLoc (Just r)
            (FunctorInstanceBadBacktick
               (BIPolymorphicArgument i (nameIdent (mvpName mp))))
         pure []
  where
  sch = mvpType mp
  newNm =
    case Map.lookup (mvpName mp) instMap of
      Just nm -> nm
      Nothing -> panic "checkParamValueBacktick" ["Missing value parameter"]
--------------------------------------------------------------------------------

{- | Make an "adaptor" that instantiates the parameter into the form expected
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