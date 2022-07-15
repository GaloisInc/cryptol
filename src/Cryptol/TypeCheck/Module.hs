{-# Language BlockArguments, ImplicitParams #-}
module Cryptol.TypeCheck.Module (doFunctorInst) where

import Data.Map(Map)
import qualified Data.Map as Map
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

doFunctorInst ::
  Located (P.ImpName Name)    {- ^ Name for the new module -} ->
  Located (P.ImpName Name)    {- ^ Functor being instantiation -} ->
  P.ModuleInstanceArgs Name   {- ^ Instance arguments -} ->
  Map Name Name
  {- ^ Instantitation.  These is the renaming for the functor that arises from
       generativity (i.e., it is something that will make the names "fresh").
  -} ->
  InferM (Maybe TCTopEntity)
doFunctorInst m f as inst =
  inRange (srcRange m)
  do mf    <- lookupFunctor (thing f)
     argIs <- checkArity (srcRange f) mf as
     (tySus,decls) <- unzip <$> mapM checkArg argIs


     let ?tSu = mergeDistinctSubst tySus
         ?vSu = inst
     let m1   = moduleInstance mf
         m2   = m1 { mName             = m
                   , mParamTypes       = mempty
                   , mParamFuns        = mempty
                   , mParamConstraints = mempty
                   , mParams           = mempty
                   -- XXX: Should we modify `mImports` to record dependencies
                   -- on parameters?
                   , mDecls = map NonRecursive (concat decls) ++ mDecls m1
                   }
     newGoals CtModuleInstance (map thing (mParamConstraints m1))

     case thing m of
       P.ImpTop mn    -> newModuleScope mn (mImports m2) (mExports m2)
       P.ImpNested mn -> newSubmoduleScope mn (mImports m2) (mExports m2)

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




-- | Validate a functor application, just checking the argument names
checkArity ::
  Range             {- ^ Location for reporting errors -} ->
  ModuleG ()        {- ^ The functor being instantiated -} ->
  P.ModuleInstanceArgs Name {- ^ The arguments -} ->
  InferM [ (Range, ModParam, IfaceG ()) ]
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
            do mo <- lookupModule (thing lm)
               checkArgs ((srcRange lm, i, mo) : done)
                         (Map.delete (thing ll) ps) more
          Nothing ->
            do recordErrorLoc (Just (srcRange ll))
                              (FunctorInstanceBadArgument (thing ll))
               checkArgs done ps more


checkArg :: (Range, ModParam, IfaceG ()) -> InferM (Subst, [Decl])
checkArg (r,expect,actual) =
  do tRens <- mapM (checkParamType r tyMap) (Map.toList (mpnTypes params))
     let renSu = listParamSubst (concat tRens)

     {- Note: the constraints from the signature are already added to the
        constraints for the functor so and they are checked all at once in
        doFunctorInst -}

     -- Available value names
     let fromD d = (ifDeclName d, ifDeclSig d)
         vMap = nameMapToIdentMap fromD (ifDecls decls)

     vDecls <- concat <$>
                mapM (checkParamValue r vMap)
                     [ s { mvpType = apSubst renSu (mvpType s) }
                     | s <- Map.elems (mpnFuns params) ]

     pure (renSu, vDecls)




  where
  params = mpParameters expect

  localNames = ifsPublic (ifNames actual)
  isLocal x  = x `Set.member` localNames
  decls      = filterIfaceDecls isLocal (ifDefines actual)

  -- Available type names
  tyMap      = Map.unions [ nameMapToIdentMap fromTS      (ifTySyns decls)
                          , nameMapToIdentMap fromNewtype (ifNewtypes decls)
                          , nameMapToIdentMap fromPrimT   (ifAbstractTypes decls)
                          ]

  fromTS ts      = (kindOf ts, tsDef ts)
  fromNewtype nt = (kindOf nt, TNewtype nt [])
  fromPrimT pt   = (kindOf pt, TCon (abstractTypeTC pt) [])


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
               newGoals CtModuleInstance props
               pure e
     su <- proveImplication (Just pname)
                            (sVars wantedS)
                            (sProps wantedS)
                            todo
     let res  = foldr ETAbs     res1            (sVars wantedS)
         res1 = foldr EProofAbs (apSubst su e)  (sProps wantedS)

     pure res




