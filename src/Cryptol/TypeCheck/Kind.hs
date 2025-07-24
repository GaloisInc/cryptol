-- |
-- Module      :  Cryptol.TypeCheck.Kind
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE BlockArguments #-}
-- See Note [-Wincomplete-uni-patterns and irrefutable patterns] in Cryptol.TypeCheck.TypePat
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Cryptol.TypeCheck.Kind
  ( checkType
  , checkSchema
  , checkNewtype
  , checkEnum
  , checkPrimType
  , checkTySyn
  , checkPropSyn
  , checkParameterType
  , checkParameterConstraints
  , checkPropGuards
  ) where

import qualified Cryptol.Parser.AST as P
import           Cryptol.Parser.Position
import           Cryptol.TypeCheck.AST
import           Cryptol.TypeCheck.Error
import           Cryptol.TypeCheck.Subst(listSubst,apSubst)
import           Cryptol.TypeCheck.Monad hiding (withTParams)
import           Cryptol.TypeCheck.SimpType(tRebuild)
import           Cryptol.TypeCheck.SimpleSolver(simplify)
import           Cryptol.TypeCheck.Solve (simplifyAllConstraints)
import           Cryptol.Utils.Panic (panic)
import           Cryptol.Utils.PP(pp,commaSep)
import           Cryptol.Utils.RecordMap

import qualified Data.Map as Map
import           Data.List(sortBy,groupBy)
import           Data.Maybe(fromMaybe)
import           Data.Function(on)
import           Data.Text (Text)
import           Control.Monad(unless,mplus,forM,when)

-- | Check a type signature.  Returns validated schema, and any implicit
-- constraints that we inferred.
checkSchema :: AllowWildCards -> P.Schema Name -> InferM (Schema, [Goal])
checkSchema withWild (P.Forall xs ps t mb) =
  do ((xs1,(ps1,t1)), gs) <-
        collectGoals $
        rng $ withTParams withWild schemaParam xs $
        do ps1 <- mapM checkProp ps
           t1  <- doCheckType t (Just KType)
           return (ps1,t1)
     -- XXX: We probably shouldn't do this, as we are changing what the
     -- user is doing.  We do it so that things are in a propal normal form,
     -- but we should probably figure out another time to do this.
     let newPs = concatMap pSplitAnd $ map (simplify mempty)
                                     $ map tRebuild ps1
     return ( Forall xs1 newPs (tRebuild t1)
            , [ g { goal = tRebuild (goal g) } | g <- gs ]
            )

  where
  rng = case mb of
          Nothing -> id
          Just r  -> inRange r

{- | Validate parsed propositions that appear in the guard of a PropGuard.

  * Note that we don't validate the well-formedness constraints here---instead,
    they'd be validated when the signature for the auto generated
    function corresponding guard is checked.

  * We also check that there are no wild-cards in the constraints.
-}
checkPropGuards :: [Located (P.Prop Name)] -> InferM [Prop]
checkPropGuards props =
  do (newPs,_gs) <- collectGoals (mapM check props)
     pure newPs
  where
  check lp =
    inRange (srcRange lp)
    do let p = thing lp
       (_,ps) <- withTParams NoWildCards schemaParam [] (checkProp p)
       case tNoUser ps of
         TCon (PC x) _ | x `elem` [PEqual,PNeq,PGeq,PFin,PTrue] -> pure ()
         _ -> recordError (InvalidConstraintGuard ps)
       pure ps



-- | Check a module parameter declarations.  Nothing much to check,
-- we just translate from one syntax to another.
checkParameterType :: P.ParameterType Name -> InferM ModTParam
checkParameterType a =
  do let mbDoc = P.ptDoc a
         k = cvtK (P.ptKind a)
         n = thing (P.ptName a)
     return ModTParam { mtpKind = k, mtpName = n, mtpDoc = thing <$> mbDoc }


-- | Check a type-synonym declaration.
checkTySyn :: P.TySyn Name -> Maybe Text -> InferM TySyn
checkTySyn (P.TySyn x _ as t) mbD =
  do ((as1,t1),gs) <- collectGoals
                    $ inRange (srcRange x)
                    $ do r <- withTParams NoWildCards tySynParam as
                                                      (doCheckType t Nothing)
                         simplifyAllConstraints
                         return r
     return TySyn { tsName   = thing x
                  , tsParams = as1
                  , tsConstraints = map (tRebuild . goal) gs
                  , tsDef = tRebuild t1
                  , tsDoc = mbD
                  }

-- | Check a constraint-synonym declaration.
checkPropSyn :: P.PropSyn Name -> Maybe Text -> InferM TySyn
checkPropSyn (P.PropSyn x _ as ps) mbD =
  do ((as1,t1),gs) <- collectGoals
                    $ inRange (srcRange x)
                    $ do r <- withTParams NoWildCards propSynParam as
                                                      (traverse checkProp ps)
                         simplifyAllConstraints
                         return r
     return TySyn { tsName   = thing x
                  , tsParams = as1
                  , tsConstraints = map (tRebuild . goal) gs
                  , tsDef = tRebuild (pAnd t1)
                  , tsDoc = mbD
                  }

-- | Check a newtype declaration.
checkNewtype :: P.Newtype Name -> Maybe Text -> InferM NominalType
checkNewtype (P.Newtype x as con fs) mbD =
  do ((as1,fs1),gs) <- collectGoals $
       inRange (srcRange x) $
       do r <- withTParams NoWildCards nominalParam as $
               flip traverseRecordMap fs $ \_n (rng,f) ->
                 kInRange rng $ doCheckType f (Just KType)
          simplifyAllConstraints
          return r

     return NominalType
                    { ntName   = thing x
                    , ntKind   = KType
                    , ntParams = as1
                    , ntConstraints = map goal gs
                    , ntDef = Struct
                                StructCon { ntConName = con, ntFields = fs1 }
                    , ntFixity = Nothing
                    , ntDoc = mbD
                    }

checkEnum :: P.EnumDecl Name -> Maybe Text -> InferM NominalType
checkEnum ed mbD =
  do let x = P.eName ed
     ((as1,cons1),gs) <- collectGoals $
       inRange (srcRange x) $
       do r <- withTParams NoWildCards nominalParam (P.eParams ed) $
               forM (P.eCons ed `zip` [0..]) \(tlC,nu) ->
                 do let con = P.tlValue tlC
                        cname = P.ecName con
                    ts <- kInRange (srcRange cname)
                            (mapM (`doCheckType` Just KType) (P.ecFields con))
                    pure EnumCon
                          { ecName   = thing cname
                          , ecNumber = nu
                          , ecFields = ts
                          , ecPublic = P.tlExport tlC == P.Public
                          , ecDoc    = thing <$> P.tlDoc tlC
                          }
          simplifyAllConstraints
          pure r
     pure NominalType
                  { ntName = thing x
                  , ntParams = as1
                  , ntKind = KType
                  , ntConstraints = map goal gs
                  , ntDef = Enum cons1
                  , ntFixity = Nothing
                  , ntDoc = mbD
                  }

checkPrimType :: P.PrimType Name -> Maybe Text -> InferM NominalType
checkPrimType p mbD =
  do let (as,cs) = P.primTCts p
     (as',cs') <- withTParams NoWildCards TPPrimParam as (mapM checkProp cs)
     let (args,finK) = splitK (cvtK (thing (P.primTKind p)))
         (declared,others) = splitAt (length as') args
     unless (and (zipWith (==) (map kindOf as') args)) $
       panic "checkPrimType"
         [ "Primtive declaration, kind argument prefix mismach:"
         , "Expected: " ++ show (commaSep (map (pp . kindOf) as'))
         , "Actual: " ++ show (commaSep (map pp declared))
         ]
     pure NominalType
            { ntName = thing (P.primTName p)
            , ntParams = as'
            , ntKind = foldr (:->) finK others
            , ntFixity = P.primTFixity p
            , ntConstraints = cs'
            , ntDoc = mbD
            , ntDef = Abstract
            }
  where
  splitK k =
    case k of
      k1 :-> k2 -> (k1:ks,r)
        where (ks,r) = splitK k2
      _ -> ([], k)


checkType :: P.Type Name -> Maybe Kind -> InferM Type
checkType t k =
  do (_, t1) <- withTParams AllowWildCards schemaParam [] $ doCheckType t k
     return (tRebuild t1)

checkParameterConstraints :: [Located (P.Prop Name)] -> InferM [Located Prop]
checkParameterConstraints ps =
  do (_, cs) <- withTParams NoWildCards schemaParam [] (mapM checkL ps)
     return cs
  where
  checkL x = do p <- checkProp (thing x)
                return x { thing = tRebuild p }


{- | Check something with type parameters.

When we check things with type parameters (i.e., type schemas, and type
synonym declarations) we do kind inference based only on the immediately
visible body.  Type parameters that are not mentioned in the body are
defaulted to kind 'KNum'.  If this is not the desired behavior, programmers
may add explicit kind annotations on the type parameters.

Here is an example of how this may show up:

> f : {n}. [8] -> [8]
> f x =  x + `n

Note that @n@ does not appear in the body of the schema, so we will
default it to 'KNum', which is the correct thing in this case.
To use such a function, we'd have to provide an explicit type application:

> f `{n = 3}

There are two reasons for this choice:

  1. It makes it possible to figure if something is correct without
     having to look through arbitrary amounts of code.

  2. It is a bit easier to implement, and it covers the large majority
     of use cases, with a very small inconvenience (an explicit kind
     annotation) in the rest.
-}

withTParams :: AllowWildCards    {- ^ Do we allow wild cards -} ->
              (Name -> TPFlavor) {- ^ What sort of params are these? -} ->
              [P.TParam Name]    {- ^ The params -} ->
              KindM a            {- ^ do this using the params -} ->
              InferM ([TParam], a)
withTParams allowWildCards flav xs m
  | not (null duplicates) = panic "withTParams" $ "Repeated parameters"
                                                : map show duplicates
  | otherwise =
  do (as,a,ctrs) <-
        mdo (a, vars,ctrs) <- runKindM allowWildCards (zip' xs as) m
            as <- mapM (newTP vars) xs
            return (as,a,ctrs)
     mapM_ (uncurry newGoals) ctrs
     return (as,a)

  where
  getKind vs tp =
    case Map.lookup (P.tpName tp) vs of
      Just k  -> return k
      Nothing -> do recordWarning (DefaultingKind tp P.KNum)
                    return KNum

  newTP vs tp = do k <- getKind vs tp
                   let nm = P.tpName tp
                   newTParam tp (flav nm) k


  {- Note that we only zip based on the first argument.
  This is needed to make the monadic recursion work correctly,
  because the data dependency is only on the part that is known. -}
  zip' [] _           = []
  zip' (a:as) ~(t:ts) = (P.tpName a, fmap cvtK (P.tpKind a), t) : zip' as ts

  duplicates = [ ds | ds@(_ : _ : _) <- groupBy ((==) `on` P.tpName)
                                      $ sortBy (compare `on` P.tpName) xs ]

cvtK :: P.Kind -> Kind
cvtK P.KNum  = KNum
cvtK P.KType = KType
cvtK P.KProp = KProp
cvtK (P.KFun k1 k2) = cvtK k1 :-> cvtK k2



-- | Check an application of a type constant.
tcon :: TCon            -- ^ Type constant being applied
     -> [P.Type Name]   -- ^ Type parameters
     -> Maybe Kind      -- ^ Expected kind
     -> KindM Type      -- ^ Resulting type
tcon tc ts0 k =
  do (ts1,k1) <- appTy ts0 (kindOf tc)
     checkKind (TCon tc ts1) k k1


-- | Check a type application of a non built-in type or type variable.
checkTUser ::
  Name          {- ^ The name that is being applied to some arguments. -} ->
  [P.Type Name] {- ^ Parameters to the type -} ->
  Maybe Kind    {- ^ Expected kind -} ->
  KindM Type    {- ^ Resulting type -}
checkTUser x ts k =
  mcase kLookupTyVar      checkBoundVarUse $
  mcase kLookupTSyn       checkTySynUse $
  mcase kLookupNominal    checkNominalTypeUse $
  mcase kLookupParamType  checkModuleParamUse $
  checkScopedVarUse -- none of the above, must be a scoped type variable,
                    -- if the renamer did its job correctly.
  where
  checkTySynUse tysyn =
    do (ts1,k1) <- appTy ts (kindOf tysyn)
       let as  = tsParams tysyn
       ts2 <- checkParams as ts1
       let su = zip as ts2
       ps1 <- mapM (`kInstantiateT` su) (tsConstraints tysyn)
       kNewGoals (CtPartialTypeFun (tsName tysyn)) ps1
       t1  <- kInstantiateT (tsDef tysyn) su
       checkKind (TUser x ts1 t1) k k1

  checkNominalTypeUse nt
    | Abstract <- ntDef nt =
      do (ts1,k1) <- appTy ts (kindOf nt)
         let as = ntParams nt
             ps = ntConstraints nt
         case as of
           [] -> pure ()
           _ -> do let need = length as
                       have = length ts1
                   when (need > have) $
                     kRecordError (TooFewTyParams (ntName nt) (need - have))
                   let su = listSubst (map tpVar as `zip` ts1)
                   kNewGoals (CtPartialTypeFun (ntName nt)) (apSubst su <$> ps)
         let ty =
               -- We must uphold the invariant that built-in abstract types
               -- are represented with TCon. User-defined abstract types use
               -- TNominal instead.
               case builtInType (ntName nt) of
                 Just tc -> TCon tc ts1
                 Nothing -> TNominal nt ts1
         checkKind ty k k1

    | otherwise =
    do (ts1,k1) <- appTy ts (kindOf nt)
       let as = ntParams nt
       ts2 <- checkParams as ts1
       let su = zip as ts2
       ps1 <- mapM (`kInstantiateT` su) (ntConstraints nt)
       kNewGoals (CtPartialTypeFun (ntName nt)) ps1
       checkKind (TNominal nt ts2) k k1

  checkParams as ts1
    | paramHave == paramNeed = return ts1
    | paramHave < paramNeed  =
                   do kRecordError (TooFewTyParams x (paramNeed-paramHave))
                      let src = TypeErrorPlaceHolder
                      fake <- mapM (kNewType src . kindOf . tpVar)
                                   (drop paramHave as)
                      return (ts1 ++ fake)
    | otherwise = do kRecordError (TooManyTySynParams x (paramHave-paramNeed))
                     return (take paramNeed ts1)
    where paramHave = length ts1
          paramNeed = length as



  checkModuleParamUse a =
    do let ty = tpVar (mtpParam a)
       (ts1,k1) <- appTy ts (kindOf ty)
       case k of
         Just ks
           | ks /= k1 -> kRecordError (KindMismatch Nothing ks k1)
         _ -> return ()

       unless (null ts1) $
         panic "Kind.checkTUser.checkModuleParam" [ "Unexpected parameters" ]

       return (TVar ty)

  checkBoundVarUse v =
    do unless (null ts) $ kRecordError TyVarWithParams
       case v of
         TLocalVar t mbk ->
            case k of
              Nothing -> return (TVar (tpVar t))
              Just k1 ->
                case mbk of
                  Nothing -> kSetKind x k1 >> return (TVar (tpVar t))
                  Just k2 -> checkKind (TVar (tpVar t)) k k2
         TOuterVar t -> checkKind (TVar (tpVar t)) k (kindOf t)

  checkScopedVarUse =
    do unless (null ts) (kRecordError TyVarWithParams)
       kExistTVar x $ fromMaybe KNum k

  mcase :: (Name -> KindM (Maybe a)) ->
           (a -> KindM Type) ->
           KindM Type ->
           KindM Type
  mcase m f rest =
    do mb <- m x
       case mb of
         Nothing -> rest
         Just a  -> f a

-- | Check a type-application.
appTy :: [P.Type Name]        -- ^ Parameters to type function
      -> Kind                 -- ^ Kind of type function
      -> KindM ([Type], Kind) -- ^ Validated parameters, resulting kind
appTy [] k1 = return ([],k1)

appTy (t : ts) (k1 :-> k2) =
  do t1      <- doCheckType t (Just k1)
     (ts1,k) <- appTy ts k2
     return (t1 : ts1, k)

appTy ts k1 =
  do kRecordError (TooManyTypeParams (length ts) k1)
     return ([], k1)


-- | Validate a parsed type.
doCheckType :: P.Type Name  -- ^ Type that needs to be checked
          -> Maybe Kind     -- ^ Expected kind (if any)
          -> KindM Type     -- ^ Checked type
doCheckType ty k =
  case ty of
    P.TWild         ->
      do wildOk <- kWildOK
         case wildOk of
           AllowWildCards -> return ()
           NoWildCards    -> kRecordError UnexpectedTypeWildCard
         theKind <- case k of
                      Just k1 -> return k1
                      Nothing -> do kRecordWarning (DefaultingWildType P.KNum)
                                    return KNum
         kNewType TypeWildCard theKind

    P.TFun t1 t2    -> tcon (TC TCFun)                 [t1,t2] k
    P.TSeq t1 t2    -> tcon (TC TCSeq)                 [t1,t2] k
    P.TBit          -> tcon (TC TCBit)                 [] k
    P.TNum n        -> tcon (TC (TCNum n))             [] k
    P.TChar n       -> tcon (TC (TCNum $ toInteger $ fromEnum n)) [] k

    P.TTuple ts     -> tcon (TC (TCTuple (length ts))) ts k

    P.TRecord fs    -> do t1 <- TRec <$> traverseRecordMap checkF fs
                          checkKind t1 k KType
    P.TLocated t r1 -> kInRange r1 $ doCheckType t k

    P.TUser x ts    -> checkTUser (thing x) ts k

    P.TParens t mb  ->
      do newK <- case (k, cvtK <$> mb) of
                   (Just a, Just b) ->
                      do unless (a == b)
                           (kRecordError (KindMismatch Nothing a b))
                         pure (Just b)
                   (a,b) -> pure (mplus a b)

         doCheckType t newK

    P.TInfix t x _ u-> doCheckType (P.TUser x [t, u]) k

    P.TTyApp _fs    -> do kRecordError BareTypeApp
                          kNewType TypeWildCard KNum

  where
  checkF _nm (rng,v) = kInRange rng $ doCheckType v (Just KType)

-- | Validate a parsed proposition.
checkProp :: P.Prop Name      -- ^ Proposition that need to be checked
          -> KindM Prop -- ^ Checked representation
checkProp (P.CType t) = doCheckType t (Just KProp)


-- | Check that a type has the expected kind.
checkKind :: Type         -- ^ Kind-checked type
          -> Maybe Kind   -- ^ Expected kind (if any)
          -> Kind         -- ^ Inferred kind
          -> KindM Type   -- ^ A type consistent with expectations.
checkKind _ (Just k1) k2
  | k1 /= k2    = do kRecordError (KindMismatch Nothing k1 k2)
                     kNewType TypeErrorPlaceHolder k1
checkKind t _ _ = return t
