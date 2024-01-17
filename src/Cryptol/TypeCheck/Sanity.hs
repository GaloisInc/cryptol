-- |
-- Module      :  Cryptol.TypeCheck.Sanity
-- Copyright   :  (c) 2015-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
{-# Language OverloadedStrings #-}
module Cryptol.TypeCheck.Sanity
  ( tcExpr
  , tcDecls
  , tcModule
  , ProofObligation
  , onlyNonTrivial
  , Error(..)
  , AreSame(..)
  , same
  ) where


import Cryptol.Parser.Position(thing,Range,emptyRange)
import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Subst (apSubst, singleTParamSubst)
import Cryptol.TypeCheck.Monad(InferInput(..))
import Cryptol.ModuleSystem.Name(nameLoc)
import Cryptol.Utils.Ident
import Cryptol.Utils.RecordMap
import Cryptol.Utils.PP

import Data.List (sort)
import qualified Data.Set as Set
import MonadLib
import qualified Control.Applicative as A

import           Data.Map ( Map )
import qualified Data.Map as Map


tcExpr :: InferInput -> Expr -> Either (Range, Error) (Schema, [ ProofObligation ])
tcExpr env e = runTcM env (exprSchema e)

tcDecls :: InferInput -> [DeclGroup] -> Either (Range, Error) [ ProofObligation ]
tcDecls env ds0 = case runTcM env (checkDecls ds0) of
                    Left err     -> Left err
                    Right (_,ps) -> Right ps

tcModule :: InferInput -> Module -> Either (Range, Error) [ ProofObligation ]
tcModule env m = case runTcM env check of
                   Left err -> Left err
                   Right (_,ps) -> Right ps
  where check = foldr withTVar k1 (map mtpParam (Map.elems (mParamTypes m)))
        k1    = foldr withAsmp k2 (map thing (mParamConstraints m))
        k2    = withVars (Map.toList (fmap mvpType (mParamFuns m)))
              $ checkDecls (mDecls m)

onlyNonTrivial :: [ProofObligation] -> [ProofObligation]
onlyNonTrivial = filter (not . trivialProofObligation)

-- | Identify proof obligations that are obviously true.
-- We can filter these to avoid clutter
trivialProofObligation :: ProofObligation -> Bool
trivialProofObligation oblig = pIsTrue goal || simpleEq || goal `elem` asmps
  where
  goal  = sType oblig
  asmps = sProps oblig
  simpleEq = case pIsEqual goal of
               Just (t1,t2) -> t1 == t2
               Nothing      -> False


--------------------------------------------------------------------------------

checkDecls :: [DeclGroup] -> TcM ()
checkDecls decls =
  case decls of
    [] -> return ()
    d : ds -> do xs <- checkDeclGroup d
                 withVars xs (checkDecls ds)

-- | Validate a type, returning its kind.
checkType :: Type -> TcM Kind
checkType ty =
  case ty of
    TUser _ _ t -> checkType t    -- Maybe check synonym too?

    TCon tc ts ->
      do ks <- mapM checkType ts
         checkKind (kindOf tc) ks

    TNewtype nt ts ->
      do ks <- mapM checkType ts
         checkKind (kindOf nt) ks

    TVar tv -> lookupTVar tv

    TRec fs ->
      do forM_ fs $ \t ->
           do k <- checkType t
              unless (k == KType) $ reportError $ KindMismatch KType k
         return KType


  where
  checkKind k [] = case k of
                     _ :-> _  -> reportError $ NotEnoughArgumentsInKind k
                     KProp    -> return k
                     KNum     -> return k
                     KType    -> return k

  checkKind (k1 :-> k2) (k : ks)
    | k == k1   = checkKind k2 ks
    | otherwise = reportError $ KindMismatch k1 k

  checkKind k ks = reportError $ BadTypeApplication k ks


-- | Check that the type is valid, and it has the given kind.
checkTypeIs :: Kind -> Type -> TcM ()
checkTypeIs k ty =
  do k1 <- checkType ty
     unless (k == k1) $ reportError $ KindMismatch k k1

-- | Check that this is a valid schema.
checkSchema :: Schema -> TcM ()
checkSchema (Forall as ps t) = foldr withTVar check as
  where check = do mapM_ (checkTypeIs KProp) ps
                   checkTypeIs KType t

data AreSame = SameIf [Prop]
             | NotSame

areSame :: AreSame
areSame = SameIf []

sameAnd :: AreSame -> AreSame -> AreSame
sameAnd x y =
  case (x,y) of
    (SameIf xs, SameIf ys) -> SameIf (xs ++ ys)
    _                      -> NotSame

sameBool :: Bool -> AreSame
sameBool b = if b then areSame else NotSame

sameTypes :: String -> Type -> Type -> TcM ()
sameTypes msg x y = sameSchemas msg (tMono x) (tMono y)

sameSchemas :: String -> Schema -> Schema -> TcM ()
sameSchemas msg x y =
  case same x y of
    NotSame   -> reportError (TypeMismatch msg x y)
    SameIf ps -> mapM_ proofObligation ps




class Same a where
  same :: a -> a -> AreSame

instance Same a => Same [a] where
  same [] [] = areSame
  same (x : xs) (y : ys) = same x y `sameAnd` same xs ys
  same _ _ = NotSame

data Field a b = Field a b

instance (Eq a, Same b) => Same (Field a b) where
  same (Field x a) (Field y b) = sameBool (x == y) `sameAnd` same a b

instance Same Type where
  same t1 t2
    | k1 /= k2    = NotSame
    | k1 == KNum  = if t1 == t2 then SameIf [] else SameIf [ t1 =#= t2 ]
    | otherwise   =
      case (tNoUser t1, tNoUser t2) of
        (TVar x, TVar y)               -> sameBool (x == y)
        (TRec x, TRec y)               -> same (mkRec x) (mkRec y)
        (TNewtype x xs, TNewtype y ys) -> same (Field x xs) (Field y ys)
        (TCon x xs, TCon y ys)         -> same (Field x xs) (Field y ys)
        _                              -> NotSame
      where
      k1 = kindOf t1
      k2 = kindOf t2
      mkRec r = [ Field x y | (x,y) <- canonicalFields r ]

instance Same Schema where
  same (Forall xs ps s) (Forall ys qs t) =
    same xs ys `sameAnd` same ps qs `sameAnd` same s t

instance Same TParam where
  same x y = sameBool (tpName x == tpName y && tpKind x == tpKind y)





--------------------------------------------------------------------------------


-- | Check that the expression is well-formed, and compute its type.
-- Reports an error if the expression is not of a mono type.
exprType :: Expr -> TcM Type
exprType expr =
  do s <- exprSchema expr
     case isMono s of
       Just t  -> return t
       Nothing -> reportError (ExpectedMono s)


-- | Check that the expression is well-formed, and compute its schema.
exprSchema :: Expr -> TcM Schema
exprSchema expr =
  case expr of

    ELocated rng t -> withRange rng (exprSchema t)

    EList es t ->
      do checkTypeIs KType t
         forM_ es $ \e ->
           do t1 <- exprType e
              sameTypes "EList" t1 t

         return $ tMono $ tSeq (tNum (length es)) t

    ETuple es ->
      fmap (tMono . tTuple) (mapM exprType es)

    ERec fs ->
      do fs1 <- traverse exprType fs
         return $ tMono $ TRec fs1

    ESet _ e x v ->
       do ty  <- exprType e
          expe <- checkHas ty x
          has <- exprType v
          sameTypes "ESet" expe has
          return (tMono ty)

    ESel e sel -> do ty <- exprType e
                     ty1 <- checkHas ty sel
                     return (tMono ty1)

    EIf e1 e2 e3 ->
      do ty <- exprType e1
         sameTypes "EIf_condition" tBit ty

         t1 <- exprType e2
         t2 <- exprType e3
         sameTypes "EIf_arms" t1 t2

         return $ tMono t1

-- XXX
--    ECase e as d ->

    EComp len t e mss ->
      do checkTypeIs KNum len
         checkTypeIs KType t

         (xs,ls) <- unzip `fmap` mapM checkArm mss
         -- XXX: check no duplicates
         elT <- withVars (concat xs) $ exprType e

         case ls of
           [] -> return ()
           _  -> convertible (tSeq len t) (tSeq (foldr1 tMin ls) elT)

         return (tMono (tSeq len t))


    EVar x -> lookupVar x

    ETAbs a e     ->
      do Forall as p t <- withTVar a (exprSchema e)
         when (any (== a) as) $
           reportError $ RepeatedVariableInForall a

         return (Forall (a : as) p t)

    ETApp e t ->
      do k <- checkType t
         s <- exprSchema e
         case s of
           Forall (a : as) ps t1 ->
             do let vs = fvs t

                forM_ (map tpVar as) $ \b ->
                  when (b `Set.member` vs) $ reportError $ Captured b

                let k' = kindOf a
                unless (k == k') $ reportError $ KindMismatch k' k

                let su = singleTParamSubst a t
                return $ Forall as (apSubst su ps) (apSubst su t1)

           Forall [] _ _ -> reportError BadInstantiation

    EApp e1 e2 ->
      do t1 <- exprType e1
         t2 <- exprType e2

         case tNoUser t1 of
           TCon (TC TCFun) [ a, b ]
              | SameIf ps <- same a t2 ->
                do mapM_ proofObligation ps
                   return (tMono b)
           tf -> reportError (BadApplication tf t1)


    EAbs x t e    ->
      do checkTypeIs KType t
         res <- withVar x t (exprType e)
         return $ tMono $ tFun t res


    EProofAbs p e ->
      do checkTypeIs KProp p
         withAsmp p $ do Forall as ps t <- exprSchema e
                         return $ Forall as (p : ps) t

    EProofApp e ->
      do Forall as ps t <- exprSchema e
         case (as,ps) of
           ([], p:qs) -> do proofObligation p
                            return (Forall [] qs t)
           ([], _)    -> reportError BadProofNoAbs
           (_,_)      -> reportError (BadProofTyVars as)


    -- XXX: Check that defined things are distinct?
    EWhere e dgs ->
      let go []       = exprSchema e
          go (d : ds) = do xs <- checkDeclGroup d
                           withVars xs (go ds)
      in go dgs


    EPropGuards _guards typ -> 
      pure Forall {sVars = [], sProps = [], sType = typ}

checkHas :: Type -> Selector -> TcM Type
checkHas t sel =
  case sel of

    TupleSel n mb ->

      case tNoUser t of
        TCon (TC (TCTuple sz)) ts ->
          do case mb of
               Just sz1 ->
                 when (sz /= sz1) (reportError (UnexpectedTupleShape sz1 sz))
               Nothing  -> return ()
             unless (n < sz) $ reportError (TupleSelectorOutOfRange n sz)
             return $ ts !! n

        TCon (TC TCSeq) [s,elT] ->
           do res <- checkHas elT sel
              return (TCon (TC TCSeq) [s,res])

        TCon (TC TCFun) [a,b] ->
            do res <- checkHas b sel
               return (TCon (TC TCFun) [a,res])

        _ -> reportError $ BadSelector sel t


    RecordSel f mb ->
      case tNoUser t of
        TRec fs ->

          do case mb of
               Nothing -> return ()
               Just fs1 ->
                 do let ns  = Set.toList (fieldSet fs)
                        ns1 = sort fs1
                    unless (ns == ns1) $
                      reportError $ UnexpectedRecordShape ns1 ns

             case lookupField f fs of
               Nothing -> reportError $ MissingField f $ displayOrder fs
               Just ft -> return ft

        TCon (TC TCSeq) [s,elT] -> do res <- checkHas elT sel
                                      return (TCon (TC TCSeq) [s,res])

        TCon (TC TCFun) [a,b]   -> do res <- checkHas b sel
                                      return (TCon (TC TCFun) [a,res])


        _ -> reportError $ BadSelector sel t


    -- XXX: Remove this?
    ListSel _ mb ->
      case tNoUser t of
        TCon (TC TCSeq) [ n, elT ] ->

          do case mb of
               Nothing  -> return ()
               Just len ->
                 case tNoUser n of
                   TCon (TC (TCNum m)) []
                     | m == toInteger len -> return ()
                   _ -> reportError $ UnexpectedSequenceShape len n

             return elT

        _ -> reportError $ BadSelector sel t




-- | Check if the one type is convertible to the other.
convertible :: Type -> Type -> TcM ()
convertible t1 t2
  | k1 /= k2    = reportError (KindMismatch k1 k2)
  | k1 == KNum  = proofObligation (t1 =#= t2)
  where
  k1 = kindOf t1
  k2 = kindOf t2

convertible t1 t2 = go t1 t2
  where
  go ty1 ty2 =
    let err   = reportError $ TypeMismatch "convertible" (tMono ty1) (tMono ty2)
        other = tNoUser ty2

        goMany [] []             = return ()
        goMany (x : xs) (y : ys) = convertible x y >> goMany xs ys
        goMany _ _               = err

    in case ty1 of
         TUser _ _ s   -> go s ty2

         TVar x        -> case other of
                            TVar y | x == y  -> return ()
                            _                -> err

         TCon tc1 ts1  -> case other of
                            TCon tc2 ts2
                               | tc1 == tc2 -> goMany ts1 ts2
                            _ -> err

         TNewtype nt1 ts1 ->
            case other of
              TNewtype nt2 ts2
                | nt1 == nt2 -> goMany ts1 ts2
              _ -> err

         TRec fs ->
           case other of
             TRec gs ->
               do unless (fieldSet fs == fieldSet gs) err
                  goMany (recordElements fs) (recordElements gs)
             _ -> err


--------------------------------------------------------------------------------

-- | Check a declaration. The boolean indicates if we should check the siganture
checkDecl :: Bool -> Decl -> TcM (Name, Schema)
checkDecl checkSig d =
  case dDefinition d of

    DPrim ->
      do when checkSig $ checkSchema $ dSignature d
         return (dName d, dSignature d)

    DForeign _ me ->
      do when checkSig $ checkSchema $ dSignature d
         mapM_ checkExpr me
         return (dName d, dSignature d)

    DExpr e ->
      do let s = dSignature d
         when checkSig $ checkSchema s
         checkExpr e
         return (dName d, s)

  where
  checkExpr e =
    do let s = dSignature d
       s1 <- exprSchema e
       let nm = dName d
           loc = "definition of " ++ show (pp nm) ++
                          ", at " ++ show (pp (nameLoc nm))
       sameSchemas loc s s1

checkDeclGroup :: DeclGroup -> TcM [(Name, Schema)]
checkDeclGroup dg =
  case dg of
    NonRecursive d -> do x <- checkDecl True d
                         return [x]
    Recursive ds ->
      do xs <- forM ds $ \d ->
                  do checkSchema (dSignature d)
                     return (dName d, dSignature d)
         withVars xs $ mapM (checkDecl False) ds


checkMatch :: Match -> TcM ((Name, Schema), Type)
checkMatch ma =
  case ma of
    From x len elt e ->
      do checkTypeIs KNum len
         checkTypeIs KType elt
         t1 <- exprType e
         case tNoUser t1 of
           TCon (TC TCSeq) [ l, el ]
             | SameIf ps <- same elt el ->
               do mapM_ proofObligation ps
                  return ((x, tMono elt), l)
             | otherwise -> reportError $ TypeMismatch "From" (tMono elt) (tMono el)


           _ -> reportError $ BadMatch t1

    Let d -> do x <- checkDecl True d
                return (x, tNum (1 :: Int))

checkArm :: [Match] -> TcM ([(Name, Schema)], Type)
checkArm []   = reportError EmptyArm
checkArm [m]  = do (x,l) <- checkMatch m
                   return ([x], l)
checkArm (m : ms) =
  do (x, l)   <- checkMatch m
     (xs, l1) <- withVars [x] $ checkArm ms
     let newLen = tMul l l1
     return $ if fst x `elem` map fst xs
                 then (xs, newLen)
                 else (x : xs, newLen)




--------------------------------------------------------------------------------

data RO = RO
  { roTVars   :: Map Int TParam
  , roAsmps   :: [Prop]
  , roRange   :: Range
  , roVars    :: Map Name Schema
  }

type ProofObligation = Schema -- but the type is of kind Prop

data RW = RW
  { woProofObligations :: [ProofObligation]
  }

newtype TcM a = TcM (ReaderT RO (ExceptionT (Range, Error) (StateT RW Id)) a)

instance Functor TcM where
  fmap = liftM

instance A.Applicative TcM where
  pure a = TcM (pure a)
  (<*>) = ap

instance Monad TcM where
  return      = pure
  TcM m >>= f = TcM (do a <- m
                        let TcM m1 = f a
                        m1)

runTcM :: InferInput -> TcM a -> Either (Range, Error) (a, [ProofObligation])
runTcM env (TcM m) =
  case runM m ro rw of
    (Left err, _) -> Left err
    (Right a, s)  -> Right (a, woProofObligations s)
  where
  allPs = inpParams env

  ro = RO { roTVars = Map.fromList [ (tpUnique x, x)
                                      | tp <- Map.elems (mpnTypes allPs)
                                      , let x = mtpParam tp ]
          , roAsmps = map thing (mpnConstraints allPs)
          , roRange = emptyRange
          , roVars  = Map.union
                        (fmap mvpType (mpnFuns allPs))
                        (inpVars env)
          }
  rw = RW { woProofObligations = [] }


data Error =
    TypeMismatch String Schema Schema    -- ^ expected, actual
  | ExpectedMono Schema           -- ^ expected a mono type, got this
  | TupleSelectorOutOfRange Int Int
  | MissingField Ident [Ident]
  | UnexpectedTupleShape Int Int
  | UnexpectedRecordShape [Ident] [Ident]
  | UnexpectedSequenceShape Int Type
  | BadSelector Selector Type
  | BadInstantiation
  | Captured TVar
  | BadProofNoAbs
  | BadProofTyVars [TParam]
  | KindMismatch Kind Kind
  | NotEnoughArgumentsInKind Kind
  | BadApplication Type Type
  | FreeTypeVariable TVar
  | BadTypeApplication Kind [Kind]
  | RepeatedVariableInForall TParam
  | BadMatch Type
  | EmptyArm
  | UndefinedTypeVaraible TVar
  | UndefinedVariable Name
    deriving Show

reportError :: Error -> TcM a
reportError e = TcM $
  do ro <- ask
     raise (roRange ro, e)

withTVar :: TParam -> TcM a -> TcM a
withTVar a (TcM m) = TcM $
  do ro <- ask
     local ro { roTVars = Map.insert (tpUnique a) a (roTVars ro) } m

withRange :: Range -> TcM a -> TcM a
withRange rng (TcM m) = TcM $
  do ro <- ask
     local ro { roRange = rng } m

withAsmp :: Prop -> TcM a -> TcM a
withAsmp p (TcM m) = TcM $
  do ro <- ask
     local ro { roAsmps = p : roAsmps ro } m

withVar :: Name -> Type -> TcM a -> TcM a
withVar x t = withVars [(x,tMono t)]

withVars :: [(Name, Schema)] -> TcM a -> TcM a
withVars xs (TcM m) = TcM $
  do ro <- ask
     local ro { roVars = Map.union (Map.fromList xs) (roVars ro) } m

proofObligation :: Prop -> TcM ()
proofObligation p = TcM $
  do ro <- ask
     sets_ $ \rw -> rw { woProofObligations =
                             Forall (Map.elems (roTVars ro)) (roAsmps ro) p
                           : woProofObligations rw }

lookupTVar :: TVar -> TcM Kind
lookupTVar x =
  case x of
    TVFree {} -> reportError (FreeTypeVariable x)
    TVBound tpv ->
       do let u = tpUnique tpv
              k = tpKind tpv
          ro <- TcM ask
          case Map.lookup u (roTVars ro) of
            Just tp
              | kindOf tp == k  -> return k
              | otherwise       -> reportError $ KindMismatch (kindOf tp) k
            Nothing  -> reportError $ UndefinedTypeVaraible x

lookupVar :: Name -> TcM Schema
lookupVar x =
  do ro <- TcM ask
     case Map.lookup x (roVars ro) of
       Just s -> return s
       Nothing -> reportError $ UndefinedVariable x


instance PP Error where
  ppPrec _ err =
    case err of

      TypeMismatch what expected actual ->
        ppErr ("Type mismatch in" <+> text what)
          [ "Expected:" <+> pp expected
          , "Actual  :" <+> pp actual
          ]

      ExpectedMono s ->
        ppErr "Not a monomorphic type"
          [ pp s ]

      TupleSelectorOutOfRange sel sz ->
        ppErr "Tuple selector out of range"
          [ "Selector:" <+> int sel
          , "Size    :" <+> int sz
          ]

      MissingField f fs ->
        ppErr "Invalid record selector"
          [ "Field: " <+> pp f
          , "Fields:" <+> commaSep (map pp fs)
          ]

      UnexpectedTupleShape expected actual ->
        ppErr "Unexpected tuple shape"
          [ "Expected:" <+> int expected
          , "Actual  :" <+> int actual
          ]

      UnexpectedRecordShape expected actual ->
        ppErr "Unexpected record shape"
          [ "Expected:" <+> commaSep (map pp expected)
          , "Actual  :" <+> commaSep (map pp actual)
          ]

      UnexpectedSequenceShape n t ->
        ppErr "Unexpected sequence shape"
          [ "Expected:" <+> int n
          , "Actual  :" <+> pp t
          ]

      BadSelector sel t ->
        ppErr "Bad selector"
          [ "Selector:" <+> pp sel
          , "Type    :" <+> pp t
          ]

      BadInstantiation ->
        ppErr "Bad instantiation" []

      Captured x ->
        ppErr "Captured type variable"
          [ "Variable:" <+> pp x ]

      BadProofNoAbs ->
        ppErr "Proof application without a proof abstraction" []

      BadProofTyVars xs ->
        ppErr "Proof application with type abstraction"
          [ "Type parameter:" <+> pp x | x <- xs ]

      KindMismatch expected actual ->
        ppErr "Kind mismatch"
          [ "Expected:" <+> pp expected
          , "Actual  :" <+> pp actual
          ]

      NotEnoughArgumentsInKind k ->
        ppErr "Not enough arguments in kind" [ pp k ]

      BadApplication t1 t2 ->
        ppErr "Bad application"
          [ "Function:" <+> pp t1
          , "Argument:" <+> pp t2
          ]

      FreeTypeVariable x ->
        ppErr "Free type variable"
          [ "Variable:" <+> pp x ]

      BadTypeApplication kf ka ->
        ppErr "Bad type application"
          [ "Function :" <+> pp kf
          , "Arguments:" <+> commaSep (map pp ka)
          ]

      RepeatedVariableInForall x ->
        ppErr "Repeated variable in forall"
          [ "Variable:" <+> pp x ]

      BadMatch t ->
        ppErr "Bad match"
          [ "Type:" <+> pp t ]

      EmptyArm -> ppErr "Empty comprehension arm" []

      UndefinedTypeVaraible x ->
        ppErr "Undefined type variable"
          [ "Variable:" <+> pp x ]

      UndefinedVariable x ->
        ppErr "Undefined variable"
          [ "Variable:" <+> pp x ]

    where
    ppErr x ys = hang x 2 (vcat [ "•" <+> y | y <- ys ])
