-- |
-- Module      :  Cryptol.TypeCheck.Sanity
-- Copyright   :  (c) 2015-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
module Cryptol.TypeCheck.Sanity
  ( tcExpr
  , tcDecls
  , tcModule
  , ProofObligation
  , Error(..)
  , same
  ) where


import Cryptol.Parser.Position(thing)
import Cryptol.TypeCheck.AST
import Cryptol.TypeCheck.Subst (apSubst, singleSubst)
import Cryptol.TypeCheck.Monad(InferInput(..))
import Cryptol.Utils.Ident

import qualified Data.Set as Set
import Data.List (sort, sortBy)
import Data.Function (on)
import MonadLib
import qualified Control.Applicative as A

import           Data.Map ( Map )
import qualified Data.Map as Map


tcExpr :: InferInput -> Expr -> Either Error (Schema, [ ProofObligation ])
tcExpr env e = runTcM env (exprSchema e)

tcDecls :: InferInput -> [DeclGroup] -> Either Error [ ProofObligation ]
tcDecls env ds0 = case runTcM env (checkDecls ds0) of
                    Left err     -> Left err
                    Right (_,ps) -> Right ps

tcModule :: InferInput -> Module -> Either Error [ ProofObligation ]
tcModule env m = case runTcM env check of
                   Left err -> Left err
                   Right (_,ps) -> Right ps
  where check = foldr withTVar k1 (map mtpParam (Map.elems (mParamTypes m)))
        k1    = foldr withAsmp k2 (map thing (mParamConstraints m))
        k2    = withVars (Map.toList (fmap mvpType (mParamFuns m)))
              $ checkDecls (mDecls m)


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

    TVar tv -> lookupTVar tv

    TRec fs ->
      do forM_ fs $ \(_,t) ->
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


class Same a where
  same :: a -> a -> Bool

instance Same a => Same [a] where
  same [] [] = True
  same (x : xs) (y : ys) = same x y && same xs ys
  same _ _ = False

instance Same Type where
  same t1 t2 = tNoUser t1 == tNoUser t2

instance Same Schema where
  same (Forall xs ps s) (Forall ys qs t) = same xs ys && same ps qs && same s t

instance Same TParam where
  same x y = tpName x == tpName y && tpKind x == tpKind y





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

    EList es t ->
      do checkTypeIs KType t
         forM_ es $ \e ->
           do t1 <- exprType e
              unless (same t1 t) $
                reportError $ TypeMismatch "EList" (tMono t) (tMono t1)

         return $ tMono $ tSeq (tNum (length es)) t

    ETuple es ->
      fmap (tMono . tTuple) (mapM exprType es)

    ERec fs ->
      do fs1 <- forM fs $ \(f,e) -> do t <- exprType e
                                       return (f,t)
         return $ tMono $ TRec fs1

    ESet e x v -> do ty  <- exprType e
                     expe <- checkHas ty x
                     has <- exprType v
                     unless (same expe has) $
                        reportError $
                          TypeMismatch "ESet" (tMono expe) (tMono has)
                     return (tMono ty)

    ESel e sel -> do ty <- exprType e
                     ty1 <- checkHas ty sel
                     return (tMono ty1)

    EIf e1 e2 e3 ->
      do ty <- exprType e1
         unless (same tBit ty) $
           reportError $ TypeMismatch "EIf_condition" (tMono tBit) (tMono ty)

         t1 <- exprType e2
         t2 <- exprType e3
         unless (same t1 t2) $
           reportError $ TypeMismatch "EIf_arms" (tMono t1) (tMono t2)

         return $ tMono t1

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

                let su = singleSubst (tpVar a) t
                return $ Forall as (apSubst su ps) (apSubst su t1)

           Forall [] _ _ -> reportError BadInstantiation

    EApp e1 e2 ->
      do t1 <- exprType e1
         t2 <- exprType e2

         case tNoUser t1 of
           TCon (TC TCFun) [ a, b ]
              | same a t2 -> return (tMono b)
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
                 do let ns  = sort (map fst fs)
                        ns1 = sort fs1
                    unless (ns == ns1) $
                      reportError $ UnexpectedRecordShape ns1 ns

             case lookup f fs of
               Nothing -> reportError $ MissingField f $ map fst fs
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

         TRec fs ->
           case other of
             TRec gs ->
               do let order = sortBy (compare `on` fst)
                      fs1   = order fs
                      gs1   = order gs
                  unless (map fst fs1 == map fst gs1) err
                  goMany (map snd fs1) (map snd gs1)
             _ -> err


--------------------------------------------------------------------------------

-- | Check a declaration. The boolean indicates if we should check the siganture
checkDecl :: Bool -> Decl -> TcM (Name, Schema)
checkDecl checkSig d =
  case dDefinition d of

    DPrim ->
      do when checkSig $ checkSchema $ dSignature d
         return (dName d, dSignature d)

    DExpr e ->
      do let s = dSignature d
         when checkSig $ checkSchema s
         s1 <- exprSchema e
         unless (same s s1) $
           reportError $ TypeMismatch "DExpr" s s1
         return (dName d, s)

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
             | same elt el -> return ((x, tMono elt), l)
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
  , roVars    :: Map Name Schema
  }

type ProofObligation = Schema -- but the type is of kind Prop

data RW = RW
  { woProofObligations :: [ProofObligation]
  }

newtype TcM a = TcM (ReaderT RO (ExceptionT Error (StateT RW Id)) a)

instance Functor TcM where
  fmap = liftM

instance A.Applicative TcM where
  pure  = return
  (<*>) = ap

instance Monad TcM where
  return a    = TcM (return a)
  fail x      = TcM (fail x)
  TcM m >>= f = TcM (do a <- m
                        let TcM m1 = f a
                        m1)

runTcM :: InferInput -> TcM a -> Either Error (a, [ProofObligation])
runTcM env (TcM m) =
  case runM m ro rw of
    (Left err, _) -> Left err
    (Right a, s)  -> Right (a, woProofObligations s)
  where
  ro = RO { roTVars = Map.fromList [ (tpUnique x, x)
                                      | tp <- Map.elems (inpParamTypes env)
                                      , let x = mtpParam tp ]
          , roAsmps = map thing (inpParamConstraints env)
          , roVars  = Map.union
                        (fmap mvpType (inpParamFuns env))
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
reportError e = TcM (raise e)

withTVar :: TParam -> TcM a -> TcM a
withTVar a (TcM m) = TcM $
  do ro <- ask
     local ro { roTVars = Map.insert (tpUnique a) a (roTVars ro) } m

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
