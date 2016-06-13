-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable
--
-- The purpose of this module is to convert all patterns to variable
-- patterns.  It also eliminates pattern bindings by de-sugaring them
-- into `Bind`.  Furthermore, here we associate signatures and pragmas
-- with the names to which they belong.

{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RecordWildCards #-}
module Cryptol.Parser.NoPat (RemovePatterns(..),Error(..)) where

import Cryptol.Parser.AST
import Cryptol.Parser.Position(Range(..),emptyRange,start,at)
import Cryptol.Parser.Names (namesP)
import Cryptol.Utils.PP
import Cryptol.Utils.Panic(panic)
import Cryptol.Utils.Color(errorMsg,errorAtMsg)

import           MonadLib hiding (mapM)
import           Data.Maybe(maybeToList)
import           Data.Either(partitionEithers)
import qualified Data.Map as Map

import GHC.Generics (Generic)
import Control.DeepSeq

import Prelude ()
import Prelude.Compat

class RemovePatterns t where
  -- | Eliminate all patterns in a program.
  removePatterns :: t -> (t, [Error])

instance RemovePatterns (Program PName) where
  removePatterns p = runNoPatM (noPatProg p)

instance RemovePatterns (Expr PName) where
  removePatterns e = runNoPatM (noPatE e)

instance RemovePatterns (Module PName) where
  removePatterns m = runNoPatM (noPatModule m)

instance RemovePatterns [Decl PName] where
  removePatterns ds = runNoPatM (noPatDs ds)

simpleBind :: Located PName -> Expr PName -> Bind PName
simpleBind x e = Bind { bName = x, bParams = []
                      , bDef = at e (Located emptyRange (DExpr e))
                      , bSignature = Nothing, bPragmas = []
                      , bMono = True, bInfix = False, bFixity = Nothing
                      , bDoc = Nothing
                      }

sel :: Pattern PName -> PName -> Selector -> Bind PName
sel p x s = let (a,ts) = splitSimpleP p
            in simpleBind a (foldl ETyped (ESel (EVar x) s) ts)

-- | Given a pattern, transform it into a simple pattern and a set of bindings.
-- Simple patterns may only contain variables and type annotations.

-- XXX: We can replace the types in the selcetors with annotations on the bindings.
noPat :: Pattern PName -> NoPatM (Pattern PName, [Bind PName])
noPat pat =
  case pat of
    PVar x -> return (PVar x, [])

    PWild ->
      do x <- newName
         r <- getRange
         return (pVar r x, [])

    PTuple ps ->
      do (as,dss) <- unzip `fmap` mapM noPat ps
         x <- newName
         r <- getRange
         let len      = length ps
             ty       = TTuple (replicate len TWild)
             getN a n = sel a x (TupleSel n (Just len))
         return (pTy r x ty, zipWith getN as [0..] ++ concat dss)

    PList [] ->
      do x <- newName
         r <- getRange
         return (pTy r x (TSeq (TNum 0) TWild), [])

    PList ps ->
      do (as,dss) <- unzip `fmap` mapM noPat ps
         x <- newName
         r <- getRange
         let len      = length ps
             ty       = TSeq (TNum (fromIntegral len)) TWild
             getN a n = sel a x (ListSel n (Just len))
         return (pTy r x ty, zipWith getN as [0..] ++ concat dss)

    PRecord fs ->
      do (as,dss) <- unzip `fmap` mapM (noPat . value) fs
         x <- newName
         r <- getRange
         let shape    = map (thing . name) fs
             ty       = TRecord (map (fmap (\_ -> TWild)) fs)
             getN a n = sel a x (RecordSel n (Just shape))
         return (pTy r x ty, zipWith getN as shape ++ concat dss)

    PTyped p t ->
      do (a,ds) <- noPat p
         return (PTyped a t, ds)

    -- XXX: Ww can do more with type annotations here
    PSplit p1 p2 ->
      do (a1,ds1) <- noPat p1
         (a2,ds2) <- noPat p2
         x <- newName
         tmp <- newName
         r <- getRange
         let prim = EVar (mkUnqual (mkIdent "splitAt"))
             bTmp = simpleBind (Located r tmp) (EApp prim (EVar x))
             b1   = sel a1 tmp (TupleSel 0 (Just 2))
             b2   = sel a2 tmp (TupleSel 1 (Just 2))
         return (pVar r x, bTmp : b1 : b2 : ds1 ++ ds2)

    PLocated p r1 -> inRange r1 (noPat p)

  where
  pVar r x   = PVar (Located r x)
  pTy  r x t = PTyped (PVar (Located r x)) t


splitSimpleP :: Pattern PName -> (Located PName, [Type PName])
splitSimpleP (PVar x)     = (x, [])
splitSimpleP (PTyped p t) = let (x,ts) = splitSimpleP p
                            in (x, t:ts)
splitSimpleP p            = panic "splitSimpleP"
                                  [ "Non-simple pattern", show p ]

--------------------------------------------------------------------------------

noPatE :: Expr PName -> NoPatM (Expr PName)
noPatE expr =
  case expr of
    EVar {}       -> return expr
    ELit {}       -> return expr
    ETuple es     -> ETuple  <$> mapM noPatE es
    ERecord es    -> ERecord <$> mapM noPatF es
    ESel e s      -> ESel    <$> noPatE e <*> return s
    EList es      -> EList   <$> mapM noPatE es
    EFromTo {}    -> return expr
    EInfFrom e e' -> EInfFrom <$> noPatE e <*> traverse noPatE e'
    EComp e mss   -> EComp  <$> noPatE e <*> mapM noPatArm mss
    EApp e1 e2    -> EApp   <$> noPatE e1 <*> noPatE e2
    EAppT e ts    -> EAppT  <$> noPatE e <*> return ts
    EIf e1 e2 e3  -> EIf    <$> noPatE e1 <*> noPatE e2 <*> noPatE e3
    EWhere e ds   -> EWhere <$> noPatE e <*> noPatDs ds
    ETyped e t    -> ETyped <$> noPatE e <*> return t
    ETypeVal {}   -> return expr
    EFun ps e     -> do (ps1,e1) <- noPatFun ps e
                        return (EFun ps1 e1)
    ELocated e r1 -> ELocated <$> inRange r1 (noPatE e) <*> return r1

    EParens e     -> EParens <$> noPatE e
    EInfix x y f z-> EInfix  <$> noPatE x <*> pure y <*> pure f <*> noPatE z

  where noPatF x = do e <- noPatE (value x)
                      return x { value = e }

noPatFun :: [Pattern PName] -> Expr PName -> NoPatM ([Pattern PName], Expr PName)
noPatFun ps e =
  do (xs,bs) <- unzip <$> mapM noPat ps
     e1 <- noPatE e
     let body = case concat bs of
                        [] -> e1
                        ds -> EWhere e1 $ map DBind ds
     return (xs, body)


noPatArm :: [Match PName] -> NoPatM [Match PName]
noPatArm ms = concat <$> mapM noPatM ms

noPatM :: Match PName -> NoPatM [Match PName]
noPatM (Match p e) =
  do (x,bs) <- noPat p
     e1     <- noPatE e
     return (Match x e1 : map MatchLet bs)
noPatM (MatchLet b) = (return . MatchLet) <$> noMatchB b

noMatchB :: Bind PName -> NoPatM (Bind PName)
noMatchB b =
  case thing (bDef b) of

    DPrim | null (bParams b) -> return b
          | otherwise        -> panic "NoPat" [ "noMatchB: primitive with params"
                                              , show b ]

    DExpr e ->
      do (ps,e') <- noPatFun (bParams b) e
         return b { bParams = ps, bDef = DExpr e' <$ bDef b }

noMatchD :: Decl PName -> NoPatM [Decl PName]
noMatchD decl =
  case decl of
    DSignature {}   -> return [decl]
    DPragma {}      -> return [decl]
    DFixity{}       -> return [decl]

    DBind b         -> do b1 <- noMatchB b
                          return [DBind b1]

    DPatBind p e    -> do (p',bs) <- noPat p
                          let (x,ts) = splitSimpleP p'
                          e1 <- noPatE e
                          let e2 = foldl ETyped e1 ts
                          return $ DBind Bind { bName = x
                                              , bParams = []
                                              , bDef = at e (Located emptyRange (DExpr e2))
                                              , bSignature = Nothing
                                              , bPragmas = []
                                              , bMono = False
                                              , bInfix = False
                                              , bFixity = Nothing
                                              , bDoc = Nothing
                                              } : map DBind bs
    DType {}        -> return [decl]

    DLocated d r1   -> do bs <- inRange r1 $ noMatchD d
                          return $ map (`DLocated` r1) bs

noPatDs :: [Decl PName] -> NoPatM [Decl PName]
noPatDs ds =
  do ds1 <- concat <$> mapM noMatchD ds
     let pragmaMap = Map.fromListWith (++) $ concatMap toPragma ds1
         sigMap    = Map.fromListWith (++) $ concatMap toSig ds1
         fixMap    = Map.fromListWith (++) $ concatMap toFixity ds1
     (ds2, (pMap,sMap,fMap,_)) <- runStateT (pragmaMap, sigMap, fixMap, Map.empty)
                                            (annotDs ds1)

     forM_ (Map.toList pMap) $ \(n,ps) ->
       forM_ ps $ \p -> recordError $ PragmaNoBind (p { thing = n }) (thing p)

     forM_ (Map.toList sMap) $ \(n,ss) ->
       do _ <- checkSigs n ss
          forM_ ss $ \s -> recordError $ SignatureNoBind (s { thing = n })
                                                         (thing s)

     forM_ (Map.toList fMap) $ \(n,fs) ->
       forM_ fs $ \f -> recordError $ FixityNoBind f { thing = n }

     return ds2

noPatTopDs :: [TopLevel (Decl PName)] -> NoPatM [TopLevel (Decl PName)]
noPatTopDs tds =
  do noPatGroups <- mapM (noMatchD . tlValue) tds

     let allDecls  = concat noPatGroups
         pragmaMap = Map.fromListWith (++) $ concatMap toPragma allDecls
         sigMap    = Map.fromListWith (++) $ concatMap toSig    allDecls
         fixMap    = Map.fromListWith (++) $ concatMap toFixity allDecls
         docMap    = Map.fromListWith (++) $ concatMap toDocs   tds

     let exportGroups = zipWith (\ td ds -> td { tlValue = ds }) tds noPatGroups
     (tds', (pMap,sMap,fMap,_)) <- runStateT (pragmaMap,sigMap,fixMap,docMap)
                                             (annotTopDs exportGroups)

     forM_ (Map.toList pMap) $ \(n,ps) ->
       forM_ ps $ \p -> recordError $ PragmaNoBind (p { thing = n }) (thing p)

     forM_ (Map.toList sMap) $ \(n,ss) ->
       do _ <- checkSigs n ss
          forM_ ss $ \s -> recordError $ SignatureNoBind (s { thing = n })
                                                         (thing s)

     forM_ (Map.toList fMap) $ \(n,fs) ->
       forM_ fs $ \f -> recordError $ FixityNoBind f { thing = n }

     return tds'


noPatProg :: Program PName -> NoPatM (Program PName)
noPatProg (Program topDs) =
  do let (ds, others) = partitionEithers (map isDecl topDs)
     ds1 <- noPatTopDs ds
     return $ Program $ others ++ map Decl ds1

  where
  isDecl (Decl d) = Left d
  isDecl d        = Right d

noPatModule :: Module PName -> NoPatM (Module PName)
noPatModule m =
  do let (ds, others) = partitionEithers (map isDecl (mDecls m))
     ds1 <- noPatTopDs ds
     return m { mDecls = others ++ map Decl ds1 }

  where
  isDecl (Decl d) = Left d
  isDecl d        = Right d


--------------------------------------------------------------------------------

type AnnotMap = ( Map.Map PName [Located  Pragma       ]
                , Map.Map PName [Located (Schema PName)]
                , Map.Map PName [Located  Fixity       ]
                , Map.Map PName [Located  String       ]
                )

-- | Add annotations to exported declaration groups.
--
-- XXX: This isn't quite right: if a signature and binding have different
-- export specifications, this will favor the specification of the binding.
-- This is most likely the intended behavior, so it's probably fine, but it does
-- smell a bit.
annotTopDs :: [TopLevel [Decl PName]]
           -> StateT AnnotMap NoPatM [TopLevel (Decl PName)]
annotTopDs tds =
  case tds of

    (ds:dss) ->
      do ds'  <- annotDs (tlValue ds)
         rest <- annotTopDs dss
         if null ds'
            then return rest
            else return ([ ds { tlValue = d } | d <- ds' ] ++ rest)

    [] -> return []


-- | Add annotations, keeping track of which annotation are not yet used up.
annotDs :: [Decl PName] -> StateT AnnotMap NoPatM [Decl PName]
annotDs (d : ds) =
  do ignore <- runExceptionT (annotD d)
     case ignore of
       Left ()   -> annotDs ds
       Right d1  -> (d1 :) <$> annotDs ds
annotDs [] = return []

-- | Add annotations, keeping track of which annotation are not yet used up.
-- The exception indicates which declarations are no longer needed.
annotD :: Decl PName -> ExceptionT () (StateT AnnotMap NoPatM) (Decl PName)
annotD decl =
  case decl of
    DBind b       -> DBind <$> lift (annotB b)
    DSignature {} -> raise ()
    DFixity{}     -> raise ()
    DPragma {}    -> raise ()
    DPatBind {}   -> raise ()
    DType {}      -> return decl
    DLocated d r  -> (`DLocated` r) <$> annotD d

-- | Add pragma/signature annotations to a binding.
annotB :: Bind PName -> StateT AnnotMap NoPatM (Bind PName)
annotB Bind { .. } =
  do (ps,ss,fs,ds) <- get
     let name       = thing bName
         remove _ _ = Nothing
     case ( Map.updateLookupWithKey remove name ps
          , Map.updateLookupWithKey remove name ss
          , Map.updateLookupWithKey remove name fs
          , Map.updateLookupWithKey remove name ds
          ) of
           ( (thisPs, pragmas1), (thisSigs, sigs1), (thisFixes, fixes1), (thisDocs, docs1)) ->
                do s <- lift $ checkSigs name (jn thisSigs)
                   f <- lift $ checkFixs name (jn thisFixes)
                   d <- lift $ checkDocs name (jn thisDocs)
                   set (pragmas1,sigs1,fixes1,docs1)
                   return Bind { bSignature = s
                               , bPragmas = map thing (jn thisPs) ++ bPragmas
                               , bFixity = f
                               , bDoc = d
                               , ..
                               }
  where jn x = concat (maybeToList x)

-- | Check for multiple signatures.
checkSigs :: PName -> [Located (Schema PName)] -> NoPatM (Maybe (Schema PName))
checkSigs _ []             = return Nothing
checkSigs _ [s]            = return (Just (thing s))
checkSigs f xs@(s : _ : _) = do recordError $ MultipleSignatures f xs
                                return (Just (thing s))

checkFixs :: PName -> [Located Fixity] -> NoPatM (Maybe Fixity)
checkFixs _ []       = return Nothing
checkFixs _ [f]      = return (Just (thing f))
checkFixs f fs@(x:_) = do recordError $ MultipleFixities f $ map srcRange fs
                          return (Just (thing x))


checkDocs :: PName -> [Located String] -> NoPatM (Maybe String)
checkDocs _ []       = return Nothing
checkDocs _ [d]      = return (Just (thing d))
checkDocs f ds@(d:_) = do recordError $ MultipleDocs f (map srcRange ds)
                          return (Just (thing d))


-- | Does this declaration provide some signatures?
toSig :: Decl PName -> [(PName, [Located (Schema PName)])]
toSig (DLocated d _)      = toSig d
toSig (DSignature xs s)   = [ (thing x,[Located (srcRange x) s]) | x <- xs ]
toSig _                   = []

-- | Does this declaration provide some signatures?
toPragma :: Decl PName -> [(PName, [Located Pragma])]
toPragma (DLocated d _)   = toPragma d
toPragma (DPragma xs s)   = [ (thing x,[Located (srcRange x) s]) | x <- xs ]
toPragma _                = []

-- | Does this declaration provide fixity information?
toFixity :: Decl PName -> [(PName, [Located Fixity])]
toFixity (DFixity f ns) = [ (thing n, [Located (srcRange n) f]) | n <- ns ]
toFixity _              = []

-- | Does this top-level declaration provide a documentation string?
toDocs :: TopLevel (Decl PName) -> [(PName, [Located String])]
toDocs TopLevel { .. }
  | Just txt <- tlDoc = go txt tlValue
  | otherwise = []
  where
  go txt decl =
    case decl of
      DSignature ns _ -> [ (thing n, [txt]) | n <- ns ]
      DFixity _ ns    -> [ (thing n, [txt]) | n <- ns ]
      DBind b         -> [ (thing (bName b), [txt]) ]
      DLocated d _    -> go txt d
      DPatBind p _    -> [ (thing n, [txt]) | n <- namesP p ]

      -- XXX revisit these
      DPragma _ _     -> []
      DType _         -> []


--------------------------------------------------------------------------------
newtype NoPatM a = M { unM :: ReaderT Range (StateT RW Id) a }

data RW     = RW { names :: !Int, errors :: [Error] }

data Error  = MultipleSignatures PName [Located (Schema PName)]
            | SignatureNoBind (Located PName) (Schema PName)
            | PragmaNoBind (Located PName) Pragma
            | MultipleFixities PName [Range]
            | FixityNoBind (Located PName)
            | MultipleDocs PName [Range]
              deriving (Show,Generic, NFData)

instance Functor NoPatM where fmap = liftM
instance Applicative NoPatM where pure = return; (<*>) = ap
instance Monad NoPatM where
  return x  = M (return x)
  fail x    = M (fail x)
  M x >>= k = M (x >>= unM . k)


-- | Pick a new name, to be used when desugaring patterns.
newName :: NoPatM PName
newName = M $ sets $ \s -> let x = names s
                           in (NewName NoPat x, s { names = x + 1 })

-- | Record an error.
recordError :: Error -> NoPatM ()
recordError e = M $ sets_ $ \s -> s { errors = e : errors s }

getRange :: NoPatM Range
getRange = M ask

inRange :: Range -> NoPatM a -> NoPatM a
inRange r m = M $ local r $ unM m


runNoPatM :: NoPatM a -> (a, [Error])
runNoPatM m
  = getErrs
  $ runId
  $ runStateT RW { names = 0, errors = [] }
  $ runReaderT (Range start start "")    -- hm
  $ unM m
  where getErrs (a,rw) = (a, errors rw)

--------------------------------------------------------------------------------

instance PP Error where
  ppPrec _ err =
    case err of
      MultipleSignatures x ss ->
        text (errorMsg ++ "Multiple type signatures for") <+> quotes (pp x)
        $$ nest 2 (vcat (map pp ss))

      SignatureNoBind x s ->
        text errorAtMsg <+> pp (srcRange x) <> colon <+>
        text "Type signature without a matching binding:"
         $$ nest 2 (pp s)

      PragmaNoBind x s ->
        text errorAtMsg <+> pp (srcRange x) <> colon <+>
        text "Pragma without a matching binding:"
         $$ nest 2 (pp s)

      MultipleFixities n locs ->
        text (errorMsg ++ "Multiple fixity declarations for") <+> quotes (pp n)
        $$ nest 2 (vcat (map pp locs))

      FixityNoBind n ->
        text errorAtMsg <+> pp (srcRange n) <> colon <+>
        text "Fixity declaration without a matching binding for:" <+>
         pp (thing n)

      MultipleDocs n locs ->
        text (errorMsg ++ "Multiple documentation blocks given for:") <+> pp n
        $$ nest 2 (vcat (map pp locs))
