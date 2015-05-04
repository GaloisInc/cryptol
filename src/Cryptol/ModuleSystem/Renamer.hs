-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE FlexibleInstances #-}

module Cryptol.ModuleSystem.Renamer (
    NamingEnv(), shadowing
  , BindsNames(..)
  , checkNamingEnv
  , Rename(..), runRenamer
  , RenamerError(..)
  , RenamerWarning(..)
  ) where

import Cryptol.ModuleSystem.NamingEnv
import Cryptol.Prims.Syntax
import Cryptol.Parser.AST
import Cryptol.Parser.Names (tnamesP)
import Cryptol.Parser.Position
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.PP

import MonadLib
import qualified Data.Map as Map

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative(Applicative(..),(<$>))
import Data.Foldable (foldMap)
import Data.Monoid (Monoid(..))
import Data.Traversable (traverse)
#endif

-- Errors ----------------------------------------------------------------------

data RenamerError
  = MultipleSyms (Located QName) [NameOrigin]
    -- ^ Multiple imported symbols contain this name

  | UnboundExpr (Located QName)
    -- ^ Expression name is not bound to any definition

  | UnboundType (Located QName)
    -- ^ Type name is not bound to any definition

  | OverlappingSyms [NameOrigin]
    -- ^ An environment has produced multiple overlapping symbols

  | ExpectedValue (Located QName)
    -- ^ When a value is expected from the naming environment, but one or more
    -- types exist instead.

  | ExpectedType (Located QName)
    -- ^ When a type is missing from the naming environment, but one or more
    -- values exist with the same name.
    deriving (Show)

instance PP RenamerError where
  ppPrec _ e = case e of

    MultipleSyms lqn qns ->
      hang (text "[error] at" <+> pp (srcRange lqn))
         4 $ (text "Multiple definitions for symbol:" <+> pp (thing lqn))
          $$ vcat (map pp qns)

    UnboundExpr lqn ->
      hang (text "[error] at" <+> pp (srcRange lqn))
         4 (text "Value not in scope:" <+> pp (thing lqn))

    UnboundType lqn ->
      hang (text "[error] at" <+> pp (srcRange lqn))
         4 (text "Type not in scope:" <+> pp (thing lqn))

    OverlappingSyms qns ->
      hang (text "[error]")
         4 $ text "Overlapping symbols defined:"
          $$ vcat (map pp qns)

    ExpectedValue lqn ->
      hang (text "[error] at" <+> pp (srcRange lqn))
         4 (fsep [ text "Expected a value named", quotes (pp (thing lqn))
                 , text "but found a type instead"
                 , text "Did you mean `(" <> pp (thing lqn) <> text")?" ])

    ExpectedType lqn ->
      hang (text "[error] at" <+> pp (srcRange lqn))
         4 (fsep [ text "Expected a type named", quotes (pp (thing lqn))
                 , text "but found a value instead" ])

-- Warnings --------------------------------------------------------------------

data RenamerWarning
  = SymbolShadowed NameOrigin [NameOrigin]
    deriving (Show)

instance PP RenamerWarning where
  ppPrec _ (SymbolShadowed new originals) =
    hang (text "[warning] at" <+> loc)
       4 $ fsep [ text "This binding for" <+> sym
                , text "shadows the existing binding" <> plural <+> text "from" ]
        $$ vcat (map pp originals)

    where
    plural | length originals > 1 = char 's'
           | otherwise            = empty

    (loc,sym) = case new of
                  Local lqn   -> (pp (srcRange lqn), pp (thing lqn))
                  Imported qn -> (empty, pp qn)


-- Renaming Monad --------------------------------------------------------------

data RO = RO
  { roLoc   :: Range
  , roNames :: NamingEnv
  }

data Out = Out
  { oWarnings :: [RenamerWarning]
  , oErrors   :: [RenamerError]
  } deriving (Show)

instance Monoid Out where
  mempty      = Out [] []
  mappend l r = Out (oWarnings l `mappend` oWarnings r)
                    (oErrors   l `mappend` oErrors   r)

newtype RenameM a = RenameM
  { unRenameM :: ReaderT RO (WriterT Out Id) a }

instance Functor RenameM where
  {-# INLINE fmap #-}
  fmap f m      = RenameM (fmap f (unRenameM m))

instance Applicative RenameM where
  {-# INLINE pure #-}
  pure x        = RenameM (pure x)

  {-# INLINE (<*>) #-}
  l <*> r       = RenameM (unRenameM l <*> unRenameM r)

instance Monad RenameM where
  {-# INLINE return #-}
  return x      = RenameM (return x)

  {-# INLINE (>>=) #-}
  m >>= k       = RenameM (unRenameM m >>= unRenameM . k)

runRenamer :: NamingEnv -> RenameM a
           -> (Either [RenamerError] a,[RenamerWarning])
runRenamer env m = (res,oWarnings out)
  where

  (a,out) = runM (unRenameM m) RO { roLoc = emptyRange, roNames = env }

  res | null (oErrors out) = Right a
      | otherwise          = Left (oErrors out)

record :: RenamerError -> RenameM ()
record err = records [err]

records :: [RenamerError] -> RenameM ()
records errs = RenameM (put mempty { oErrors = errs })

located :: a -> RenameM (Located a)
located a = RenameM $ do
  ro <- ask
  return Located { srcRange = roLoc ro, thing = a }

withLoc :: HasLoc loc => loc -> RenameM a -> RenameM a
withLoc loc m = RenameM $ case getLoc loc of

  Just range -> do
    ro <- ask
    local ro { roLoc = range } (unRenameM m)

  Nothing -> unRenameM m

-- | Shadow the current naming environment with some more names.
shadowNames :: BindsNames env => env -> RenameM a -> RenameM a
shadowNames names m = RenameM $ do
  let env = namingEnv names
  ro <- ask
  put (checkEnv env (roNames ro))
  let ro' = ro { roNames = env `shadowing` roNames ro }
  local ro' (unRenameM m)

-- | Generate warnings when the left environment shadows things defined in
-- the right.  Additionally, generate errors when two names overlap in the
-- left environment.
checkEnv :: NamingEnv -> NamingEnv -> Out
checkEnv l r = Map.foldlWithKey (step neExprs) mempty (neExprs l)
     `mappend` Map.foldlWithKey (step neTypes) mempty (neTypes l)
  where

  step prj acc k ns = acc `mappend` mempty
    { oWarnings = case Map.lookup k (prj r) of
        Nothing -> []
        Just os -> [SymbolShadowed (origin (head ns)) (map origin os)]
    , oErrors   = containsOverlap ns
    }

-- | Check the RHS of a single name rewrite for conflicting sources.
containsOverlap :: HasQName a => [a] -> [RenamerError]
containsOverlap [_] = []
containsOverlap []  = panic "Renamer" ["Invalid naming environment"]
containsOverlap ns  = [OverlappingSyms (map origin ns)]

-- | Throw errors for any names that overlap in a rewrite environment.
checkNamingEnv :: NamingEnv -> ([RenamerError],[RenamerWarning])
checkNamingEnv env = (out, [])
  where
  out    = Map.foldr check outTys (neExprs env)
  outTys = Map.foldr check mempty (neTypes env)

  check ns acc = containsOverlap ns ++ acc


-- Renaming --------------------------------------------------------------------

class Rename a where
  rename :: a -> RenameM a

instance Rename a => Rename [a] where
  rename        = traverse rename

instance Rename a => Rename (Maybe a) where
  rename        = traverse rename

instance Rename a => Rename (Located a) where
  rename loc    = withLoc loc $ do
    a' <- rename (thing loc)
    return loc { thing = a' }

instance Rename a => Rename (Named a) where
  rename n      = do
    a' <-rename (value n)
    return n { value = a' }

instance Rename Module where
  rename m      = do
    decls' <- rename (mDecls m)
    return m { mDecls = decls' }

instance Rename TopDecl where
  rename td     = case td of
    Decl d      -> Decl      <$> rename d
    TDNewtype n -> TDNewtype <$> rename n
    Include{}   -> return td

instance Rename a => Rename (TopLevel a) where
  rename tl     = do
    a' <- rename (tlValue tl)
    return tl { tlValue = a' }

instance Rename Decl where
  rename d      = case d of
    DSignature ns sig -> DSignature ns <$> rename sig
    DPragma ns p      -> DPragma ns    <$> rename p
    DBind b           -> DBind         <$> rename b
    DPatBind pat e    -> DPatBind pat  <$> shadowNames (namingEnv pat) (rename e)
    DType syn         -> DType         <$> rename syn
    DLocated d' r     -> withLoc r
                       $ DLocated      <$> rename d'  <*> pure r

instance Rename Newtype where
  rename n      = do
    name' <- renameLoc renameType (nName n)
    body' <- shadowNames (nParams n) (rename (nBody n))
    return Newtype { nName   = name'
                   , nParams = nParams n
                   , nBody   = body' }

renameExpr :: QName -> RenameM QName
renameExpr qn = do
  ro <- RenameM ask
  case Map.lookup qn (neExprs (roNames ro)) of
    Just [en] -> return (qname en)
    Just []   -> panic "Renamer" ["Invalid expression renaming environment"]
    Just syms ->
      do n <- located qn
         record (MultipleSyms n (map origin syms))
         return qn
    Nothing   ->
      do n <- located qn

         case Map.lookup qn (neTypes (roNames ro)) of
           -- types existed with the name of the value expected
           Just _ -> record (ExpectedValue n)

           -- the value is just missing
           Nothing -> record (UnboundExpr n)
         return qn

renameType :: QName -> RenameM QName
renameType qn = do
  ro <- RenameM ask
  case Map.lookup qn (neTypes (roNames ro)) of
    Just [tn] -> return (qname tn)
    Just []   -> panic "Renamer" ["Invalid type renaming environment"]
    Just syms ->
      do n <- located qn
         record (MultipleSyms n (map origin syms))
         return qn
    Nothing   ->
      do n <- located qn

         case Map.lookup qn (neExprs (roNames ro)) of

           -- values exist with the same name, so throw a different error
           Just _ -> record (ExpectedType n)

           -- no terms with the same name, so the type is just unbound
           Nothing -> record (UnboundType n)

         return qn

-- | Rename a schema, assuming that none of its type variables are already in
-- scope.
instance Rename Schema where
  rename s@(Forall ps _ _ _) = shadowNames ps (renameSchema s)

-- | Rename a schema, assuming that the type variables have already been brought
-- into scope.
renameSchema :: Schema -> RenameM Schema
renameSchema (Forall ps p ty loc) = Forall ps <$> rename p <*> rename ty
                                              <*> pure loc

instance Rename Prop where
  rename p      = case p of
    CFin t        -> CFin     <$> rename t
    CEqual l r    -> CEqual   <$> rename l  <*> rename r
    CGeq l r      -> CGeq     <$> rename l  <*> rename r
    CArith t      -> CArith   <$> rename t
    CCmp t        -> CCmp     <$> rename t
    CLocated p' r -> withLoc r
                   $ CLocated <$> rename p' <*> pure r

instance Rename Type where
  rename t      = case t of
    TFun a b     -> TFun     <$> rename a  <*> rename b
    TSeq n a     -> TSeq     <$> rename n  <*> rename a
    TBit         -> return t
    TNum _       -> return t
    TChar _      -> return t
    TInf         -> return t

    TUser (QName Nothing (Name "width")) ps
                 -> TApp TCWidth <$> rename ps

    TUser qn ps  -> TUser    <$> renameType qn <*> rename ps
    TApp f xs    -> TApp f   <$> rename xs
    TRecord fs   -> TRecord  <$> rename fs
    TTuple fs    -> TTuple   <$> rename fs
    TWild        -> return t
    TLocated t' r -> withLoc r
                 $ TLocated <$> rename t' <*> pure r

instance Rename Pragma where
  rename p      = case p of
    PragmaNote _   -> return p
    PragmaProperty -> return p

-- | The type renaming environment generated by a binding.
bindingTypeEnv :: Bind -> NamingEnv
bindingTypeEnv b = patParams `shadowing` sigParams
  where
  -- type parameters
  sigParams = namingEnv (bSignature b)

  -- pattern type parameters
  patParams   = foldMap (foldMap qualType . tnamesP) (bParams b)
  qualType qn = singletonT qn (TFromParam qn)

-- | Rename a binding.
--
-- NOTE: this does not bind its own name into the naming context of its body.
-- The assumption here is that this has been done by the enclosing environment,
-- to allow for top-level renaming
instance Rename Bind where
  rename b      = do
    n' <- renameLoc renameExpr (bName b)
    shadowNames (bindingTypeEnv b) $ do
      (patenv,pats') <- renamePats (bParams b)
      sig'           <- traverse renameSchema (bSignature b)
      shadowNames patenv $
        do e'   <- rename (bDef b)
           p'   <- rename (bPragmas b)
           return b { bName      = n'
                    , bParams    = pats'
                    , bDef       = e'
                    , bSignature = sig'
                    , bPragmas   = p'
                    }

-- NOTE: this only renames types within the pattern.
instance Rename Pattern where
  rename p      = case p of
    PVar _          -> pure p
    PWild           -> pure p
    PTuple ps       -> PTuple   <$> rename ps
    PRecord nps     -> PRecord  <$> rename nps
    PList elems     -> PList    <$> rename elems
    PTyped p' t     -> PTyped   <$> rename p'    <*> rename t
    PSplit l r      -> PSplit   <$> rename l     <*> rename r
    PLocated p' loc -> withLoc loc
                     $ PLocated <$> rename p'    <*> pure loc

instance Rename Expr where
  rename e = case e of
    EVar n        -> EVar    <$> renameExpr n
    ECon _        -> return e
    ELit _        -> return e
    ETuple es     -> ETuple  <$> rename es
    ERecord fs    -> ERecord <$> rename fs
    ESel e' s     -> ESel    <$> rename e' <*> pure s
    EList es      -> EList   <$> rename es
    EFromTo s n e'-> EFromTo <$> rename s  <*> rename n  <*> rename e'
    EInfFrom a b  -> EInfFrom<$> rename a  <*> rename b
    EComp e' bs   -> do bs' <- mapM renameMatch bs
                        shadowNames (namingEnv bs')
                            (EComp <$> rename e' <*> pure bs')
    EApp f x      -> EApp    <$> rename f  <*> rename x
    EAppT f ti    -> EAppT   <$> rename f  <*> rename ti
    EIf b t f     -> EIf     <$> rename b  <*> rename t  <*> rename f
    EWhere e' ds  -> shadowNames ds (EWhere <$> rename e' <*> rename ds)
    ETyped e' ty  -> ETyped  <$> rename e' <*> rename ty
    ETypeVal ty   -> ETypeVal<$> rename ty
    EFun ps e'    -> do ps' <- rename ps
                        shadowNames ps' (EFun ps' <$> rename e')
    ELocated e' r -> withLoc r
                   $ ELocated <$> rename e' <*> pure r

instance Rename TypeInst where
  rename ti = case ti of
    NamedInst nty -> NamedInst <$> rename nty
    PosInst ty    -> PosInst   <$> rename ty

renameMatch :: [Match] -> RenameM [Match]
renameMatch  = loop
  where
  loop ms = case ms of

    m:rest -> do
      m' <- rename m
      (m':) <$> shadowNames m' (loop rest)

    [] -> return []

renamePats :: [Pattern] -> RenameM (NamingEnv,[Pattern])
renamePats  = loop
  where
  loop ps = case ps of

    p:rest -> do
      p' <- rename p
      let pe = namingEnv p'
      (env',rest') <- loop rest
      return (pe `mappend` env', p':rest')

    [] -> return (mempty, [])

instance Rename Match where
  rename m = case m of
    Match p e  ->                Match    <$> rename p <*> rename e
    MatchLet b -> shadowNames b (MatchLet <$> rename b)

instance Rename TySyn where
  rename (TySyn n ps ty) =
     shadowNames ps (TySyn <$> renameLoc renameType n <*> pure ps <*> rename ty)

renameLoc :: (a -> RenameM a) -> Located a -> RenameM (Located a)
renameLoc by loc = do
  a' <- by (thing loc)
  return loc { thing = a' }
