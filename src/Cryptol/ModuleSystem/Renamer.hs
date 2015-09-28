-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2015 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE CPP #-}

module Cryptol.ModuleSystem.Renamer (
    NamingEnv(), shadowing
  , BindsNames(..), InModule(..), namingEnv'
  , checkNamingEnv
  , shadowNames
  , Rename(..), runRenamer, RenameM()
  , RenamerError(..)
  , RenamerWarning(..)
  , renameVar
  , renameType
  , renameModule
  ) where

import Cryptol.ModuleSystem.Name
import Cryptol.ModuleSystem.NamingEnv
import Cryptol.Prims.Syntax
import Cryptol.Parser.AST
import Cryptol.Parser.Position
import Cryptol.Utils.Ident (packIdent,packInfix)
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.PP

import MonadLib
import qualified Data.Map as Map

import GHC.Generics (Generic)
import Control.DeepSeq

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative(Applicative(..),(<$>))
import Data.Foldable (foldMap)
import Data.Monoid (Monoid(..))
import Data.Traversable (traverse)
#endif


-- Errors ----------------------------------------------------------------------

data RenamerError
  = MultipleSyms (Located PName) [Name]
    -- ^ Multiple imported symbols contain this name

  | UnboundExpr (Located PName)
    -- ^ Expression name is not bound to any definition

  | UnboundType (Located PName)
    -- ^ Type name is not bound to any definition

  | OverlappingSyms [Name]
    -- ^ An environment has produced multiple overlapping symbols

  | ExpectedValue (Located PName)
    -- ^ When a value is expected from the naming environment, but one or more
    -- types exist instead.

  | ExpectedType (Located PName)
    -- ^ When a type is missing from the naming environment, but one or more
    -- values exist with the same name.

  | FixityError (Located Name) (Located Name)
    -- ^ When the fixity of two operators conflict

  | InvalidConstraint (Type PName)
    -- ^ When it's not possible to produce a Prop from a Type.

  | MalformedConstraint (Located (Type PName))
    -- ^ When a constraint appears within another constraint
    deriving (Show,Generic)

instance NFData RenamerError

instance PP RenamerError where
  ppPrec _ e = case e of

    MultipleSyms lqn qns ->
      hang (text "[error] at" <+> pp (srcRange lqn))
         4 $ (text "Multiple definitions for symbol:" <+> pp (thing lqn))
          $$ vcat (map ppLocName qns)

    UnboundExpr lqn ->
      hang (text "[error] at" <+> pp (srcRange lqn))
         4 (text "Value not in scope:" <+> pp (thing lqn))

    UnboundType lqn ->
      hang (text "[error] at" <+> pp (srcRange lqn))
         4 (text "Type not in scope:" <+> pp (thing lqn))

    OverlappingSyms qns ->
      hang (text "[error]")
         4 $ text "Overlapping symbols defined:"
          $$ vcat (map ppLocName qns)

    ExpectedValue lqn ->
      hang (text "[error] at" <+> pp (srcRange lqn))
         4 (fsep [ text "Expected a value named", quotes (pp (thing lqn))
                 , text "but found a type instead"
                 , text "Did you mean `(" <> pp (thing lqn) <> text")?" ])

    ExpectedType lqn ->
      hang (text "[error] at" <+> pp (srcRange lqn))
         4 (fsep [ text "Expected a type named", quotes (pp (thing lqn))
                 , text "but found a value instead" ])

    FixityError o1 o2 ->
      hang (text "[error]")
         4 (fsep [ text "The fixities of", pp o1, text "and", pp o2
                 , text "are not compatible.  "
                 , text "You may use explicit parenthesis to disambiguate" ])

    InvalidConstraint ty ->
      hang (text "[error]" <+> maybe empty (\r -> text "at" <+> pp r) (getLoc ty))
         4 (fsep [ pp ty, text "is not a valid constraint" ])

    MalformedConstraint t ->
      hang (text "[error] at" <+> pp (srcRange t))
         4 (sep [ quotes (pp (thing t))
                , text "is not a valid argument to a constraint" ])

-- Warnings --------------------------------------------------------------------

data RenamerWarning
  = SymbolShadowed Name [Name]
    deriving (Show,Generic)

instance NFData RenamerWarning

instance PP RenamerWarning where
  ppPrec _ (SymbolShadowed new originals) =
    hang (text "[warning] at" <+> loc)
       4 $ fsep [ text "This binding for" <+> sym
                , text "shadows the existing binding" <> plural <+> text "from" ]
        $$ vcat (map pp originals)

    where
    plural | length originals > 1 = char 's'
           | otherwise            = empty

    loc = pp (nameLoc new)
    sym = pp new


-- Renaming Monad --------------------------------------------------------------

data RO = RO
  { roLoc   :: Range
  , roMod   :: !ModName
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
  { unRenameM :: ReaderT RO (WriterT Out SupplyM) a }

instance Monoid a => Monoid (RenameM a) where
  {-# INLINE mempty #-}
  mempty = return mempty

  {-# INLINE mappend #-}
  mappend a b =
    do x <- a
       y <- b
       return (mappend x y)

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

runRenamer :: Supply -> ModName -> NamingEnv -> RenameM a
           -> (Either [RenamerError] (a,Supply),[RenamerWarning])
runRenamer s ns env m = (res,oWarnings out)
  where

  ((a,out),s') = runM (unRenameM m) RO { roLoc = emptyRange
                                       , roNames = env
                                       , roMod = ns
                                       } s

  res | null (oErrors out) = Right (a,s')
      | otherwise          = Left (oErrors out)

record :: RenamerError -> RenameM ()
record err = records [err]

records :: [RenamerError] -> RenameM ()
records errs = RenameM (put mempty { oErrors = errs })

curLoc :: RenameM Range
curLoc  = RenameM (roLoc `fmap` ask)

located :: a -> RenameM (Located a)
located thing =
  do srcRange <- curLoc
     return Located { .. }

withLoc :: HasLoc loc => loc -> RenameM a -> RenameM a
withLoc loc m = RenameM $ case getLoc loc of

  Just range -> do
    ro <- ask
    local ro { roLoc = range } (unRenameM m)

  Nothing -> unRenameM m

-- | Retrieve the name of the current module.
getNS :: RenameM ModName
getNS  = RenameM (roMod `fmap` ask)

-- | Shadow the current naming environment with some more names.
shadowNames :: BindsNames env => env -> RenameM a -> RenameM a
shadowNames names m = RenameM $ do
  env <- inBase (namingEnv names)
  ro  <- ask
  put (checkEnv env (roNames ro))
  let ro' = ro { roNames = env `shadowing` roNames ro }
  local ro' (unRenameM m)

shadowNamesNS :: BindsNames (InModule env) => env -> RenameM a -> RenameM a
shadowNamesNS names m =
  do ns <- getNS
     shadowNames (InModule ns names) m


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
        Just os -> [SymbolShadowed (head ns) os]
    , oErrors   = containsOverlap ns
    }

-- | Check the RHS of a single name rewrite for conflicting sources.
containsOverlap :: [Name] -> [RenamerError]
containsOverlap [_] = []
containsOverlap []  = panic "Renamer" ["Invalid naming environment"]
containsOverlap ns  = [OverlappingSyms ns]

-- | Throw errors for any names that overlap in a rewrite environment.
checkNamingEnv :: NamingEnv -> ([RenamerError],[RenamerWarning])
checkNamingEnv env = (out, [])
  where
  out    = Map.foldr check outTys (neExprs env)
  outTys = Map.foldr check mempty (neTypes env)

  check ns acc = containsOverlap ns ++ acc

supply :: SupplyM a -> RenameM a
supply m = RenameM (inBase m)


-- Renaming --------------------------------------------------------------------

class Rename f where
  rename :: f PName -> RenameM (f Name)

renameModule :: Module PName -> RenameM (NamingEnv,Module Name)
renameModule m =
  do env    <- supply (namingEnv m)
     decls' <- shadowNames env (traverse rename (mDecls m))
     return (env,m { mDecls = decls' })

instance Rename Module where
  rename m =
    do decls' <- shadowNames m (traverse rename (mDecls m))
       return m { mDecls = decls' }

instance Rename TopDecl where
  rename td     = case td of
    Decl d      -> Decl      <$> traverse rename d
    TDNewtype n -> TDNewtype <$> traverse rename n
    Include n   -> return (Include n)

rnLocated :: (a -> RenameM b) -> Located a -> RenameM (Located b)
rnLocated f loc = withLoc loc $
  do a' <- f (thing loc)
     return loc { thing = a' }

instance Rename Decl where
  rename d      = case d of
    DSignature ns sig -> DSignature    <$> traverse (rnLocated renameVar) ns
                                       <*> rename sig
    DPragma ns p      -> DPragma       <$> traverse (rnLocated renameVar) ns
                                       <*> pure p
    DBind b           -> DBind         <$> rename b

    -- XXX we probably shouldn't see these at this point...
    DPatBind pat e    -> do (pe,[pat']) <- renamePats [pat]
                            shadowNames pe (DPatBind pat' <$> rename e)

    DType syn         -> DType         <$> rename syn
    DLocated d' r     -> withLoc r
                       $ DLocated      <$> rename d'  <*> pure r
    DFixity{}         -> panic "Renamer" ["Unexpected fixity declaration"
                                         , show d]

instance Rename Newtype where
  rename n      = do
    name' <- rnLocated renameType (nName n)
    shadowNames (nParams n) $
      do ps'   <- traverse rename (nParams n)
         body' <- traverse (rnNamed rename) (nBody n)
         return Newtype { nName   = name'
                        , nParams = ps'
                        , nBody   = body' }

renameVar :: PName -> RenameM Name
renameVar qn = do
  ro <- RenameM ask
  case Map.lookup qn (neExprs (roNames ro)) of
    Just [n]  -> return n
    Just []   -> panic "Renamer" ["Invalid expression renaming environment"]
    Just syms ->
      do n <- located qn
         record (MultipleSyms n syms)
         return (head syms)

    -- This is an unbound value. Record an error and invent a bogus real name
    -- for it.
    Nothing ->
      do n <- located qn

         case Map.lookup qn (neTypes (roNames ro)) of
           -- types existed with the name of the value expected
           Just _ -> record (ExpectedValue n)

           -- the value is just missing
           Nothing -> record (UnboundExpr n)

         mkFakeName qn

-- | Produce a name if one exists. Note that this includes situations where
-- overlap exists, as it's just a query about anything being in scope. In the
-- event that overlap does exist, an error will be recorded.
typeExists :: PName -> RenameM (Maybe Name)
typeExists pn =
  do ro <- RenameM ask
     case Map.lookup pn (neTypes (roNames ro)) of
       Just [n]  -> return (Just n)
       Just []   -> panic "Renamer" ["Invalid type renaming environment"]
       Just syms -> do n <- located pn
                       record (MultipleSyms n syms)
                       return (Just (head syms))
       Nothing -> return Nothing

renameType :: PName -> RenameM Name
renameType pn =
  do mb <- typeExists pn
     case mb of
       Just n -> return n

       -- This is an unbound value. Record an error and invent a bogus real name
       -- for it.
       Nothing ->
         do ro <- RenameM ask
            let n = Located { srcRange = roLoc ro, thing = pn }

            case Map.lookup pn (neExprs (roNames ro)) of

              -- values exist with the same name, so throw a different error
              Just _ -> record (ExpectedType n)

              -- no terms with the same name, so the type is just unbound
              Nothing -> record (UnboundType n)

            mkFakeName pn

-- | Assuming an error has been recorded already, construct a fake name that's
-- not expected to make it out of the renamer.
mkFakeName :: PName -> RenameM Name
mkFakeName pn = RenameM $
  do ro <- ask
     inBase (liftSupply (mkParameter (getIdent pn) (roLoc ro)))

-- | Rename a schema, assuming that none of its type variables are already in
-- scope.
instance Rename Schema where
  rename s = snd `fmap` renameSchema s

-- | Rename a schema, assuming that the type variables have already been brought
-- into scope.
renameSchema :: Schema PName -> RenameM (NamingEnv,Schema Name)
renameSchema (Forall ps p ty loc) =
  do env <- supply (namingEnv ps)
     s'  <- shadowNames env $ Forall <$> traverse rename ps
                                     <*> traverse rename p
                                     <*> rename ty
                                     <*> pure loc

     return (env,s')

instance Rename TParam where
  rename TParam { .. } =
    do n <- renameType tpName
       return TParam { tpName = n, .. }

instance Rename Prop where
  rename p      = case p of
    CFin t        -> CFin     <$> rename t
    CEqual l r    -> CEqual   <$> rename l  <*> rename r
    CGeq l r      -> CGeq     <$> rename l  <*> rename r
    CArith t      -> CArith   <$> rename t
    CCmp t        -> CCmp     <$> rename t
    CLocated p' r -> withLoc r
                   $ CLocated <$> rename p' <*> pure r

    -- here, we rename the type and then require that it produces something that
    -- looks like a Prop
    CType t -> translateProp =<< resolveTypeFixity t

translateProp :: Type PName -> RenameM (Prop Name)
translateProp ty = go ty
  where
  go t = case t of

    TLocated t' r -> (`CLocated` r) <$> go t'

    -- these are the only cases that will produce valid props.
    TUser n [l,r]
      | i == packIdent "==" -> CEqual <$> rename l <*> rename r
      | i == packIdent ">=" -> CGeq   <$> rename l <*> rename r
      | i == packIdent "<=" -> CGeq   <$> rename r <*> rename l
      where
      i = getIdent n

    -- record an error, but continue renaming to gather any other errors
    _ ->
      do record (InvalidConstraint ty)
         CType <$> rename t


-- | Resolve fixity, then rename the resulting type.
instance Rename Type where
  rename ty0 = go =<< resolveTypeFixity ty0
    where
    go :: Type PName -> RenameM (Type Name)
    go (TFun a b)    = TFun     <$> go a  <*> go b
    go (TSeq n a)    = TSeq     <$> go n  <*> go a
    go  TBit         = return TBit
    go (TNum c)      = return (TNum c)
    go (TChar c)     = return (TChar c)
    go  TInf         = return TInf

    go (TUser pn ps)
      | i == packIdent "inf", null ps     = return TInf
      | i == packIdent "Bit", null ps     = return TBit

      | i == packIdent "min"              = TApp TCMin           <$> traverse go ps
      | i == packIdent "max"              = TApp TCMax           <$> traverse go ps
      | i == packIdent "lengthFromThen"   = TApp TCLenFromThen   <$> traverse go ps
      | i == packIdent "lengthFromThenTo" = TApp TCLenFromThenTo <$> traverse go ps
      | i == packIdent "width"            = TApp TCWidth         <$> traverse go ps

      -- XXX is this case actully needed now?
      -- | i == packIdent "fin" =
      --   do locTy <- located t
      --      record (MalformedConstraint locTy)
      --      n <- mkFakeName pn
      --      TUser n <$> traverse go ps

      where
      i = getIdent pn

    go (TUser qn ps)   = TUser    <$> renameType qn <*> traverse go ps
    go (TApp f xs)     = TApp f   <$> traverse go xs
    go (TRecord fs)    = TRecord  <$> traverse (rnNamed go) fs
    go (TTuple fs)     = TTuple   <$> traverse go fs
    go  TWild          = return TWild
    go (TLocated t' r) = withLoc r (TLocated <$> go t' <*> pure r)

    go (TParens t')    = TParens <$> go t'

    -- at this point, the fixity is correct, and we just need to perform
    -- renaming.
    go (TInfix a o f b) = TInfix <$> rename a
                                 <*> rnLocated renameType o
                                 <*> pure f
                                 <*> rename b


resolveTypeFixity :: Type PName -> RenameM (Type PName)
resolveTypeFixity  = go
  where
  go t = case t of
    TFun a b     -> TFun     <$> go a  <*> go b
    TSeq n a     -> TSeq     <$> go n  <*> go a
    TUser pn ps  -> TUser pn <$> traverse go ps
    TApp f xs    -> TApp f   <$> traverse go xs
    TRecord fs   -> TRecord  <$> traverse (traverse go) fs
    TTuple fs    -> TTuple   <$> traverse go fs

    TLocated t' r-> withLoc r (TLocated <$> go t' <*> pure r)

    TParens t'   -> TParens <$> go t'

    TInfix a o _ b ->
      do let op = lookupFixity o
         a' <- go a
         b' <- go b
         mkTInfix a' op b'

    TBit         -> return t
    TNum _       -> return t
    TChar _      -> return t
    TInf         -> return t
    TWild        -> return t


type TOp = Type PName -> Type PName -> Type PName

infixProps :: [PName]
infixProps  = map (mkUnqual . packInfix) [ "==", ">=", "<=" ]

mkTInfix :: Type PName -> (TOp,Fixity) -> Type PName -> RenameM (Type PName)

-- only if the function is one of props
mkTInfix t@(TUser o1 [x,y]) op@(o2,f2) z
  | o1 `elem` infixProps =
    do let f1 = Fixity NonAssoc 0
       case compareFixity f1 f2 of
         FCLeft  -> return (o2 t z)
         FCRight -> do r <- mkTInfix y op z
                       return (TUser o1 [x,r])

         -- Just reconstruct with the TUser part being an application. If this was
         -- a real error, it will be caught during renaming.
         FCError -> return (o2 t z)

-- In this case, we know the fixities of both sides.
mkTInfix t@(TApp o1 [x,y]) op@(o2,f2) z
  | Just (a1,p1) <- Map.lookup o1 tBinOpPrec =
     case compareFixity (Fixity a1 p1) f2 of
       FCLeft  -> return (o2 t z)
       FCRight -> do r <- mkTInfix y op z
                     return (TApp o1 [x,r])

       -- As the fixity table is known, and this is a case where the fixity came
       -- from that table, it's a real error if the fixities didn't work out.
       FCError -> panic "Renamer" [ "fixity problem for type operators"
                                  , show (o2 t z) ]

mkTInfix (TLocated t _) op z =
     mkTInfix t op z

mkTInfix t (op,_) z =
     return (op t z)


-- | When possible, rewrite the type operator to a known constructor, otherwise
-- return a 'TOp' that reconstructs the original term, and a default fixity.
lookupFixity :: Located PName -> (TOp,Fixity)
lookupFixity op =
  case lkp of
    Just (p,f) -> (\x y -> TApp p [x,y], f)

    -- unknown type operator, just use default fixity
    -- NOTE: this works for the props defined above, as all other operators
    -- are defined with a higher precedence.
    Nothing    -> (\x y -> TUser sym [x,y], Fixity NonAssoc 0)

  where
  sym = thing op
  lkp = do n               <- Map.lookup (thing op) tfunNames
           (fAssoc,fLevel) <- Map.lookup n tBinOpPrec
           return (n,Fixity { .. })

-- | Rename a binding.
instance Rename Bind where
  rename b      = do
    n'    <- rnLocated renameVar (bName b)
    mbSig <- traverse renameSchema (bSignature b)
    shadowNames (fst `fmap` mbSig) $
      do (patEnv,pats') <- renamePats (bParams b)
         e'             <- shadowNames patEnv (rnLocated rename (bDef b))
         return b { bName      = n'
                  , bParams    = pats'
                  , bDef       = e'
                  , bSignature = snd `fmap` mbSig
                  , bPragmas   = bPragmas b
                  }

instance Rename BindDef where
  rename DPrim     = return DPrim
  rename (DExpr e) = DExpr <$> rename e

-- NOTE: this only renames types within the pattern.
instance Rename Pattern where
  rename p      = case p of
    PVar lv         -> PVar <$> rnLocated renameVar lv
    PWild           -> pure PWild
    PTuple ps       -> PTuple   <$> traverse rename ps
    PRecord nps     -> PRecord  <$> traverse (rnNamed rename) nps
    PList elems     -> PList    <$> traverse rename elems
    PTyped p' t     -> PTyped   <$> rename p'    <*> rename t
    PSplit l r      -> PSplit   <$> rename l     <*> rename r
    PLocated p' loc -> withLoc loc
                     $ PLocated <$> rename p'    <*> pure loc

instance Rename Expr where
  rename e = case e of
    EVar n        -> EVar <$> renameVar n
    ELit l        -> return (ELit l)
    ETuple es     -> ETuple  <$> traverse rename es
    ERecord fs    -> ERecord <$> traverse (rnNamed rename) fs
    ESel e' s     -> ESel    <$> rename e' <*> pure s
    EList es      -> EList   <$> traverse rename es
    EFromTo s n e'-> EFromTo <$> rename s
                             <*> traverse rename n
                             <*> traverse rename e'
    EInfFrom a b  -> EInfFrom<$> rename a  <*> traverse rename b
    EComp e' bs   -> do arms' <- traverse renameArm bs
                        let (envs,bs') = unzip arms'
                        shadowNames envs (EComp <$> rename e' <*> pure bs')
    EApp f x      -> EApp    <$> rename f  <*> rename x
    EAppT f ti    -> EAppT   <$> rename f  <*> traverse rename ti
    EIf b t f     -> EIf     <$> rename b  <*> rename t  <*> rename f
    EWhere e' ds  -> do ns <- getNS
                        shadowNames (map (InModule ns) ds) $
                          EWhere <$> rename e' <*> traverse rename ds
    ETyped e' ty  -> ETyped  <$> rename e' <*> rename ty
    ETypeVal ty   -> ETypeVal<$> rename ty
    EFun ps e'    -> do (env,ps') <- renamePats ps
                        shadowNames env (EFun ps' <$> rename e')
    ELocated e' r -> withLoc r
                   $ ELocated <$> rename e' <*> pure r

    EParens p     -> EParens <$> rename p
    EInfix x y _ z-> do op <- renameOp y
                        x' <- rename x
                        z' <- rename z
                        mkEInfix x' op z'

mkEInfix :: Expr Name             -- ^ May contain infix expressions
         -> (Located Name,Fixity) -- ^ The operator to use
         -> Expr Name             -- ^ Will not contain infix expressions
         -> RenameM (Expr Name)

mkEInfix e@(EInfix x o1 f1 y) op@(o2,f2) z =
  case compareFixity f1 f2 of
    FCLeft  -> return (EInfix e o2 f2 z)

    FCRight -> do r <- mkEInfix y op z
                  return (EInfix x o1 f1 r)

    FCError -> do record (FixityError o1 o2)
                  return (EInfix e o2 f2 z)

mkEInfix (ELocated e' _) op z =
     mkEInfix e' op z

mkEInfix e (o,f) z =
     return (EInfix e o f z)


renameOp :: Located PName -> RenameM (Located Name,Fixity)
renameOp ln = withLoc ln $
  do n  <- renameVar (thing ln)
     ro <- RenameM ask
     case Map.lookup n (neFixity (roNames ro)) of
       Just fixity -> return (ln { thing = n },fixity)
       Nothing     -> return (ln { thing = n },defaultFixity)


instance Rename TypeInst where
  rename ti = case ti of
    NamedInst nty -> NamedInst <$> traverse rename nty
    PosInst ty    -> PosInst   <$> rename ty

renameArm :: [Match PName] -> RenameM (NamingEnv,[Match Name])

renameArm (m:ms) =
  do (me,m') <- renameMatch m
     shadowNames me $
       do (env,rest) <- renameArm ms

          -- NOTE: the inner environment shadows the outer one, for examples
          -- like this:
          --
          -- [ x | x <- xs, let x = 10 ]
          return (env `shadowing` me, m':rest)

renameArm [] =
     return (mempty,[])

-- | The name environment generated by a single match.
renameMatch :: Match PName -> RenameM (NamingEnv,Match Name)

renameMatch (Match p e) =
  do (pe,[p']) <- renamePats [p]
     e'        <- rename e
     return (pe,Match p' e')

renameMatch (MatchLet b) =
  do ns <- getNS
     be <- supply (namingEnv (InModule ns b))
     b' <- shadowNames be (rename b)
     return (be,MatchLet b')

-- | Rename patterns, and collect the new environment that they introduce.
renamePats :: [Pattern PName] -> RenameM (NamingEnv,[Pattern Name])
renamePats  = loop
  where
  loop ps = case ps of

    p:rest -> do
      pe <- patternEnv p
      shadowNames pe $
        do p'           <- rename p
           (env',rest') <- loop rest
           return (pe `mappend` env', p':rest')

    [] -> return (mempty, [])

patternEnv :: Pattern PName -> RenameM NamingEnv
patternEnv p0 = go p0
  where
  go (PVar Located { .. }) =
    do n <- supply (liftSupply (mkParameter (getIdent thing) srcRange))
       return (singletonE thing n)

  go PWild            = return mempty
  go (PTuple ps)      = foldMap go ps
  go (PRecord fs)     = foldMap (foldMap go) fs
  go (PList ps)       = foldMap go ps
  go (PTyped p ty)    = go p `mappend` typeEnv ty
  go (PSplit a b)     = go a `mappend` go b
  go (PLocated p loc) = withLoc loc (go p)

  typeEnv (TFun a b) = typeEnv a `mappend` typeEnv b
  typeEnv (TSeq a b) = typeEnv a `mappend` typeEnv b

  typeEnv TBit       = return mempty
  typeEnv TNum{}     = return mempty
  typeEnv TChar{}    = return mempty
  typeEnv TInf       = return mempty

  typeEnv (TUser pn ps) =
    do mb <- typeExists pn
       case mb of

         -- The type is already bound, don't introduce anything.
         Just _ -> foldMap typeEnv ps

         Nothing
           -- The type isn't bound, and has no parameters, so it names a portion
           -- of the type of the pattern.
           | null ps ->
             do loc <- curLoc
                n   <- supply (liftSupply (mkParameter (getIdent pn) loc))
                return (singletonT pn n)

           -- This references a type synonym that's not in scope. Record an
           -- error and continue with a made up name.
           | otherwise ->
             do loc <- curLoc
                record (UnboundType (Located loc pn))
                n   <- supply (liftSupply (mkParameter (getIdent pn) loc))
                return (singletonT pn n)

  typeEnv (TApp _ ts)       = foldMap typeEnv ts
  typeEnv (TRecord fs)      = foldMap (foldMap typeEnv) fs
  typeEnv (TTuple ts)       = foldMap typeEnv ts
  typeEnv TWild             = return mempty
  typeEnv (TLocated ty loc) = withLoc loc (typeEnv ty)
  typeEnv (TParens ty)      = typeEnv ty
  typeEnv (TInfix a _ _ b)  = typeEnv a `mappend` typeEnv b

instance Rename Match where
  rename m = case m of
    Match p e  ->                  Match    <$> rename p <*> rename e
    MatchLet b -> shadowNamesNS b (MatchLet <$> rename b)

instance Rename TySyn where
  rename (TySyn n ps ty) =
     shadowNames ps $ TySyn <$> rnLocated renameType n
                            <*> traverse rename ps
                            <*> rename ty


-- Utilities -------------------------------------------------------------------

rnNamed :: (a -> RenameM b) -> Named a -> RenameM (Named b)
rnNamed  = traverse
{-# INLINE rnNamed #-}
