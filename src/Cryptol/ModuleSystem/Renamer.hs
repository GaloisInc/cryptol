-- |
-- Module      :  Cryptol.ModuleSystem.Renamer
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
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
import Cryptol.ModuleSystem.Exports
import Cryptol.Parser.AST
import Cryptol.Parser.Position
import Cryptol.Parser.Selector(ppNestedSels,selName)
import Cryptol.Utils.Panic (panic)
import Cryptol.Utils.PP

import Data.List(find)
import Data.Maybe (fromMaybe)
import qualified Data.Foldable as F
import           Data.Map.Strict ( Map )
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import qualified Data.Semigroup as S
import qualified Data.Set as Set
import           MonadLib hiding (mapM, mapM_)

import GHC.Generics (Generic)
import Control.DeepSeq

import Prelude ()
import Prelude.Compat

-- Errors ----------------------------------------------------------------------

data RenamerError
  = MultipleSyms (Located PName) [Name] NameDisp
    -- ^ Multiple imported symbols contain this name

  | UnboundExpr (Located PName) NameDisp
    -- ^ Expression name is not bound to any definition

  | UnboundType (Located PName) NameDisp
    -- ^ Type name is not bound to any definition

  | OverlappingSyms [Name] NameDisp
    -- ^ An environment has produced multiple overlapping symbols

  | ExpectedValue (Located PName) NameDisp
    -- ^ When a value is expected from the naming environment, but one or more
    -- types exist instead.

  | ExpectedType (Located PName) NameDisp
    -- ^ When a type is missing from the naming environment, but one or more
    -- values exist with the same name.

  | FixityError (Located Name) Fixity (Located Name) Fixity NameDisp
    -- ^ When the fixity of two operators conflict

  | InvalidConstraint (Type PName) NameDisp
    -- ^ When it's not possible to produce a Prop from a Type.

  | MalformedBuiltin (Type PName) PName NameDisp
    -- ^ When a builtin type/type-function is used incorrectly.

  | BoundReservedType PName (Maybe Range) Doc NameDisp
    -- ^ When a builtin type is named in a binder.

  | OverlappingRecordUpdate (Located [Selector]) (Located [Selector]) NameDisp
    -- ^ When record updates overlap (e.g., @{ r | x = e1, x.y = e2 }@)
    deriving (Show, Generic, NFData)

instance PP RenamerError where
  ppPrec _ e = case e of

    MultipleSyms lqn qns disp -> fixNameDisp disp $
      hang (text "[error] at" <+> pp (srcRange lqn))
         4 $ (text "Multiple definitions for symbol:" <+> pp (thing lqn))
          $$ vcat (map ppLocName qns)

    UnboundExpr lqn disp -> fixNameDisp disp $
      hang (text "[error] at" <+> pp (srcRange lqn))
         4 (text "Value not in scope:" <+> pp (thing lqn))

    UnboundType lqn disp -> fixNameDisp disp $
      hang (text "[error] at" <+> pp (srcRange lqn))
         4 (text "Type not in scope:" <+> pp (thing lqn))

    OverlappingSyms qns disp -> fixNameDisp disp $
      hang (text "[error]")
         4 $ text "Overlapping symbols defined:"
          $$ vcat (map ppLocName qns)

    ExpectedValue lqn disp -> fixNameDisp disp $
      hang (text "[error] at" <+> pp (srcRange lqn))
         4 (fsep [ text "Expected a value named", quotes (pp (thing lqn))
                 , text "but found a type instead"
                 , text "Did you mean `(" <.> pp (thing lqn) <.> text")?" ])

    ExpectedType lqn disp -> fixNameDisp disp $
      hang (text "[error] at" <+> pp (srcRange lqn))
         4 (fsep [ text "Expected a type named", quotes (pp (thing lqn))
                 , text "but found a value instead" ])

    FixityError o1 f1 o2 f2 disp -> fixNameDisp disp $
      hang (text "[error] at" <+> pp (srcRange o1) <+> text "and" <+> pp (srcRange o2))
         4 (fsep [ text "The fixities of"
                 , nest 2 $ vcat
                   [ "•" <+> pp (thing o1) <+> parens (pp f1)
                   , "•" <+> pp (thing o2) <+> parens (pp f2) ]
                 , text "are not compatible."
                 , text "You may use explicit parentheses to disambiguate." ])

    InvalidConstraint ty disp -> fixNameDisp disp $
      hang (text "[error]" <+> maybe empty (\r -> text "at" <+> pp r) (getLoc ty))
         4 (fsep [ pp ty, text "is not a valid constraint" ])

    MalformedBuiltin ty pn disp -> fixNameDisp disp $
      hang (text "[error]" <+> maybe empty (\r -> text "at" <+> pp r) (getLoc ty))
         4 (fsep [ text "invalid use of built-in type", pp pn
                 , text "in type", pp ty ])

    BoundReservedType n loc src disp -> fixNameDisp disp $
      hang (text "[error]" <+> maybe empty (\r -> text "at" <+> pp r) loc)
         4 (fsep [ text "built-in type", quotes (pp n), text "shadowed in", src ])

    OverlappingRecordUpdate xs ys disp -> fixNameDisp disp $
      hang "[error] Overlapping record updates:"
         4 (vcat [ ppLab xs, ppLab ys ])
      where
      ppLab as = ppNestedSels (thing as) <+> "at" <+> pp (srcRange as)

-- Warnings --------------------------------------------------------------------

data RenamerWarning
  = SymbolShadowed Name [Name] NameDisp

  | UnusedName Name NameDisp
    deriving (Show, Generic, NFData)

instance PP RenamerWarning where
  ppPrec _ (SymbolShadowed new originals disp) = fixNameDisp disp $
    hang (text "[warning] at" <+> loc)
       4 $ fsep [ text "This binding for" <+> backticks sym
                , text "shadows the existing binding" <.> plural <+>
                  text "at" ]
        $$ vcat (map (pp . nameLoc) originals)

    where
    plural | length originals > 1 = char 's'
           | otherwise            = empty

    loc = pp (nameLoc new)
    sym = pp new

  ppPrec _ (UnusedName x disp) = fixNameDisp disp $
    hang (text "[warning] at" <+> pp (nameLoc x))
       4 (text "Unused name:" <+> pp x)

-- Renaming Monad --------------------------------------------------------------

data RO = RO
  { roLoc   :: Range
  , roMod   :: !ModName
  , roNames :: NamingEnv
  , roDisp  :: !NameDisp
  }

data RW = RW
  { rwWarnings      :: !(Seq.Seq RenamerWarning)
  , rwErrors        :: !(Seq.Seq RenamerError)
  , rwSupply        :: !Supply
  , rwNameUseCount  :: !(Map Name Int)
    -- ^ How many times did we refer to each name.
    -- Used to generate warnings for unused definitions.
  }

newtype RenameM a = RenameM
  { unRenameM :: ReaderT RO (StateT RW Lift) a }

instance S.Semigroup a => S.Semigroup (RenameM a) where
  {-# INLINE (<>) #-}
  a <> b =
    do x <- a
       y <- b
       return (x S.<> y)

instance (S.Semigroup a, Monoid a) => Monoid (RenameM a) where
  {-# INLINE mempty #-}
  mempty = return mempty

  {-# INLINE mappend #-}
  mappend = (S.<>)

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

instance FreshM RenameM where
  liftSupply f = RenameM $ sets $ \ RW { .. } ->
    let (a,s') = f rwSupply
        rw'    = RW { rwSupply = s', .. }
     in a `seq` rw' `seq` (a, rw')

runRenamer :: Supply -> ModName -> NamingEnv -> RenameM a
           -> (Either [RenamerError] (a,Supply),[RenamerWarning])
runRenamer s ns env m = (res, warnUnused ns env ro rw ++ F.toList (rwWarnings rw))
  where
  (a,rw) = runM (unRenameM m) ro
                              RW { rwErrors   = Seq.empty
                                 , rwWarnings = Seq.empty
                                 , rwSupply   = s
                                 , rwNameUseCount = Map.empty
                                 }

  ro = RO { roLoc = emptyRange
          , roNames = env
          , roMod = ns
          , roDisp = neverQualifyMod ns `mappend` toNameDisp env
          }

  res | Seq.null (rwErrors rw) = Right (a,rwSupply rw)
      | otherwise              = Left (F.toList (rwErrors rw))

-- | Record an error.  XXX: use a better name
record :: (NameDisp -> RenamerError) -> RenameM ()
record f = RenameM $
  do RO { .. } <- ask
     RW { .. } <- get
     set RW { rwErrors = rwErrors Seq.|> f roDisp, .. }

-- | Get the source range for wahtever we are currently renaming.
curLoc :: RenameM Range
curLoc  = RenameM (roLoc `fmap` ask)

-- | Annotate something with the current range.
located :: a -> RenameM (Located a)
located thing =
  do srcRange <- curLoc
     return Located { .. }

-- | Do the given computation using the source code range from `loc` if any.
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
shadowNames  = shadowNames' CheckAll

data EnvCheck = CheckAll     -- ^ Check for overlap and shadowing
              | CheckOverlap -- ^ Only check for overlap
              | CheckNone    -- ^ Don't check the environment
                deriving (Eq,Show)

-- | Shadow the current naming environment with some more names. The boolean
-- parameter indicates whether or not to check for shadowing.
shadowNames' :: BindsNames env => EnvCheck -> env -> RenameM a -> RenameM a
shadowNames' check names m = do
  do env <- liftSupply (namingEnv' names)
     RenameM $
       do ro  <- ask
          env' <- sets (checkEnv (roDisp ro) check env (roNames ro))
          let ro' = ro { roNames = env' `shadowing` roNames ro }
          local ro' (unRenameM m)

shadowNamesNS :: BindsNames (InModule env) => env -> RenameM a -> RenameM a
shadowNamesNS names m =
  do ns <- getNS
     shadowNames (InModule ns names) m


-- | Generate warnings when the left environment shadows things defined in
-- the right.  Additionally, generate errors when two names overlap in the
-- left environment.
checkEnv :: NameDisp -> EnvCheck -> NamingEnv -> NamingEnv -> RW -> (NamingEnv,RW)
checkEnv disp check l r rw
  | check == CheckNone = (l',rw)
  | otherwise          = (l',rw'')

  where

  l' = l { neExprs = es, neTypes = ts }

  (rw',es)  = Map.mapAccumWithKey (step neExprs) rw  (neExprs l)
  (rw'',ts) = Map.mapAccumWithKey (step neTypes) rw' (neTypes l)

  step prj acc k ns = (acc', [head ns])
    where
    acc' = acc
      { rwWarnings =
          if check == CheckAll
             then case Map.lookup k (prj r) of
                    Nothing -> rwWarnings acc
                    Just os -> rwWarnings acc Seq.|> SymbolShadowed (head ns) os disp

             else rwWarnings acc
      , rwErrors   = rwErrors acc Seq.>< containsOverlap disp ns
      }

-- | Check the RHS of a single name rewrite for conflicting sources.
containsOverlap :: NameDisp -> [Name] -> Seq.Seq RenamerError
containsOverlap _    [_] = Seq.empty
containsOverlap _    []  = panic "Renamer" ["Invalid naming environment"]
containsOverlap disp ns  = Seq.singleton (OverlappingSyms ns disp)

-- | Throw errors for any names that overlap in a rewrite environment.
checkNamingEnv :: NamingEnv -> ([RenamerError],[RenamerWarning])
checkNamingEnv env = (F.toList out, [])
  where
  out    = Map.foldr check outTys (neExprs env)
  outTys = Map.foldr check mempty (neTypes env)

  disp   = toNameDisp env

  check ns acc = containsOverlap disp ns Seq.>< acc

recordUse :: Name -> RenameM ()
recordUse x = RenameM $ sets_ $ \rw ->
  rw { rwNameUseCount = Map.insertWith (+) x 1 (rwNameUseCount rw) }


warnUnused :: ModName -> NamingEnv -> RO -> RW -> [RenamerWarning]
warnUnused m0 env ro rw =
  map warn
  $ Map.keys
  $ Map.filterWithKey keep
  $ rwNameUseCount rw
  where
  warn x   = UnusedName x (roDisp ro)
  keep k n = n == 1 && isLocal k
  oldNames = fst (visibleNames env)
  isLocal nm = case nameInfo nm of
                 Declared m sys -> sys == UserName &&
                                   m == m0 && nm `Set.notMember` oldNames
                 Parameter  -> True

-- Renaming --------------------------------------------------------------------

class Rename f where
  rename :: f PName -> RenameM (f Name)

renameModule :: Module PName -> RenameM (NamingEnv,Module Name)
renameModule m =
  do env    <- liftSupply (namingEnv' m)
     -- NOTE: we explicitly hide shadowing errors here, by using shadowNames'
     decls' <-  shadowNames' CheckOverlap env (traverse rename (mDecls m))
     let m1 = m { mDecls = decls' }
         exports = modExports m1
     mapM_ recordUse (eTypes exports)
     return (env,m1)

instance Rename TopDecl where
  rename td     = case td of
    Decl d      -> Decl      <$> traverse rename d
    DPrimType d -> DPrimType <$> traverse rename d
    TDNewtype n -> TDNewtype <$> traverse rename n
    Include n   -> return (Include n)
    DParameterFun f  -> DParameterFun  <$> rename f
    DParameterType f -> DParameterType <$> rename f

    DParameterConstraint d -> DParameterConstraint <$> mapM renameLocated d

renameLocated :: Rename f => Located (f PName) -> RenameM (Located (f Name))
renameLocated x =
  do y <- rename (thing x)
     return x { thing = y }

instance Rename PrimType where
  rename pt =
    do x <- rnLocated renameType (primTName pt)
       let (as,ps) = primTCts pt
       (_,cts) <- renameQual as ps $ \as' ps' -> pure (as',ps')
       pure pt { primTCts = cts, primTName = x }

instance Rename ParameterType where
  rename a =
    do n' <- rnLocated renameType (ptName a)
       return a { ptName = n' }

instance Rename ParameterFun where
  rename a =
    do n'   <- rnLocated renameVar (pfName a)
       sig' <- renameSchema (pfSchema a)
       return a { pfName = n', pfSchema = snd sig' }

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
    DPatBind pat e    -> do (pe,pat') <- renamePat pat
                            shadowNames pe (DPatBind pat' <$> rename e)

    DType syn         -> DType         <$> rename syn
    DProp syn         -> DProp         <$> rename syn
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
       Just [n]  -> recordUse n >> return (Just n)
       Just []   -> panic "Renamer" ["Invalid type renaming environment"]
       Just syms -> do n <- located pn
                       mapM_ recordUse syms
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
mkFakeName pn =
  do ro <- RenameM ask
     liftSupply (mkParameter (getIdent pn) (roLoc ro))

-- | Rename a schema, assuming that none of its type variables are already in
-- scope.
instance Rename Schema where
  rename s = snd `fmap` renameSchema s

-- | Rename a schema, assuming that the type variables have already been brought
-- into scope.
renameSchema :: Schema PName -> RenameM (NamingEnv,Schema Name)
renameSchema (Forall ps p ty loc) =
  renameQual ps p $ \ps' p' ->
    do ty' <- rename ty
       pure (Forall ps' p' ty' loc)

-- | Rename a qualified thing.
renameQual :: [TParam PName] -> [Prop PName] ->
              ([TParam Name] -> [Prop Name] -> RenameM a) ->
              RenameM (NamingEnv, a)
renameQual as ps k =
  do env <- liftSupply (namingEnv' as)
     res <- shadowNames env $ do as' <- traverse rename as
                                 ps' <- traverse rename ps
                                 k as' ps'
     pure (env,res)

instance Rename TParam where
  rename TParam { .. } =
    do n <- renameType tpName
       return TParam { tpName = n, .. }

instance Rename Prop where
  rename (CType t) = CType <$> rename t


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

    go (TUser qn ps)   = TUser    <$> renameType qn <*> traverse go ps
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
    TRecord fs   -> TRecord  <$> traverse (traverse go) fs
    TTuple fs    -> TTuple   <$> traverse go fs

    TLocated t' r-> withLoc r (TLocated <$> go t' <*> pure r)

    TParens t'   -> TParens <$> go t'

    TInfix a o _ b ->
      do op <- lookupFixity o
         a' <- go a
         b' <- go b
         mkTInfix a' op b'

    TBit         -> return t
    TNum _       -> return t
    TChar _      -> return t
    TWild        -> return t


type TOp = Type PName -> Type PName -> Type PName

mkTInfix :: Type PName -> (TOp,Fixity) -> Type PName -> RenameM (Type PName)

mkTInfix t op@(o2,f2) z =
  case t of
    TLocated t1 _ -> mkTInfix t1 op z
    TInfix x ln f1 y ->
      doFixity (\a b -> TInfix a ln f1 b) f1 x y

    _ -> return (o2 t z)

  where
  doFixity mk f1 x y =
    case compareFixity f1 f2 of
      FCLeft  -> return (o2 t z)
      FCRight -> do r <- mkTInfix y op z
                    return (mk x r)

      -- As the fixity table is known, and this is a case where the fixity came
      -- from that table, it's a real error if the fixities didn't work out.
      FCError -> panic "Renamer" [ "fixity problem for type operators"
                                 , show (o2 t z) ]



-- | When possible, rewrite the type operator to a known constructor, otherwise
-- return a 'TOp' that reconstructs the original term, and a default fixity.
lookupFixity :: Located PName -> RenameM (TOp, Fixity)
lookupFixity op =
  do n <- renameType sym
     let fi = fromMaybe defaultFixity (nameFixity n)
     return (\x y -> TInfix x op fi y, fi)

  where
  sym = thing op


-- | Rename a binding.
instance Rename Bind where
  rename b      = do
    n'    <- rnLocated renameVar (bName b)
    mbSig <- traverse renameSchema (bSignature b)
    shadowNames (fst `fmap` mbSig) $
      do (patEnv,pats') <- renamePats (bParams b)
         -- NOTE: renamePats will generate warnings, so we don't need to trigger
         -- them again here.
         e'             <- shadowNames' CheckNone patEnv (rnLocated rename (bDef b))
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

-- | Note that after this point the @->@ updates have an explicit function
-- and there are no more nested updates.
instance Rename UpdField where
  rename (UpdField h ls e) =
    -- The plan:
    -- x =  e       ~~~>        x = e
    -- x -> e       ~~~>        x -> \x -> e
    -- x.y = e      ~~~>        x -> { _ | y = e }
    -- x.y -> e     ~~~>        x -> { _ | y -> e }
    case ls of
      l : more ->
       case more of
         [] -> case h of
                 UpdSet -> UpdField UpdSet [l] <$> rename e
                 UpdFun -> UpdField UpdFun [l] <$> rename (EFun [PVar p] e)
                       where
                       p = UnQual . selName <$> last ls
         _ -> UpdField UpdFun [l] <$> rename (EUpd Nothing [ UpdField h more e])
      [] -> panic "rename@UpdField" [ "Empty label list." ]


instance Rename Expr where
  rename expr = case expr of
    EVar n          -> EVar <$> renameVar n
    ELit l          -> return (ELit l)
    ENeg e          -> ENeg    <$> rename e
    EComplement e   -> EComplement
                               <$> rename e
    EGenerate e     -> EGenerate
                               <$> rename e
    ETuple es       -> ETuple  <$> traverse rename es
    ERecord fs      -> ERecord <$> traverse (rnNamed rename) fs
    ESel e' s       -> ESel    <$> rename e' <*> pure s
    EUpd mb fs      -> do checkLabels fs
                          EUpd <$> traverse rename mb <*> traverse rename fs
    EList es        -> EList   <$> traverse rename es
    EFromTo s n e t -> EFromTo <$> rename s
                               <*> traverse rename n
                               <*> rename e
                               <*> traverse rename t
    EInfFrom a b    -> EInfFrom<$> rename a  <*> traverse rename b
    EComp e' bs     -> do arms' <- traverse renameArm bs
                          let (envs,bs') = unzip arms'
                          -- NOTE: renameArm will generate shadowing warnings; we only
                          -- need to check for repeated names across multiple arms
                          shadowNames' CheckOverlap envs (EComp <$> rename e' <*> pure bs')
    EApp f x        -> EApp    <$> rename f  <*> rename x
    EAppT f ti      -> EAppT   <$> rename f  <*> traverse rename ti
    EIf b t f       -> EIf     <$> rename b  <*> rename t  <*> rename f
    EWhere e' ds    -> do ns <- getNS
                          shadowNames (map (InModule ns) ds) $
                            EWhere <$> rename e' <*> traverse rename ds
    ETyped e' ty    -> ETyped  <$> rename e' <*> rename ty
    ETypeVal ty     -> ETypeVal<$> rename ty
    EFun ps e'      -> do (env,ps') <- renamePats ps
                          -- NOTE: renamePats will generate warnings, so we don't
                          -- need to duplicate them here
                          shadowNames' CheckNone env (EFun ps' <$> rename e')
    ELocated e' r   -> withLoc r
                     $ ELocated <$> rename e' <*> pure r

    ESplit e        -> ESplit  <$> rename e
    EParens p       -> EParens <$> rename p
    EInfix x y _ z  -> do op <- renameOp y
                          x' <- rename x
                          z' <- rename z
                          mkEInfix x' op z'


checkLabels :: [UpdField PName] -> RenameM ()
checkLabels = foldM_ check [] . map labs
  where
  labs (UpdField _ ls _) = ls

  check done l =
    do case find (overlap l) done of
         Just l' -> record (OverlappingRecordUpdate (reLoc l) (reLoc l'))
         Nothing -> pure ()
       pure (l : done)

  overlap xs ys =
    case (xs,ys) of
      ([],_)  -> True
      (_, []) -> True
      (x : xs', y : ys') -> same x y && overlap xs' ys'

  same x y =
    case (thing x, thing y) of
      (TupleSel a _, TupleSel b _)   -> a == b
      (ListSel  a _, ListSel  b _)   -> a == b
      (RecordSel a _, RecordSel b _) -> a == b
      _                              -> False

  reLoc xs = (head xs) { thing = map thing xs }


mkEInfix :: Expr Name             -- ^ May contain infix expressions
         -> (Located Name,Fixity) -- ^ The operator to use
         -> Expr Name             -- ^ Will not contain infix expressions
         -> RenameM (Expr Name)

mkEInfix e@(EInfix x o1 f1 y) op@(o2,f2) z =
   case compareFixity f1 f2 of
     FCLeft  -> return (EInfix e o2 f2 z)

     FCRight -> do r <- mkEInfix y op z
                   return (EInfix x o1 f1 r)

     FCError -> do record (FixityError o1 f1 o2 f2)
                   return (EInfix e o2 f2 z)

mkEInfix (ELocated e' _) op z =
     mkEInfix e' op z

mkEInfix e (o,f) z =
     return (EInfix e o f z)


renameOp :: Located PName -> RenameM (Located Name,Fixity)
renameOp ln = withLoc ln $
  do n  <- renameVar (thing ln)
     case nameFixity n of
       Just fixity -> return (ln { thing = n },fixity)
       Nothing     -> return (ln { thing = n },defaultFixity)


instance Rename TypeInst where
  rename ti = case ti of
    NamedInst nty -> NamedInst <$> traverse rename nty
    PosInst ty    -> PosInst   <$> rename ty

renameArm :: [Match PName] -> RenameM (NamingEnv,[Match Name])

renameArm (m:ms) =
  do (me,m') <- renameMatch m
     -- NOTE: renameMatch will generate warnings, so we don't
     -- need to duplicate them here
     shadowNames' CheckNone me $
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
  do (pe,p') <- renamePat p
     e'      <- rename e
     return (pe,Match p' e')

renameMatch (MatchLet b) =
  do ns <- getNS
     be <- liftSupply (namingEnv' (InModule ns b))
     b' <- shadowNames be (rename b)
     return (be,MatchLet b')

-- | Rename patterns, and collect the new environment that they introduce.
renamePat :: Pattern PName -> RenameM (NamingEnv, Pattern Name)
renamePat p =
  do pe <- patternEnv p
     p' <- shadowNames pe (rename p)
     return (pe, p')



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
patternEnv  = go
  where
  go (PVar Located { .. }) =
    do n <- liftSupply (mkParameter (getIdent thing) srcRange)
       return (singletonE thing n)

  go PWild            = return mempty
  go (PTuple ps)      = bindVars ps
  go (PRecord fs)     = bindVars (map value fs)
  go (PList ps)       = foldMap go ps
  go (PTyped p ty)    = go p `mappend` typeEnv ty
  go (PSplit a b)     = go a `mappend` go b
  go (PLocated p loc) = withLoc loc (go p)

  bindVars []     = return mempty
  bindVars (p:ps) =
    do env <- go p
       shadowNames env $
         do rest <- bindVars ps
            return (env `mappend` rest)


  typeEnv (TFun a b) = bindTypes [a,b]
  typeEnv (TSeq a b) = bindTypes [a,b]

  typeEnv TBit       = return mempty
  typeEnv TNum{}     = return mempty
  typeEnv TChar{}    = return mempty

  typeEnv (TUser pn ps) =
    do mb <- typeExists pn
       case mb of

         -- The type is already bound, don't introduce anything.
         Just _ -> bindTypes ps

         Nothing

           -- The type isn't bound, and has no parameters, so it names a portion
           -- of the type of the pattern.
           | null ps ->
             do loc <- curLoc
                n   <- liftSupply (mkParameter (getIdent pn) loc)
                return (singletonT pn n)

           -- This references a type synonym that's not in scope. Record an
           -- error and continue with a made up name.
           | otherwise ->
             do loc <- curLoc
                record (UnboundType (Located loc pn))
                n   <- liftSupply (mkParameter (getIdent pn) loc)
                return (singletonT pn n)

  typeEnv (TRecord fs)      = bindTypes (map value fs)
  typeEnv (TTuple ts)       = bindTypes ts
  typeEnv TWild             = return mempty
  typeEnv (TLocated ty loc) = withLoc loc (typeEnv ty)
  typeEnv (TParens ty)      = typeEnv ty
  typeEnv (TInfix a _ _ b)  = bindTypes [a,b]

  bindTypes [] = return mempty
  bindTypes (t:ts) =
    do env' <- typeEnv t
       shadowNames env' $
         do res <- bindTypes ts
            return (env' `mappend` res)


instance Rename Match where
  rename m = case m of
    Match p e  ->                  Match    <$> rename p <*> rename e
    MatchLet b -> shadowNamesNS b (MatchLet <$> rename b)

instance Rename TySyn where
  rename (TySyn n f ps ty) =
    shadowNames ps $ TySyn <$> rnLocated renameType n
                           <*> pure f
                           <*> traverse rename ps
                           <*> rename ty

instance Rename PropSyn where
  rename (PropSyn n f ps cs) =
    shadowNames ps $ PropSyn <$> rnLocated renameType n
                             <*> pure f
                             <*> traverse rename ps
                             <*> traverse rename cs


-- Utilities -------------------------------------------------------------------

rnNamed :: (a -> RenameM b) -> Named a -> RenameM (Named b)
rnNamed  = traverse
{-# INLINE rnNamed #-}
