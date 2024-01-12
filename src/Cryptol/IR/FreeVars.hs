module Cryptol.IR.FreeVars
  ( FreeVars(..)
  , Deps(..)
  , Defs(..)
  , moduleDeps, transDeps
  ) where

import           Data.Set ( Set )
import qualified Data.Set as Set
import           Data.Map ( Map )
import qualified Data.Map as Map

import Cryptol.TypeCheck.AST
import Cryptol.Utils.RecordMap

data Deps = Deps { valDeps  :: Set Name
                   -- ^ Undefined value names

                 , tyDeps   :: Set Name
                   -- ^ Undefined type names (from newtype)

                 , tyParams :: Set TParam
                   -- ^ Undefined type params (e.d. mod params)
                 } deriving Eq

instance Semigroup Deps where
  d1 <> d2 = mconcat [d1,d2]

instance Monoid Deps where
  mempty = Deps { valDeps   = Set.empty
                , tyDeps    = Set.empty
                , tyParams  = Set.empty
                }

  mappend = (<>)

  mconcat ds = Deps { valDeps   = Set.unions (map valDeps ds)
                    , tyDeps    = Set.unions (map tyDeps  ds)
                    , tyParams  = Set.unions (map tyParams ds)
                    }

rmTParam :: TParam -> Deps -> Deps
rmTParam p x = x { tyParams = Set.delete p (tyParams x) }

rmVal :: Name -> Deps -> Deps
rmVal p x = x { valDeps = Set.delete p (valDeps x) }

rmVals :: Set Name -> Deps -> Deps
rmVals p x = x { valDeps = Set.difference (valDeps x) p }


-- | Compute the transitive closure of the given dependencies.
transDeps :: Map Name Deps -> Map Name Deps
transDeps mp0 = fst
              $ head
              $ dropWhile (uncurry (/=))
              $ zip steps (tail steps)
  where
  step1 mp d = mconcat [ Map.findWithDefault
                            mempty { valDeps = Set.singleton x }
                            x mp | x <- Set.toList (valDeps d) ]
  step mp = fmap (step1 mp) mp

  steps = iterate step mp0

-- | Dependencies of top-level declarations in a module.
-- These are dependencies on module parameters or things
-- defined outside the module.
moduleDeps :: Module -> Map Name Deps
moduleDeps = transDeps . Map.unions . map fromDG . mDecls
  where
  fromDG dg = let vs = freeVars dg
              in Map.fromList [ (x,vs) | x <- Set.toList (defs dg) ]

class FreeVars e where
  freeVars :: e -> Deps


instance FreeVars e => FreeVars [e] where
  freeVars = mconcat . map freeVars


instance FreeVars DeclGroup where
  freeVars dg = case dg of
                  NonRecursive d -> freeVars d
                  Recursive ds   -> rmVals (defs ds) (freeVars ds)


instance FreeVars Decl where
  freeVars d = freeVars (dDefinition d) <> freeVars (dSignature d)


instance FreeVars DeclDef where
  freeVars d = case d of
                 DPrim -> mempty
                 DForeign _ me -> foldMap freeVars me
                 DExpr e -> freeVars e


instance FreeVars Expr where
  freeVars expr =
    case expr of
      ELocated _r t     -> freeVars t
      EList es t        -> freeVars es <> freeVars t
      ETuple es         -> freeVars es
      ERec fs           -> freeVars (recordElements fs)
      ESel e _          -> freeVars e
      ESet ty e _ v     -> freeVars ty <> freeVars [e,v]
      EIf e1 e2 e3      -> freeVars [e1,e2,e3]
      EComp t1 t2 e mss -> freeVars [t1,t2] <> rmVals (defs mss) (freeVars e)
                                            <> mconcat (map foldFree mss)
      EVar x            -> mempty { valDeps = Set.singleton x }
      ETAbs a e         -> rmTParam a (freeVars e)
      ETApp e t         -> freeVars e <> freeVars t
      EApp e1 e2        -> freeVars [e1,e2]
      EAbs x t e        -> freeVars t <> rmVal x (freeVars e)
      EProofAbs p e     -> freeVars p <> freeVars e
      EProofApp e       -> freeVars e
      EWhere e ds       -> foldFree ds <> rmVals (defs ds) (freeVars e)
      EPropGuards guards t -> mconcat [ freeVars e | (_, e) <- guards ]
                              <> freeVars t
    where
      foldFree :: (FreeVars a, Defs a) => [a] -> Deps
      foldFree = foldr updateFree mempty
      updateFree x rest = freeVars x <> rmVals (defs x) rest

instance FreeVars Match where
  freeVars m = case m of
                 From _ t1 t2 e -> freeVars t1 <> freeVars t2 <> freeVars e
                 Let d          -> freeVars d



instance FreeVars Schema where
  freeVars s = foldr rmTParam (freeVars (sProps s) <> freeVars (sType s))
                              (sVars s)

instance FreeVars Type where
  freeVars ty =
    case ty of
      TCon tc ts -> freeVars tc <> freeVars ts
      TVar tv -> freeVars tv

      TUser _ _ t -> freeVars t
      TRec fs     -> freeVars (recordElements fs)
      TNewtype nt ts -> freeVars nt <> freeVars ts

instance FreeVars TVar where
  freeVars tv = case tv of
                  TVBound p -> mempty { tyParams = Set.singleton p }
                  _         -> mempty

instance FreeVars TCon where
  freeVars _tc = mempty

instance FreeVars Newtype where
  freeVars nt = foldr rmTParam base (ntParams nt)
    where base = freeVars (ntConstraints nt) <> freeVars (ntDef nt)

instance FreeVars NewtypeDef where
  freeVars def =
    case def of
      Struct c -> freeVars c
      Enum cs -> freeVars cs

instance FreeVars StructCon where
  freeVars c = freeVars (recordElements (ntFields c))

instance FreeVars EnumCon where
  freeVars c = freeVars (ecFields c)


--------------------------------------------------------------------------------

class Defs d where
  defs :: d -> Set Name

instance Defs a => Defs [a] where
  defs = Set.unions . map defs

instance Defs DeclGroup where
  defs dg = case dg of
              Recursive ds   -> defs ds
              NonRecursive d -> defs d

instance Defs Decl where
  defs d = Set.singleton (dName d)

instance Defs Match where
  defs m = case m of
             From x _ _ _ -> Set.singleton x
             Let d -> defs d
