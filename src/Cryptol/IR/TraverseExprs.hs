{-# Language ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

module Cryptol.IR.TraverseExprs 
  ( TraverseExprs(..)
  , traverseSubExprs
  , traverseImmSubExprs
  , mapSubExprs
  , mapExprs
  , foldMapSubExprs
  , foldMapExprs
  ) where

import Control.Monad.Writer

import Data.Functor.Identity
import Data.Set(Set)
import qualified Data.Set as Set

import Cryptol.TypeCheck.AST
import Cryptol.Parser.Position(Located(..))

class TraverseExprs t where
  -- | Traverse over constituent expressions, without recursing into sub-expressions.
  traverseExprs :: Applicative f => (Expr -> f Expr) -> t -> f t

-- | Traverse over constituent expressions, first recursing into sub-expressions.
traverseSubExprs ::
  forall t m. (TraverseExprs t, Monad m) => (Expr -> m Expr) -> (t -> m t)
traverseSubExprs f = traverseExprs go
  where
    go :: Expr -> m Expr
    go e = traverseImmSubExprs go e >>= f

mapSubExprs :: TraverseExprs t => (Expr -> Expr) -> t -> t
mapSubExprs f x = runIdentity (traverseSubExprs (Identity . f) x)

mapExprs :: TraverseExprs t => (Expr -> Expr) -> t -> t
mapExprs f x = runIdentity (traverseExprs (Identity . f) x)

foldMapSubExprs :: (TraverseExprs t, Monoid m) => (Expr -> m) -> t -> m
foldMapSubExprs f t = execWriter $ traverseSubExprs (\e -> tell (f e) >> return e) t

foldMapExprs :: (TraverseExprs t, Monoid m) => (Expr -> m) -> t -> m
foldMapExprs f t = execWriter $ traverseExprs (\e -> tell (f e) >> return e) t

-- | Traverse over immediate sub-expressions.
traverseImmSubExprs :: forall f. Applicative f => (Expr -> f Expr) -> Expr -> f Expr
traverseImmSubExprs f se = case se of
  EList es t -> EList <$> go es <*> pure t
  ETuple es -> ETuple <$> go es
  ERec mp -> ERec <$> traverse go mp
  ESel e sel -> ESel <$> go e <*> pure sel
  ESet t e1 sel e2 -> ESet <$> pure t <*> go e1 <*> pure sel <*> go e2
  EIf eP eT eF -> EIf <$> go eP <*> go eT <*> go eF
  ECase e alts malt -> ECase
    <$> go e <*> traverse go alts <*> go malt
  EComp t1 t2 e matches -> EComp
    <$> pure t1 <*> pure t2 <*> go e <*> go matches
  EVar n -> EVar <$> pure n
  ETAbs tps e -> ETAbs <$> pure tps <*> go e
  ETApp e t -> ETApp <$> go e <*> pure t
  EApp e1 e2 -> EApp <$> go e1 <*> go e2
  EAbs n t e -> EAbs <$> pure n <*> pure t <*> go e
  ELocated r e -> ELocated <$> pure r <*> go e
  EProofAbs p e -> EProofAbs <$> pure p <*> go e
  EProofApp e -> EProofApp <$> go e
  EWhere e decls -> EWhere <$> go e <*> traverse go decls
  EPropGuards gs t  -> EPropGuards <$> traverse doG gs <*> pure t
    where doG (xs, e) = (,) <$> pure xs <*> go e
  where
    go :: forall t. TraverseExprs t => t -> f t
    go = traverseExprs f

instance TraverseExprs a => TraverseExprs [a] where
  traverseExprs f = traverse (traverseExprs f)

instance TraverseExprs a => TraverseExprs (Maybe a) where
  traverseExprs f = traverse (traverseExprs f)

instance (Ord a, TraverseExprs a) => TraverseExprs (Set a) where
  traverseExprs f = fmap Set.fromList . traverseExprs f . Set.toList

instance TraverseExprs a => TraverseExprs (Located a) where
  traverseExprs f (Located r a) = Located r <$> traverseExprs f a

instance TraverseExprs Expr where
  traverseExprs f = f

instance TraverseExprs CaseAlt where
  traverseExprs f (CaseAlt xs e) =
    CaseAlt <$> pure xs <*> traverseExprs f e

instance TraverseExprs Match where
  traverseExprs f = \case
    From x t1 t2 e -> From <$> pure x <*> pure t1 <*> pure t2 <*> traverseExprs f e
    Let d -> Let <$> traverseExprs f d

instance TraverseExprs DeclDef where
  traverseExprs f = \case
    DPrim -> pure DPrim
    DForeign ffi me -> DForeign <$> pure ffi <*> traverseExprs f me
    DExpr e -> DExpr <$> traverseExprs f e

instance TraverseExprs DeclGroup where
  traverseExprs f = \case
    Recursive ds -> Recursive <$> traverseExprs f ds
    NonRecursive d -> NonRecursive <$> traverseExprs f d

instance TraverseExprs Decl where
  traverseExprs f Decl{..} = Decl
    <$> pure dName <*> pure dSignature <*> traverseExprs f dDefinition <*> pure dPragmas 
    <*> pure dInfix <*> pure dFixity <*> pure dDoc

