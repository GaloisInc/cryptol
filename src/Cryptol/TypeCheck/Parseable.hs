-- |
-- Module      :  Cryptol.TypeCheck.Parseable
-- Copyright   :  (c) 2013-2017 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe                                #-}

{-# LANGUAGE RecordWildCards                     #-}
{-# LANGUAGE PatternGuards                       #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE DeriveAnyClass, DeriveGeneric       #-}
module Cryptol.TypeCheck.Parseable
  ( module Cryptol.TypeCheck.Parseable
  , ShowParseable(..)
  ) where

import Data.Void
import qualified Data.Map as Map
import Prettyprinter

import Cryptol.TypeCheck.AST
import Cryptol.Utils.Ident (Ident,unpackIdent)
import Cryptol.Utils.RecordMap (canonicalFields)
import Cryptol.Parser.AST ( Located(..))
import Cryptol.ModuleSystem.Name


infixl 5 $$
($$) :: Doc a -> Doc a -> Doc a
($$) x y = sep [x, y]

text :: String -> Doc a
text = pretty

int :: Int -> Doc a
int = pretty

-- ShowParseable prints out a cryptol program in a way that it's parseable by Coq (and likely other things)
-- Used mainly for reasoning about the semantics of cryptol programs in Coq (https://github.com/GaloisInc/cryptol-semantics)
class ShowParseable t where
  showParseable :: t -> Doc Void

instance ShowParseable Expr where
  showParseable (ELocated _ e) = showParseable e -- TODO? emit range information
  showParseable (EList es _) = parens (text "EList" <+> showParseable es)
  showParseable (ETuple es) = parens (text "ETuple" <+> showParseable es)
  showParseable (ERec ides) = parens (text "ERec" <+> showParseable (canonicalFields ides))
  showParseable (ESel e s) = parens (text "ESel" <+> showParseable e <+> showParseable s)
  showParseable (ESet _ty e s v) = parens (text "ESet" <+>
                                showParseable e <+> showParseable s
                                                <+> showParseable v)
  showParseable (EIf c t f) = parens (text "EIf" <+> showParseable c $$ showParseable t $$ showParseable f)
  showParseable (ECase e as d) =
    parens (text "ECase" <+> showParseable e $$ showParseable (Map.toList as)
                                             $$ showParseable d)
  showParseable (EComp _ _ e mss) = parens (text "EComp" $$ showParseable e $$ showParseable mss)
  showParseable (EVar n) = parens (text "EVar" <+> showParseable n)
  showParseable (EApp fe ae) = parens (text "EApp" $$ showParseable fe $$ showParseable ae)
  showParseable (EAbs n _ e) = parens (text "EAbs" <+> showParseable n $$ showParseable e)
  showParseable (EWhere e dclg) = parens (text "EWhere" $$ showParseable e $$ showParseable dclg)
  showParseable (ETAbs tp e) = parens (text "ETAbs" <+> showParseable tp
                                        $$ showParseable e)
  showParseable (ETApp e t) = parens (text "ETApp" $$ showParseable e $$ parens (text "ETyp" <+> showParseable t))
  --NOTE: erase all "proofs" for now (change the following two lines to change that)
  showParseable (EProofAbs {-p-}_ e) = showParseable e --"(EProofAbs " ++ show p ++ showParseable e ++ ")"
  showParseable (EProofApp e) = showParseable e --"(EProofApp " ++ showParseable e ++ ")"
  
  showParseable (EPropGuards guards _) = parens (text "EPropGuards" $$ showParseable guards)

instance (ShowParseable a, ShowParseable b) => ShowParseable (a,b) where
  showParseable (x,y) = parens (showParseable x <> comma <> showParseable y)

instance ShowParseable Int where
  showParseable i = int i

instance ShowParseable Ident where
  showParseable i = text $ show $ unpackIdent i

instance ShowParseable Type where
  showParseable (TUser n lt t) = parens (text "TUser" <+> showParseable n <+> showParseable lt <+> showParseable t)
  showParseable (TRec lidt) = parens (text "TRec" <+> showParseable (canonicalFields lidt))
  showParseable t = parens $ text $ show t

instance ShowParseable Selector where
  showParseable (TupleSel n _) = parens (text "TupleSel" <+> showParseable n)
  showParseable (RecordSel n _) = parens (text "RecordSel" <+> showParseable n)
  showParseable (ListSel n _) = parens (text "ListSel" <+> showParseable n)

instance ShowParseable Match where
  showParseable (From n _ _ e) = parens (text "From" <+> showParseable n <+> showParseable e)
  showParseable (Let d) = parens (text "MLet" <+> showParseable d)


instance ShowParseable CaseAlt where
  showParseable (CaseAlt xs e) =
    parens (text "CaseAlt" <+> showParseable xs <+> showParseable e)


instance ShowParseable Decl where
  showParseable d = parens (text "Decl" <+> showParseable (dName d)
                              $$ showParseable (dDefinition d))

instance ShowParseable FFI where
  showParseable mo =
    case mo of
      CallAbstract t -> parens (text "CallAbstract" <+> parens (text (show t)))
      CallC t        -> parens (text "CallC" <+> parens (text (show t)))

instance ShowParseable DeclDef where
  showParseable DPrim = text (show DPrim)
  showParseable (DForeign t me) =
    parens (text "DForeign" $$ showParseable t $$ showParseable me)
  showParseable (DExpr e) = parens (text "DExpr" $$ showParseable e)

instance ShowParseable DeclGroup where
  showParseable (Recursive ds) =
    parens (text "Recursive" $$ showParseable ds)
  showParseable (NonRecursive d) =
    parens (text "NonRecursive" $$ showParseable d)

instance (ShowParseable a) => ShowParseable [a] where
  showParseable a = case a of
                      [] -> text "[]"
                      [x] -> brackets (showParseable x)
                      x : xs -> text "[" <+> showParseable x $$
                                vcat [ comma <+> showParseable y | y <- xs ] $$
                                text "]"

instance (ShowParseable a) => ShowParseable (Maybe a) where
  showParseable Nothing = text "(0,\"\")" --empty ident, won't shadow number
  showParseable (Just x) = showParseable x

instance (ShowParseable a) => ShowParseable (Located a) where
  showParseable l = showParseable (thing l)

instance ShowParseable TParam where
  showParseable tp = parens (text (show (tpUnique tp)) <> comma <> maybeNameDoc (tpName tp))

maybeNameDoc :: Maybe Name -> Doc Void
maybeNameDoc Nothing = dquotes mempty
maybeNameDoc (Just n) = showParseable (nameIdent n)

instance ShowParseable Name where
  showParseable n = parens (text (show (nameUnique n)) <> comma <> showParseable (nameIdent n))
