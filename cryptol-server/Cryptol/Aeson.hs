{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wall -fno-warn-orphans -fno-warn-type-defaults #-}
-- | Orphan 'FromJSON' and 'ToJSON' instances for certain Cryptol
-- types. Since these are meant to be consumed over a wire, they are
-- mostly focused on base values and interfaces rather than a full
-- serialization of internal ASTs and such.
module Cryptol.Aeson where

import Control.Applicative
import Control.Exception
import Data.Aeson
import Data.Aeson.TH
import qualified Data.HashMap.Strict as HM
import Data.List
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Text (Text)
import qualified Data.Text as T

import qualified Cryptol.Eval.Error as E
import qualified Cryptol.Eval.Value as E
import qualified Cryptol.ModuleSystem as M
import qualified Cryptol.ModuleSystem.Monad as M
import qualified Cryptol.ModuleSystem.Renamer as M
import Cryptol.ModuleSystem.Interface
import Cryptol.ModuleSystem.Name
import qualified Cryptol.Parser as P
import qualified Cryptol.Parser.AST as P
import qualified Cryptol.Parser.Lexer as P
import qualified Cryptol.Parser.NoInclude as P
import qualified Cryptol.Parser.NoPat as NoPat
import qualified Cryptol.Parser.Position as P
import Cryptol.REPL.Monad
import qualified Cryptol.TypeCheck.AST as T
import qualified Cryptol.TypeCheck.InferTypes as T
import Cryptol.Utils.PP hiding (empty)

instance FromJSON a => FromJSON (Map QName a) where
  parseJSON = withObject "QName map" $ \o -> do
    let (ks, vs) = unzip (HM.toList o)
        ks' = map keyToQName ks
    vs' <- mapM parseJSON vs
    return (Map.fromList (zip ks' vs'))

instance ToJSON a => ToJSON (Map QName a) where
  toJSON m = Object (HM.fromList (zip ks' vs'))
    where (ks, vs) = unzip (Map.toList m)
          ks' = map keyFromQName ks
          vs' = map toJSON vs

-- | Assume that a 'QName' contains only an optional 'ModName' and a
-- 'Name', rather than a 'NewName'. This should be safe for the
-- purposes of this API where we're dealing with top-level names.
keyToQName :: Text -> QName
keyToQName str =
  case map T.unpack (T.split (== '.') str) of
    []   -> error "empty QName"
    [""] -> error "empty QName"
    [x]  -> mkUnqual (Name x)
    xs   -> mkQual (ModName (init xs)) (Name (last xs))

keyFromQName :: QName -> Text
keyFromQName = \case
  QName Nothing (Name x) -> T.pack x
  QName (Just (ModName mn)) (Name x) ->
    T.pack (intercalate "." (mn ++ [x]))
  _ -> error "NewName unsupported in JSON"

instance ToJSON Doc where
  toJSON = String . T.pack . render

instance ToJSON E.Value where
  toJSON = \case
    E.VRecord fs -> object
      [ "record" .= fs ]
    E.VTuple vs -> object
      [ "tuple" .= vs ]
    E.VBit b -> object
      [ "bit" .= b ]
    E.VSeq isWord xs -> object
      [ "sequence" .= object [ "isWord" .= isWord, "elements" .= xs ] ]
    E.VWord w -> object
      [ "word" .= w ]
    E.VStream _ -> object
      [ "stream" .= object [ "@note" .= "streams not supported" ] ]
    E.VFun _ -> object
      [ "function" .= object [ "@note" .= "functions not supported" ] ]
    E.VPoly _ -> object
      [ "poly" .= object [ "@note" .= "polymorphic values not supported" ] ]

instance FromJSON E.Value where
  parseJSON = withObject "Value" $ \o ->
        E.VRecord <$> o .: "record"
    <|> E.VTuple <$> o .: "tuple"
    <|> E.VBit <$> o .: "bit"
    <|> do s <- o .: "sequence"
           E.VSeq <$> s .: "isWord" <*> s .: "elements"
    <|> E.VWord <$> o .: "word"
    <|> error ("unexpected JSON value: " ++ show o)

instance ToJSON P.Token where
  toJSON = toJSON . pp

instance ToJSON IOException where
  toJSON exn = object
    [ "IOException" .= show exn ]

instance ToJSON M.RenamerError where
  toJSON err = object
    [ "renamerError" .= pp err ]

instance ToJSON T.Error where
  toJSON err = object
    [ "inferError" .= pp err ]

instance ToJSON E.BV where
  toJSON = \case
    E.BV w v -> object
      [ "bitvector" .= object [ "width" .= w, "value" .= v ] ]

instance FromJSON E.BV where
  parseJSON = withObject "BV" $ \o -> do
    bv <- o .: "bitvector"
    E.BV <$> bv .: "width" <*> bv .: "value"

$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''REPLException)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''NameEnv)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''NameInfo)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''E.EvalError)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''P.ParseError)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''P.Position)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''P.Range)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''P.Located)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''P.IncludeError)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''P.Schema)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''P.Type)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''P.TParam)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''P.Prop)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''P.Named)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''P.Kind)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''NoPat.Error)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''M.ModuleError)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''M.ImportSource)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''T.Import)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''T.ImportSpec)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''T.Type)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''T.TParam)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''T.Kind)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''T.TVar)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''T.TCon)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''T.PC)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''T.TC)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''T.UserTC)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''T.Schema)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''T.TFun)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''T.Selector)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } { fieldLabelModifier = drop 1 } ''T.Fixity)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''T.Pragma)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''Assoc)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''QName)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''ModName)
$(deriveJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''Name)
$(deriveJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''Pass)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''IfaceDecl)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''T.Newtype)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''T.TySyn)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''IfaceDecls)
$(deriveToJSON defaultOptions { sumEncoding = ObjectWithSingleField } ''Iface)
