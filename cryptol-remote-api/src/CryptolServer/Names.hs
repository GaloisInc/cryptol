{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
module CryptolServer.Names
  ( visibleNames
  , visibleNamesDescr
  , nameLocation
  , nameLocationDescr
  ) where

import qualified Argo.Doc as Doc
import Control.Monad.IO.Class (liftIO)
import qualified Data.Aeson as JSON
import Data.Aeson ((.=), (.:))
import Data.List (nub)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Text (unpack)
import Data.Typeable (Proxy(..), typeRep)
import Data.Maybe (fromMaybe, mapMaybe, isJust)

import Cryptol.Parser (parseHelpName)
import Cryptol.Parser.Name (PName(..))
import Cryptol.Parser.AST (Pragma)
import Cryptol.Parser.Position (Range(..), col, line)
import Cryptol.ModuleSystem (makeRelativeToSearchPath)
import Cryptol.ModuleSystem.Env
  ( ModContext(..), ModuleEnv(..), DynamicEnv(..), ModulePath(..)
  , focusedEnv, modContextParamNames, lookupTCEntity
  , lmFilePath, lmModuleId, lmName
  )
import Cryptol.ModuleSystem.Interface (IfaceDecl(..), IfaceDecls(..))
import Cryptol.ModuleSystem.Name (Name)
import qualified Cryptol.ModuleSystem.Name as N
  ( nameInfo, NameInfo(..), nameLoc, nameNamespace, nameTopModule )
import Cryptol.ModuleSystem.NamingEnv
                  (NamingEnv, namespaceMap, lookupListNS, shadowing)
import Cryptol.TypeCheck.Type (Schema(..), ModVParam(..), mpnFuns)
import Cryptol.Utils.Fixity(Fixity(..), defaultFixity)
import Cryptol.Utils.PP (pp, pretty)
import Cryptol.Utils.Ident(Namespace(..),ogModule)

import CryptolServer
import CryptolServer.Data.Type

data VisibleNamesParams = VisibleNamesParams

instance JSON.FromJSON VisibleNamesParams where
  parseJSON _ = pure VisibleNamesParams

instance Doc.DescribedMethod VisibleNamesParams [NameInfo] where
  parameterFieldDescription = []

  resultFieldDescription =
    [ ("name",
      Doc.Paragraph [Doc.Text "A human-readable representation of the name"])
    , ("type string",
      Doc.Paragraph [Doc.Text "A human-readable representation of the name's type schema"])
    , ("type",
      Doc.Paragraph [ Doc.Text " A"
                    , Doc.Link (Doc.TypeDesc (typeRep (Proxy @JSONSchema))) "JSON Cryptol type"
                    ])
    , ("module",
      Doc.Paragraph [Doc.Text "A human-readable representation of the module from which the name originates"])
    , ("parameter",
      Doc.Paragraph [ Doc.Text "An optional field which is present iff the name is a module parameter" ])
    , ("infix",
      Doc.Paragraph [ Doc.Text "An optional field which is present iff the name is an infix operator. ",
                      Doc.Text "If present, it contains an object with two fields. One field is ",
                      Doc.Literal "associativity", Doc.Text ", containing one of the strings ",
                      Doc.Literal "left-associative", Doc.Text ", ",
                      Doc.Literal "right-associative", Doc.Text ", or ",
                      Doc.Literal "non-associative", Doc.Text ", and the other is ",
                      Doc.Literal "level", Doc.Text ", containing the name's precedence level." ])
    , ("pragmas",
      Doc.Paragraph [ Doc.Text "An optional field containing a list of the name's pragmas (e.g. ",
                      Doc.Literal "property", Doc.Text "), if it has any"])
    , ("documentation",
      Doc.Paragraph [Doc.Text "An optional field containing documentation string for the name, if it is documented"])
    ]

visibleNamesDescr :: Doc.Block
visibleNamesDescr =
  Doc.Paragraph [Doc.Text "List the currently visible (i.e., in scope) term names."]

visibleNames :: VisibleNamesParams -> CryptolCommand [NameInfo]
visibleNames _ =
  do me <- getModuleEnv
     let DEnv { deNames = dyNames } = meDynEnv me
     let ModContext { mctxParams = fparams
                    , mctxDecls = fDecls
                    , mctxNames = fNames
                    } = focusedEnv me
     let inScope = Map.keys (namespaceMap NSValue $ dyNames `shadowing` fNames)
         params = mpnFuns (modContextParamNames fparams)
     return $ concatMap (getInfo fNames params (ifDecls fDecls)) inScope

newtype NameLocationParams = NameLocationParams PName

instance JSON.FromJSON NameLocationParams where
  parseJSON =
    JSON.withObject "params for \"name location\"" $ \o -> do
      txt <- o .: "name"
      case parseHelpName txt of
        Nothing -> fail "Invalid Cryptol name"
        Just name -> pure (NameLocationParams name)

instance Doc.DescribedMethod NameLocationParams [NameLocation] where
  parameterFieldDescription =
    [ ("name", Doc.Paragraph [Doc.Text "The name whose definition locations should be returned."]) ]

  resultFieldDescription =
    [ ("namespace",
      Doc.Paragraph [Doc.Text "The namespace of the definition: value, type, or module."])
    , ("location",
      Doc.Paragraph
        [ Doc.Text "A filename relative to the Cryptol search path when possible "
        , Doc.Text "(and absolute otherwise), "
        , Doc.Literal "module M"
        , Doc.Text " for a builtin module, or "
        , Doc.Literal "interactive"
        , Doc.Text " for a definition introduced through the API."
        ])
    , ("line", Doc.Paragraph [Doc.Text "The one-based line number of the definition."])
    , ("column", Doc.Paragraph [Doc.Text "The one-based column number of the definition."])
    ]

nameLocationDescr :: Doc.Block
nameLocationDescr =
  Doc.Paragraph
    [ Doc.Text "Return the definition locations of all entities with the given name that are in scope." ]

nameLocation :: NameLocationParams -> CryptolCommand [NameLocation]
nameLocation (NameLocationParams pname) =
  do me <- getModuleEnv
     let names =
           nub
             $ concatMap
                 (\ns -> lookupListNS ns pname (mctxNames (focusedEnv me)))
                 [NSValue, NSConstructor, NSType, NSModule]
     mapM (formatNameLocation me) names

data NameLocation =
  NameLocation
    { locationNamespace :: String
    , locationSource :: String
    , locationLine :: Int
    , locationColumn :: Int
    }

instance JSON.ToJSON NameLocation where
  toJSON NameLocation {..} =
    JSON.object
      [ "namespace" .= locationNamespace
      , "location" .= locationSource
      , "line" .= locationLine
      , "column" .= locationColumn
      ]

formatNameLocation :: ModuleEnv -> Name -> CryptolCommand NameLocation
formatNameLocation me name =
  do source <-
       case lookupTCEntity (N.nameTopModule name) me of
         Just lm ->
           case lmFilePath lm of
             InFile {} -> liftIO (makeRelativeToSearchPath me (lmModuleId lm))
             InMem {}  -> pure ("module " ++ pretty (lmName lm))
         Nothing -> pure "interactive"
     pure
       NameLocation
         { locationNamespace =
             case N.nameNamespace name of
               NSValue       -> "value"
               NSConstructor -> "value"
               NSType        -> "type"
               NSModule      -> "module"
         , locationSource = source
         , locationLine = line (from loc)
         , locationColumn = col (from loc)
         }
  where
  loc = N.nameLoc name

getInfo :: NamingEnv -> Map Name ModVParam -> Map Name IfaceDecl -> PName -> [NameInfo]
getInfo rnEnv params decls n' =
  flip mapMaybe (lookupListNS NSValue n' rnEnv) $ \n ->
    case (N.nameInfo n, Map.lookup n params, Map.lookup n decls) of
      (N.GlobalName _ og, Just (ModVParam _ ty nameDocs fx), _) ->
        Just $ mkNameInfo True ty og (isJust fx) fx ([]::[Pragma]) nameDocs
      (N.GlobalName _ og, _, Just (IfaceDecl _ ty _ prags ifx fx nameDocs)) ->
        Just $ mkNameInfo False ty og ifx fx prags nameDocs
      _ -> Nothing
  where mkNameInfo param ty og ifx fx prags nameDocs = 
          let fxy
                | not ifx = Nothing
                | otherwise =
                  case fromMaybe defaultFixity fx of
                    Fixity assoc lvl -> Just (show (pp assoc), lvl)

           in NameInfo
                { name      = show (pp n')
                , typeSig   = show (pp ty)
                , schema    = ty
                , modl      = show (pp (ogModule og))
                , isParam   = param
                , fixity    = fxy
                , pragmas   = show . pp <$> prags
                , nameDocs  = unpack <$> nameDocs
                }

data NameInfo =
  NameInfo
  { name     :: String
  , typeSig  :: String
  , schema   :: Schema
  , modl     :: String
  , isParam  :: Bool
  , fixity   :: Maybe (String, Int)
  , pragmas  :: [String]
  , nameDocs :: Maybe String
  }

instance JSON.ToJSON NameInfo where
  toJSON (NameInfo{..}) =
    JSON.object $
    [ "name" .= name
    , "type string" .= typeSig
    , "type" .= JSONSchema schema
    , "module" .= modl
    ] ++
    (if isParam then ["parameter" .= ()] else []) ++
    maybe [] (\(assoc, lvl) ->
              ["infix" .= JSON.object
                          [ "associativity" .= assoc
                          , "level" .= lvl ]]) fixity ++
    (if null pragmas then [] else ["pragmas" .= pragmas]) ++
    maybe [] (\d -> ["documentation" .= d]) nameDocs
