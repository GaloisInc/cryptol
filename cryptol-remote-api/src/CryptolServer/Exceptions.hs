{-# LANGUAGE OverloadedStrings #-}
module CryptolServer.Exceptions
  ( dirNotFound
  , invalidBase64
  , invalidHex
  , invalidType
  , unwantedDefaults
  , evalInParamMod
  , evalPolyErr
  , proverError
  , cryptolParseErr
  , cryptolError
  , moduleNotLoaded
  ) where

import qualified Data.Aeson as JSON
import qualified Data.Text as Text
import qualified Data.Vector as Vector

import Cryptol.Parser.AST(ModName)
import Cryptol.ModuleSystem (ModuleError(..), ModuleWarning(..))
import Cryptol.ModuleSystem.Name as CM
import Cryptol.Utils.PP (pretty, PP)

import Data.Aeson hiding (Encoding, Value, decode)
import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as B8
import Data.Text (Text)
import qualified Data.Text as T

import Cryptol.Parser
import qualified Cryptol.TypeCheck.Type as TC

import Argo
import CryptolServer.AesonCompat
import CryptolServer.Data.Type

cryptolError :: ModuleError -> [ModuleWarning] -> JSONRPCException
cryptolError modErr warns =
  makeJSONRPCException
    errorNum
    (Text.pack $ (pretty modErr) <> foldMap (\w -> "\n" <> pretty w) warns)
    (Just . JSON.object $ errorData ++ [("warnings", moduleWarnings warns)])
  where
    -- TODO: make sub-errors (parse, typecheck, etc.) into structured data so
    -- that another client can parse them and make use of them (possible
    -- locations noted below)

    (errorNum, errorData) = moduleError modErr

    moduleError err = case err of
      ModuleNotFound src path ->
        (20500, [ ("source", jsonPretty src)
                , ("path", jsonList (map jsonString path))
                ])
      CantFindFile path ->
        (20050, [ ("path", jsonString path)
                ])
      BadUtf8 path ue ->
        (20010, [ ("path", jsonShow path)
                , ("error", jsonShow ue)
                ])
      OtherIOError path exn ->
        (20060, [ ("path", jsonString path)
                , ("error", jsonShow exn)
                ])
      ModuleParseError source message ->
        (20540, [ ("source", jsonShow source)
                , ("error", jsonShow message)
                ])
      RecursiveModules mods ->
        (20550, [ ("modules", jsonList (reverse (map jsonPretty mods)))
                ])
      RenamerErrors src errs ->
        -- TODO: structured error here
        (20700, [ ("source", jsonPretty src)
                , ("errors", jsonList (map jsonPretty errs))
                ])
      NoPatErrors src errs ->
        -- TODO: structured error here
        (20710, [ ("source", jsonPretty src)
                , ("errors", jsonList (map jsonPretty errs))
                ])
      ExpandPropGuardsError src err' ->
        (20711, [ ("source", jsonPretty src)
                , ("errors", jsonPretty err')
                ])

      NoIncludeErrors src errs ->
        -- TODO: structured error here
        (20720, [ ("source", jsonPretty src)
                , ("errors", jsonList (map jsonShow errs))
                ])
      TypeCheckingFailed src _nameMap errs ->
        -- TODO: structured error here
        (20730, [ ("source", jsonPretty src)
                , ("errors", jsonList (map jsonShow errs))
                ])
      ModuleNameMismatch expected found ->
        (20600, [ ("expected", jsonPretty expected)
                , ("found", jsonPretty found)
                ])
      DuplicateModuleName name path1 path2 ->
        (20610, [ ("name", jsonPretty name)
                , ("paths", jsonList [jsonString path1, jsonString path2])
                ])
      FFILoadErrors x errs ->
        (20660, [ ("module", jsonPretty x)
                , ("errors", jsonList (map jsonPretty errs))
                ])
      OtherFailure x ->
        (29999, [ ("error", jsonString x)
                ])
      ErrorInFile x y ->
        (n, ("path", jsonShow x) : e)
        where (n, e) = moduleError y

    moduleWarnings :: [ModuleWarning] -> JSON.Value
    moduleWarnings =
      -- TODO: structured error here
      jsonList . concatMap
        (\w -> case w of
                TypeCheckWarnings _nameMap tcwarns ->
                  map (jsonPretty . snd) tcwarns
                RenamerWarnings rnwarns ->
                  map jsonPretty rnwarns)

    -- Some little helpers for common ways of building JSON values in the above:

    jsonString :: String -> JSON.Value
    jsonString = JSON.String . Text.pack

    jsonPretty :: PP a => a -> JSON.Value
    jsonPretty = jsonString . pretty

    jsonShow :: Show a => a -> JSON.Value
    jsonShow = jsonString . show

    jsonList :: [JSON.Value] -> JSON.Value
    jsonList = JSON.Array . Vector.fromList

dirNotFound :: FilePath -> JSONRPCException
dirNotFound dir =
  makeJSONRPCException
    20051 (T.pack ("Directory doesn't exist: " <> dir))
    (Just (JSON.object ["path" .= dir]))

invalidBase64 :: ByteString -> String -> JSONRPCException
invalidBase64 invalidData msg =
  makeJSONRPCException
    20020 (T.pack msg)
    (Just (JSON.object ["input" .= B8.unpack invalidData]))

invalidHex :: Char -> JSONRPCException
invalidHex invalidData =
  makeJSONRPCException
    20030 "Not a hex digit"
    (Just (JSON.object ["input" .= T.singleton invalidData]))

invalidType :: TC.Type -> JSONRPCException
invalidType ty =
  makeJSONRPCException
    20040 "Can't convert Cryptol data from this type to JSON"
    (Just (jsonTypeAndString ty))

unwantedDefaults :: [(TC.TParam, TC.Type)] -> JSONRPCException
unwantedDefaults defs =
  makeJSONRPCException
    20210 "Execution would have required these defaults"
    (Just (JSON.object ["defaults" .=
      [ jsonTypeAndString ty <> fromListKM ["parameter" .= pretty param]
      | (param, ty) <- defs ] ]))

evalInParamMod :: [TC.TParam] -> [CM.Name] -> JSONRPCException
evalInParamMod tyParams defs =
  makeJSONRPCException
    20220 "Can't evaluate Cryptol in a parameterized module."
    (Just (JSON.object ["type parameters" .= map pretty tyParams
                       , "definitions" .= map pretty defs ]))

evalPolyErr ::
  TC.Schema {- ^ the type that was too polymorphic -} ->
  JSONRPCException
evalPolyErr schema =
  makeJSONRPCException
    20200 "Can't evaluate at polymorphic type"
    (Just (JSON.object [ "type" .= JSONSchema schema
                       , "type string" .= pretty schema ]))

proverError :: String -> JSONRPCException
proverError msg =
  makeJSONRPCException
    20230 "Prover error"
    (Just (JSON.object ["error" .= msg]))

cryptolParseErr ::
  Text {- ^ the input that couldn't be parsed -} ->
  ParseError {- ^ the parse error from Cryptol -} ->
  JSONRPCException
cryptolParseErr expr err =
  makeJSONRPCException
    20000 "Cryptol parse error"
    (Just $ JSON.object ["input" .= expr, "error" .= show err])

-- The standard way of presenting a type: a structured type, plus a
-- human-readable string
jsonTypeAndString :: TC.Type -> JSON.Object
jsonTypeAndString ty =
  fromListKM
    [ "type" .= JSONSchema (TC.Forall [] [] ty)
    , "type string" .= pretty ty ]

moduleNotLoaded :: ModName -> JSONRPCException
moduleNotLoaded m =
  makeJSONRPCException
    20100 "Module not loaded"
    (Just (JSON.object ["error" .= show (pretty m)]))

