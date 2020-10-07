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
  ) where

import qualified Data.Aeson as JSON
import qualified Data.Text as Text
import qualified Data.Vector as Vector

import Cryptol.ModuleSystem (ModuleError(..), ModuleWarning(..))
import Cryptol.Utils.PP (pretty, PP)

import Data.Aeson hiding (Encoding, Value, decode)
import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as B8
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.HashMap.Strict as HashMap

import Cryptol.ModuleSystem.Name (Name)
import Cryptol.Parser
import qualified Cryptol.TypeCheck.Type as TC

import Argo
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
      NoIncludeErrors src errs ->
        -- TODO: structured error here
        (20720, [ ("source", jsonPretty src)
                , ("errors", jsonList (map jsonShow errs))
                ])
      TypeCheckingFailed src errs ->
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
      ImportedParamModule x ->
        (20630, [ ("module", jsonPretty x)
                ])
      FailedToParameterizeModDefs x xs ->
        (20640, [ ("module", jsonPretty x)
                , ("parameters", jsonList (map (jsonString . pretty) xs))
                ])
      NotAParameterizedModule x ->
        (20650, [ ("module", jsonPretty x)
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
                TypeCheckWarnings tcwarns ->
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
      [ jsonTypeAndString ty <> HashMap.fromList ["parameter" .= pretty param]
      | (param, ty) <- defs ] ]))

evalInParamMod :: [Cryptol.ModuleSystem.Name.Name] -> JSONRPCException
evalInParamMod mods =
  makeJSONRPCException
    20220 "Can't evaluate Cryptol in a parameterized module."
    (Just (JSON.object ["modules" .= map pretty mods]))

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
  HashMap.fromList
    [ "type" .= JSONSchema (TC.Forall [] [] ty)
    , "type string" .= pretty ty ]
