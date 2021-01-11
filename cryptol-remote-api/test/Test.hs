{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main (main) where

import Data.Aeson as JSON (fromJSON, toJSON, Result(..))

import qualified Data.HashMap.Strict as HM
import Data.List.NonEmpty(NonEmpty(..))
import System.Directory (findExecutable)

import Test.QuickCheck.Instances.Text()
import Test.Tasty
import Test.Tasty.HUnit.ScriptExit
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import CryptolServer.Call

import Argo.PythonBindings
import Paths_cryptol_remote_api

exeExists :: FilePath -> IO FilePath
exeExists e = findExecutable e >>=
  maybe (assertFailure $ e <> " executable not found") pure

main :: IO ()
main =
  do reqs <- getArgoPythonFile "requirements.txt"
     sequence_ [exeExists "z3", exeExists "cryptol-remote-api", exeExists "cryptol-eval-server"]
     withPython3venv (Just reqs) $ \pip python ->
       do pySrc <- getArgoPythonFile "."
          testScriptsDir <- getDataFileName "test-scripts/"
          pip ["install", pySrc]
          putStrLn "pipped"

          scriptTests <- makeScriptTests testScriptsDir [python]

          defaultMain $
            testGroup "Tests for saw-remote-api"
              [ testGroup "Scripting API tests" scriptTests
              , callMsgProps
              ]

instance Arbitrary Encoding where
  arbitrary = oneof [pure Hex, pure Base64]

instance Arbitrary Expression where
  arbitrary = sized spec
    where
      spec n
        | n <= 0 =
          oneof [ Bit <$> arbitrary
                , pure Unit
                , Num <$> arbitrary <*> arbitrary <*> arbitrary
                , Integer <$> arbitrary
                -- NB: The following case will not generate
                -- syntactically valid Cryptol. But for testing
                -- round-tripping of the JSON, and coverage of various
                -- functions, it's better than nothing.
                , Concrete <$> arbitrary
                ]
        | otherwise =
          choose (2, n) >>=
          \len ->
            let sub = n `div` len
            in
              oneof [ Record . HM.fromList <$> vectorOf len ((,) <$> arbitrary <*> spec sub)
                    , Sequence <$> vectorOf len (spec sub)
                    , Tuple <$> vectorOf len (spec sub)
                    -- NB: Will not make valid identifiers, so if we
                    -- ever insert validation, then this will need to
                    -- change.
                    , Let <$> vectorOf len (LetBinding <$> arbitrary <*> spec sub) <*> spec sub
                    , Application <$> spec sub <*> ((:|) <$> spec sub <*> vectorOf len (spec sub))
                    ]

callMsgProps :: TestTree
callMsgProps =
  testGroup "QuickCheck properties for the \"call\" message"
    [ testProperty "encoding and decoding arg specs is the identity" $
      \(spec :: Expression) ->
        case fromJSON (toJSON spec) of
          JSON.Success v -> spec == v
          JSON.Error _ -> False
    ]
