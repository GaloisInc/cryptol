module Main (main) where

import System.Console.Haskeline.Completion (Completion(..))
import Test.Tasty
import Test.Tasty.HUnit

import qualified Cryptol.REPL.Command as REPL
import qualified Cryptol.REPL.Monad as REPL
import Cryptol.REPL.Monad (REPL)
import Cryptol.Utils.Logger (quietLogger)
import Cryptol.Utils.PP (pp)

import REPL.Haskeline (cryptolCommand)

main :: IO ()
main = defaultMain $
  testGroup "Cryptol API tests"
    [ testGroup "Tab completion tests" $
      map (uncurry replTabCompletionTestCase)
        [ (":check rev", ":check reverse")
        , (":t rev", ":t reverse")
        , (":type rev", ":type reverse")
        ]
    ]

-- | Assert a property in the 'REPL' monad and turn it into a test case.
replTestCase :: TestName -> REPL () -> TestTree
replTestCase name replAssertion =
  testCase name $
  REPL.runREPL
    False       -- Don't use batch mode
    False       -- Disable call stacks
    quietLogger -- Ignore all log messages
    replAssertion

-- | Assert that the REPL will tab-complete the given input in a particular way.
replTabCompletionTestCase ::
  -- | The input before the cursor just prior to hitting the tab key.
  String ->
  -- | The expected terminal input after hitting the tab key.
  String ->
  TestTree
replTabCompletionTestCase beforeTab afterTabExpected =
  replTestCase (show beforeTab ++ " --> " ++ show afterTabExpected) $
  do -- Load the prelude so that the REPL knows how to tab-complete prelude
     -- definitions.
     REPL.loadPrelude
     -- Perform the actual tab completion. (Oddly, Haskeline requires that the
     -- input to the left of the cursor should be reversed.)
     (_input, completions) <- cryptolCommand (reverse beforeTab, "")
     -- Check that the results match what is expected.
     REPL.io $
       case completions of
         [completion] ->
           do assertBool "Tab completion finished" (isFinished completion)
              let afterTabActual = beforeTab ++ replacement completion
              afterTabExpected @=? afterTabActual
         [] -> assertFailure "Expected one tab completion, but received none"
         _ -> assertFailure $ "Expected one tab completion, but received " ++
                              show (length completions)
  `REPL.catch`
    -- If something goes wrong run running the REPL, report it as a test
    -- failure.
    \x -> REPL.io $ assertFailure $ show $ pp x
