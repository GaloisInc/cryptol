-- | A simple system so that the Cryptol driver can communicate
-- with users (or not).
module Cryptol.Utils.Logger
  ( Logger

  , stdoutLogger
  , handleLogger
  , quietLogger
  , funLogger

  , logPutStr
  , logPutStrLn
  , logPrint
  ) where

import System.IO(Handle, hPutStr, stdout)
import Control.DeepSeq(NFData(..))

-- | A logger provides simple abstraction for sending messages.
newtype Logger = Logger (String -> IO ())

instance NFData Logger where
  rnf (Logger x) = rnf x

-- | Send the given string to the log.
logPutStr :: Logger -> String -> IO ()
logPutStr (Logger f) = f

-- | Send the given string with a newline at the end.
logPutStrLn :: Logger -> String -> IO ()
logPutStrLn l s = logPutStr l (s ++ "\n")

-- | Send the given value using its 'Show' instance.
-- Adds a newline at the end.
logPrint :: Show a => Logger -> a -> IO ()
logPrint l a = logPutStrLn l (show a)

-- | A logger that ignores all messages.
quietLogger :: Logger
quietLogger = Logger (const (return ()))

-- | Log to the given handle.
handleLogger :: Handle -> Logger
handleLogger h = Logger (hPutStr h)

-- | Log to stdout.
stdoutLogger :: Logger
stdoutLogger = handleLogger stdout

-- | Just use this function for logging.
funLogger :: (String -> IO ()) -> Logger
funLogger = Logger




