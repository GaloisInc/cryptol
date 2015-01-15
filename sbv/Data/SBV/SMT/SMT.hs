-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.SMT.SMT
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Abstraction of SMT solvers
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE DefaultSignatures   #-}

module Data.SBV.SMT.SMT where

import qualified Control.Exception as C

import Control.Concurrent (newEmptyMVar, takeMVar, putMVar, forkIO)
import Control.DeepSeq    (NFData(..))
import Control.Monad      (when, zipWithM)
import Data.Char          (isSpace)
import Data.Int           (Int8, Int16, Int32, Int64)
import Data.List          (intercalate, isPrefixOf, isInfixOf)
import Data.Word          (Word8, Word16, Word32, Word64)
import System.Directory   (findExecutable)
import System.Process     (runInteractiveProcess, waitForProcess, terminateProcess)
import System.Exit        (ExitCode(..))
import System.IO          (hClose, hFlush, hPutStr, hGetContents, hGetLine)

import qualified Data.Map as M
import Data.Typeable

import Data.SBV.BitVectors.AlgReals
import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.PrettyNum
import Data.SBV.Utils.TDiff

-- | Extract the final configuration from a result
resultConfig :: SMTResult -> SMTConfig
resultConfig (Unsatisfiable c) = c
resultConfig (Satisfiable c _) = c
resultConfig (Unknown c _)     = c
resultConfig (ProofError c _)  = c
resultConfig (TimeOut c)       = c

-- | A 'prove' call results in a 'ThmResult'
newtype ThmResult    = ThmResult    SMTResult

-- | A 'sat' call results in a 'SatResult'
-- The reason for having a separate 'SatResult' is to have a more meaningful 'Show' instance.
newtype SatResult    = SatResult    SMTResult

-- | An 'allSat' call results in a 'AllSatResult'. The boolean says whether
-- we should warn the user about prefix-existentials.
newtype AllSatResult = AllSatResult (Bool, [SMTResult])

-- | User friendly way of printing theorem results
instance Show ThmResult where
  show (ThmResult r) = showSMTResult "Q.E.D."
                                     "Unknown"     "Unknown. Potential counter-example:\n"
                                     "Falsifiable" "Falsifiable. Counter-example:\n" r

-- | User friendly way of printing satisfiablity results
instance Show SatResult where
  show (SatResult r) = showSMTResult "Unsatisfiable"
                                     "Unknown"     "Unknown. Potential model:\n"
                                     "Satisfiable" "Satisfiable. Model:\n" r

-- | The Show instance of AllSatResults. Note that we have to be careful in being lazy enough
-- as the typical use case is to pull results out as they become available.
instance Show AllSatResult where
  show (AllSatResult (e, xs)) = go (0::Int) xs
    where uniqueWarn | e    = " (Unique up to prefix existentials.)"
                     | True = ""
          go c (s:ss) = let c'      = c+1
                            (ok, o) = sh c' s
                        in c' `seq` if ok then o ++ "\n" ++ go c' ss else o
          go c []     = case c of
                          0 -> "No solutions found."
                          1 -> "This is the only solution." ++ uniqueWarn
                          _ -> "Found " ++ show c ++ " different solutions." ++ uniqueWarn
          sh i c = (ok, showSMTResult "Unsatisfiable"
                                      "Unknown" "Unknown. Potential model:\n"
                                      ("Solution #" ++ show i ++ ":\n[Backend solver returned no assignment to variables.]") ("Solution #" ++ show i ++ ":\n") c)
              where ok = case c of
                           Satisfiable{} -> True
                           _             -> False

-- | The result of an 'sAssert' call
data SafeResult = SafeNeverFails
                | SafeAlwaysFails  String
                | SafeFailsInModel String SMTConfig SMTModel
                deriving Typeable

-- | The show instance for SafeResult. Note that this is for display purposes only,
-- user programs are likely to pattern match on the output and proceed accordingly.
instance Show SafeResult where
   show SafeNeverFails              = "No safety violations detected."
   show (SafeAlwaysFails s)         = intercalate "\n" ["Assertion failure: " ++ show s, "*** Fails in all assignments to inputs"]
   show (SafeFailsInModel s cfg md) = intercalate "\n" ["Assertion failure: " ++ show s, showModel cfg md]

-- | If a 'prove' or 'sat' call comes accross an 'sAssert' call that fails, they will throw a 'SafeResult' as an exception.
instance C.Exception SafeResult

-- | Instances of 'SatModel' can be automatically extracted from models returned by the
-- solvers. The idea is that the sbv infrastructure provides a stream of 'CW''s (constant-words)
-- coming from the solver, and the type @a@ is interpreted based on these constants. Many typical
-- instances are already provided, so new instances can be declared with relative ease.
--
-- Minimum complete definition: 'parseCWs'
class SatModel a where
  -- | Given a sequence of constant-words, extract one instance of the type @a@, returning
  -- the remaining elements untouched. If the next element is not what's expected for this
  -- type you should return 'Nothing'
  parseCWs  :: [CW] -> Maybe (a, [CW])
  -- | Given a parsed model instance, transform it using @f@, and return the result.
  -- The default definition for this method should be sufficient in most use cases.
  cvtModel  :: (a -> Maybe b) -> Maybe (a, [CW]) -> Maybe (b, [CW])
  cvtModel f x = x >>= \(a, r) -> f a >>= \b -> return (b, r)

  default parseCWs :: Read a => [CW] -> Maybe (a, [CW])
  parseCWs (CW _ (CWUserSort (_, s)) : r) = Just (read s, r)
  parseCWs _                              = Nothing

-- | Parse a signed/sized value from a sequence of CWs
genParse :: Integral a => Kind -> [CW] -> Maybe (a, [CW])
genParse k (x@(CW _ (CWInteger i)):r) | kindOf x == k = Just (fromIntegral i, r)
genParse _ _                                          = Nothing

-- | Base case for 'SatModel' at unit type. Comes in handy if there are no real variables.
instance SatModel () where
  parseCWs xs = return ((), xs)

-- | 'Bool' as extracted from a model
instance SatModel Bool where
  parseCWs xs = do (x, r) <- genParse KBool xs
                   return ((x :: Integer) /= 0, r)

-- | 'Word8' as extracted from a model
instance SatModel Word8 where
  parseCWs = genParse (KBounded False 8)

-- | 'Int8' as extracted from a model
instance SatModel Int8 where
  parseCWs = genParse (KBounded True 8)

-- | 'Word16' as extracted from a model
instance SatModel Word16 where
  parseCWs = genParse (KBounded False 16)

-- | 'Int16' as extracted from a model
instance SatModel Int16 where
  parseCWs = genParse (KBounded True 16)

-- | 'Word32' as extracted from a model
instance SatModel Word32 where
  parseCWs = genParse (KBounded False 32)

-- | 'Int32' as extracted from a model
instance SatModel Int32 where
  parseCWs = genParse (KBounded True 32)

-- | 'Word64' as extracted from a model
instance SatModel Word64 where
  parseCWs = genParse (KBounded False 64)

-- | 'Int64' as extracted from a model
instance SatModel Int64 where
  parseCWs = genParse (KBounded True 64)

-- | 'Integer' as extracted from a model
instance SatModel Integer where
  parseCWs = genParse KUnbounded

-- | 'AlgReal' as extracted from a model
instance SatModel AlgReal where
  parseCWs (CW KReal (CWAlgReal i) : r) = Just (i, r)
  parseCWs _                            = Nothing

-- | 'Float' as extracted from a model
instance SatModel Float where
  parseCWs (CW KFloat (CWFloat i) : r) = Just (i, r)
  parseCWs _                           = Nothing

-- | 'Double' as extracted from a model
instance SatModel Double where
  parseCWs (CW KDouble (CWDouble i) : r) = Just (i, r)
  parseCWs _                             = Nothing

instance SatModel CW where
  parseCWs (cw : r) = Just (cw, r)
  parseCWs []       = Nothing

-- | A list of values as extracted from a model. When reading a list, we
-- go as long as we can (maximal-munch). Note that this never fails, as
-- we can always return the empty list!
instance SatModel a => SatModel [a] where
  parseCWs [] = Just ([], [])
  parseCWs xs = case parseCWs xs of
                  Just (a, ys) -> case parseCWs ys of
                                    Just (as, zs) -> Just (a:as, zs)
                                    Nothing       -> Just ([], ys)
                  Nothing     -> Just ([], xs)

-- | Tuples extracted from a model
instance (SatModel a, SatModel b) => SatModel (a, b) where
  parseCWs as = do (a, bs) <- parseCWs as
                   (b, cs) <- parseCWs bs
                   return ((a, b), cs)

-- | 3-Tuples extracted from a model
instance (SatModel a, SatModel b, SatModel c) => SatModel (a, b, c) where
  parseCWs as = do (a,      bs) <- parseCWs as
                   ((b, c), ds) <- parseCWs bs
                   return ((a, b, c), ds)

-- | 4-Tuples extracted from a model
instance (SatModel a, SatModel b, SatModel c, SatModel d) => SatModel (a, b, c, d) where
  parseCWs as = do (a,         bs) <- parseCWs as
                   ((b, c, d), es) <- parseCWs bs
                   return ((a, b, c, d), es)

-- | 5-Tuples extracted from a model
instance (SatModel a, SatModel b, SatModel c, SatModel d, SatModel e) => SatModel (a, b, c, d, e) where
  parseCWs as = do (a, bs)            <- parseCWs as
                   ((b, c, d, e), fs) <- parseCWs bs
                   return ((a, b, c, d, e), fs)

-- | 6-Tuples extracted from a model
instance (SatModel a, SatModel b, SatModel c, SatModel d, SatModel e, SatModel f) => SatModel (a, b, c, d, e, f) where
  parseCWs as = do (a, bs)               <- parseCWs as
                   ((b, c, d, e, f), gs) <- parseCWs bs
                   return ((a, b, c, d, e, f), gs)

-- | 7-Tuples extracted from a model
instance (SatModel a, SatModel b, SatModel c, SatModel d, SatModel e, SatModel f, SatModel g) => SatModel (a, b, c, d, e, f, g) where
  parseCWs as = do (a, bs)                  <- parseCWs as
                   ((b, c, d, e, f, g), hs) <- parseCWs bs
                   return ((a, b, c, d, e, f, g), hs)

-- | Various SMT results that we can extract models out of.
class Modelable a where
  -- | Is there a model?
  modelExists :: a -> Bool
  -- | Extract a model, the result is a tuple where the first argument (if True)
  -- indicates whether the model was "probable". (i.e., if the solver returned unknown.)
  getModel :: SatModel b => a -> Either String (Bool, b)
  -- | Extract a model dictionary. Extract a dictionary mapping the variables to
  -- their respective values as returned by the SMT solver. Also see `getModelDictionaries`.
  getModelDictionary :: a -> M.Map String CW
  -- | Extract a model value for a given element. Also see `getModelValues`.
  getModelValue :: SymWord b => String -> a -> Maybe b
  getModelValue v r = fromCW `fmap` (v `M.lookup` getModelDictionary r)
  -- | Extract a representative name for the model value of an uninterpreted kind.
  -- This is supposed to correspond to the value as computed internally by the
  -- SMT solver; and is unportable from solver to solver. Also see `getModelUninterpretedValues`.
  getModelUninterpretedValue :: String -> a -> Maybe String
  getModelUninterpretedValue v r = case v `M.lookup` getModelDictionary r of
                                     Just (CW _ (CWUserSort (_, s))) -> Just s
                                     _                               -> Nothing

  -- | A simpler variant of 'getModel' to get a model out without the fuss.
  extractModel :: SatModel b => a -> Maybe b
  extractModel a = case getModel a of
                     Right (_, b) -> Just b
                     _            -> Nothing

-- | Return all the models from an 'allSat' call, similar to 'extractModel' but
-- is suitable for the case of multiple results.
extractModels :: SatModel a => AllSatResult -> [a]
extractModels (AllSatResult (_, xs)) = [ms | Right (_, ms) <- map getModel xs]

-- | Get dictionaries from an all-sat call. Similar to `getModelDictionary`.
getModelDictionaries :: AllSatResult -> [M.Map String CW]
getModelDictionaries (AllSatResult (_, xs)) = map getModelDictionary xs

-- | Extract value of a variable from an all-sat call. Similar to `getModelValue`.
getModelValues :: SymWord b => String -> AllSatResult -> [Maybe b]
getModelValues s (AllSatResult (_, xs)) =  map (s `getModelValue`) xs

-- | Extract value of an uninterpreted variable from an all-sat call. Similar to `getModelUninterpretedValue`.
getModelUninterpretedValues :: String -> AllSatResult -> [Maybe String]
getModelUninterpretedValues s (AllSatResult (_, xs)) =  map (s `getModelUninterpretedValue`) xs

-- | 'ThmResult' as a generic model provider
instance Modelable ThmResult where
  getModel           (ThmResult r) = getModel r
  modelExists        (ThmResult r) = modelExists r
  getModelDictionary (ThmResult r) = getModelDictionary r

-- | 'SatResult' as a generic model provider
instance Modelable SatResult where
  getModel           (SatResult r) = getModel r
  modelExists        (SatResult r) = modelExists r
  getModelDictionary (SatResult r) = getModelDictionary r

-- | 'SMTResult' as a generic model provider
instance Modelable SMTResult where
  getModel (Unsatisfiable _) = Left "SBV.getModel: Unsatisfiable result"
  getModel (Unknown _ m)     = Right (True, parseModelOut m)
  getModel (ProofError _ s)  = error $ unlines $ "Backend solver complains: " : s
  getModel (TimeOut _)       = Left "Timeout"
  getModel (Satisfiable _ m) = Right (False, parseModelOut m)
  modelExists (Satisfiable{}) = True
  modelExists (Unknown{})     = False -- don't risk it
  modelExists _               = False
  getModelDictionary (Unsatisfiable _) = M.empty
  getModelDictionary (Unknown _ m)     = M.fromList (modelAssocs m)
  getModelDictionary (ProofError _ _)  = M.empty
  getModelDictionary (TimeOut _)       = M.empty
  getModelDictionary (Satisfiable _ m) = M.fromList (modelAssocs m)

-- | Extract a model out, will throw error if parsing is unsuccessful
parseModelOut :: SatModel a => SMTModel -> a
parseModelOut m = case parseCWs [c | (_, c) <- modelAssocs m] of
                   Just (x, []) -> x
                   Just (_, ys) -> error $ "SBV.getModel: Partially constructed model; remaining elements: " ++ show ys
                   Nothing      -> error $ "SBV.getModel: Cannot construct a model from: " ++ show m

-- | Given an 'allSat' call, we typically want to iterate over it and print the results in sequence. The
-- 'displayModels' function automates this task by calling 'disp' on each result, consecutively. The first
-- 'Int' argument to 'disp' 'is the current model number. The second argument is a tuple, where the first
-- element indicates whether the model is alleged (i.e., if the solver is not sure, returing Unknown)
displayModels :: SatModel a => (Int -> (Bool, a) -> IO ()) -> AllSatResult -> IO Int
displayModels disp (AllSatResult (_, ms)) = do
    inds <- zipWithM display [a | Right a <- map (getModel . SatResult) ms] [(1::Int)..]
    return $ last (0:inds)
  where display r i = disp i r >> return i

-- | Show an SMTResult; generic version
showSMTResult :: String -> String -> String -> String -> String -> SMTResult -> String
showSMTResult unsatMsg unkMsg unkMsgModel satMsg satMsgModel result = case result of
  Unsatisfiable _                   -> unsatMsg
  Satisfiable _ (SMTModel [] [] []) -> satMsg
  Satisfiable _ m                   -> satMsgModel ++ showModel cfg m
  Unknown _ (SMTModel [] [] [])     -> unkMsg
  Unknown _ m                       -> unkMsgModel ++ showModel cfg m
  ProofError _ []                   -> "*** An error occurred. No additional information available. Try running in verbose mode"
  ProofError _ ls                   -> "*** An error occurred.\n" ++ intercalate "\n" (map ("***  " ++) ls)
  TimeOut _                         -> "*** Timeout"
 where cfg = resultConfig result

-- | Show a model in human readable form
showModel :: SMTConfig -> SMTModel -> String
showModel cfg m = intercalate "\n" (map shM assocs ++ concatMap shUI uninterps ++ concatMap shUA arrs)
  where assocs     = modelAssocs m
        uninterps  = modelUninterps m
        arrs       = modelArrays m
        shM (s, v) = "  " ++ s ++ " = " ++ shCW cfg v

-- | Show a constant value, in the user-specified base
shCW :: SMTConfig -> CW -> String
shCW = sh . printBase
  where sh 2  = binS
        sh 10 = show
        sh 16 = hexS
        sh n  = \w -> show w ++ " -- Ignoring unsupported printBase " ++ show n ++ ", use 2, 10, or 16."

-- | Print uninterpreted function values from models. Very, very crude..
shUI :: (String, [String]) -> [String]
shUI (flong, cases) = ("  -- uninterpreted: " ++ f) : map shC cases
  where tf = dropWhile (/= '_') flong
        f  =  if null tf then flong else tail tf
        shC s = "       " ++ s

-- | Print uninterpreted array values from models. Very, very crude..
shUA :: (String, [String]) -> [String]
shUA (f, cases) = ("  -- array: " ++ f) : map shC cases
  where shC s = "       " ++ s

-- | Helper function to spin off to an SMT solver.
pipeProcess :: SMTConfig -> String -> [String] -> SMTScript -> (String -> String) -> IO (Either String [String])
pipeProcess cfg execName opts script cleanErrs = do
        let nm = show (name (solver cfg))
        mbExecPath <- findExecutable execName
        case mbExecPath of
          Nothing       -> return $ Left $ "Unable to locate executable for " ++ nm
                                        ++ "\nExecutable specified: " ++ show execName
          Just execPath ->
                   do solverResult <- dispatchSolver cfg execPath opts script
                      case solverResult of
                        Left s                          -> return $ Left s
                        Right (ec, contents, allErrors) ->
                          let errors = dropWhile isSpace (cleanErrs allErrors)
                          in case (null errors, xformExitCode (solver cfg) ec) of
                                (True, ExitSuccess)  -> return $ Right $ map clean (filter (not . null) (lines contents))
                                (_, ec')             -> let errors' = if null errors
                                                                      then (if null (dropWhile isSpace contents)
                                                                            then "(No error message printed on stderr by the executable.)"
                                                                            else contents)
                                                                      else errors
                                                            finalEC = case (ec', ec) of
                                                                        (ExitFailure n, _) -> n
                                                                        (_, ExitFailure n) -> n
                                                                        _                  -> 0 -- can happen if ExitSuccess but there is output on stderr
                                                        in return $ Left $  "Failed to complete the call to " ++ nm
                                                                         ++ "\nExecutable   : " ++ show execPath
                                                                         ++ "\nOptions      : " ++ unwords opts
                                                                         ++ "\nExit code    : " ++ show finalEC
                                                                         ++ "\nSolver output: "
                                                                         ++ "\n" ++ line ++ "\n"
                                                                         ++ intercalate "\n" (filter (not . null) (lines errors'))
                                                                         ++ "\n" ++ line
                                                                         ++ "\nGiving up.."
  where clean = reverse . dropWhile isSpace . reverse . dropWhile isSpace
        line  = replicate 78 '='

-- | A standard solver interface. If the solver is SMT-Lib compliant, then this function should suffice in
-- communicating with it.
standardSolver :: SMTConfig -> SMTScript -> (String -> String) -> ([String] -> a) -> ([String] -> a) -> IO a
standardSolver config script cleanErrs failure success = do
    let msg      = when (verbose config) . putStrLn . ("** " ++)
        smtSolver= solver config
        exec     = executable smtSolver
        opts     = options smtSolver
        isTiming = timing config
        nmSolver = show (name smtSolver)
    msg $ "Calling: " ++ show (unwords (exec:opts))
    case smtFile config of
      Nothing -> return ()
      Just f  -> do msg $ "Saving the generated script in file: " ++ show f
                    writeFile f (scriptBody script)
    contents <- timeIf isTiming nmSolver $ pipeProcess config  exec opts script cleanErrs
    msg $ nmSolver ++ " output:\n" ++ either id (intercalate "\n") contents
    case contents of
      Left e   -> return $ failure (lines e)
      Right xs -> return $ success (mergeSExpr xs)

-- | Wrap the solver call to protect against any exceptions
dispatchSolver :: SMTConfig -> FilePath -> [String] -> SMTScript -> IO (Either String (ExitCode, String, String))
dispatchSolver cfg execPath opts script = rnf script `seq` (Right `fmap` runSolver cfg execPath opts script) `C.catch` (\(e::C.SomeException) -> bad (show e))
  where bad s = return $ Left $ unlines [ "Failed to start the external solver: " ++ s
                                        , "Make sure you can start " ++ show execPath
                                        , "from the command line without issues."
                                        ]

-- | A variant of 'readProcessWithExitCode'; except it knows about continuation strings
-- and can speak SMT-Lib2 (just a little).
runSolver :: SMTConfig -> FilePath -> [String] -> SMTScript -> IO (ExitCode, String, String)
runSolver cfg execPath opts script
 = do (send, ask, cleanUp, pid) <- do
                (inh, outh, errh, pid) <- runInteractiveProcess execPath opts Nothing Nothing
                let send l    = hPutStr inh (l ++ "\n") >> hFlush inh
                    recv      = hGetLine outh
                    ask l     = send l >> recv
                    cleanUp response
                        = do hClose inh
                             outMVar <- newEmptyMVar
                             out <- hGetContents outh
                             _ <- forkIO $ C.evaluate (length out) >> putMVar outMVar ()
                             err <- hGetContents errh
                             _ <- forkIO $ C.evaluate (length err) >> putMVar outMVar ()
                             takeMVar outMVar
                             takeMVar outMVar
                             hClose outh
                             hClose errh
                             ex <- waitForProcess pid
                             return $ case response of
                                        Nothing        -> (ex, out, err)
                                        Just (r, vals) -> -- if the status is unknown, prepare for the possibility of not having a model
                                                          -- TBD: This is rather crude and potentially Z3 specific
                                                          let finalOut = intercalate "\n" (r : vals)
                                                          in if "unknown" `isPrefixOf` r && "error" `isInfixOf` (out ++ err)
                                                             then (ExitSuccess, finalOut               , "")
                                                             else (ex,          finalOut ++ "\n" ++ out, err)
                return (send, ask, cleanUp, pid)
      let executeSolver = do mapM_ send (lines (scriptBody script))
                             response <- case scriptModel script of
                                           Nothing -> do send $ satCmd cfg
                                                         return Nothing
                                           Just ls -> do r <- ask $ satCmd cfg
                                                         vals <- if any (`isPrefixOf` r) ["sat", "unknown"]
                                                                 then do let mls = lines ls
                                                                         when (verbose cfg) $ do putStrLn "** Sending the following model extraction commands:"
                                                                                                 mapM_ putStrLn mls
                                                                         mapM ask mls
                                                                 else return []
                                                         return $ Just (r, vals)
                             cleanUp response
      executeSolver `C.onException`  terminateProcess pid

-- | In case the SMT-Lib solver returns a response over multiple lines, compress them so we have
-- each S-Expression spanning only a single line. We'll ignore things line parentheses inside quotes
-- etc., as it should not be an issue
mergeSExpr :: [String] -> [String]
mergeSExpr []       = []
mergeSExpr (x:xs)
 | d == 0 = x : mergeSExpr xs
 | True   = let (f, r) = grab d xs in unwords (x:f) : mergeSExpr r
 where d = parenDiff x
       parenDiff :: String -> Int
       parenDiff = go 0
         where go i ""       = i
               go i ('(':cs) = let i'= i+1 in i' `seq` go i' cs
               go i (')':cs) = let i'= i-1 in i' `seq` go i' cs
               go i (_  :cs) = go i cs
       grab i ls
         | i <= 0    = ([], ls)
       grab _ []     = ([], [])
       grab i (l:ls) = let (a, b) = grab (i+parenDiff l) ls in (l:a, b)
