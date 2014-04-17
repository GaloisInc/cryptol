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

module Data.SBV.SMT.SMT where

import qualified Control.Exception as C

import Control.Concurrent (newEmptyMVar, takeMVar, putMVar, forkIO)
import Control.DeepSeq    (NFData(..))
import Control.Monad      (when, zipWithM)
import Data.Char          (isSpace)
import Data.Int           (Int8, Int16, Int32, Int64)
import Data.List          (intercalate, isPrefixOf, isInfixOf)
import Data.Maybe         (isNothing, fromJust)
import Data.Word          (Word8, Word16, Word32, Word64)
import System.Directory   (findExecutable)
import System.Process     (readProcessWithExitCode, runInteractiveProcess, waitForProcess)
import System.Exit        (ExitCode(..))
import System.IO          (hClose, hFlush, hPutStr, hGetContents, hGetLine)

import Data.SBV.BitVectors.AlgReals
import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.PrettyNum
import Data.SBV.Utils.TDiff

-- | Solver configuration. See also 'z3', 'yices', 'cvc4', and 'boolector, which are instantiations of this type for those solvers, with
-- reasonable defaults. In particular, custom configuration can be created by varying those values. (Such as @z3{verbose=True}@.)
--
-- Most fields are self explanatory. The notion of precision for printing algebraic reals stems from the fact that such values does
-- not necessarily have finite decimal representations, and hence we have to stop printing at some depth. It is important to
-- emphasize that such values always have infinite precision internally. The issue is merely with how we print such an infinite
-- precision value on the screen. The field 'printRealPrec' controls the printing precision, by specifying the number of digits after
-- the decimal point. The default value is 16, but it can be set to any positive integer.
--
-- When printing, SBV will add the suffix @...@ at the and of a real-value, if the given bound is not sufficient to represent the real-value
-- exactly. Otherwise, the number will be written out in standard decimal notation. Note that SBV will always print the whole value if it
-- is precise (i.e., if it fits in a finite number of digits), regardless of the precision limit. The limit only applies if the representation
-- of the real value is not finite, i.e., if it is not rational.
data SMTConfig = SMTConfig {
         verbose       :: Bool           -- ^ Debug mode
       , timing        :: Bool           -- ^ Print timing information on how long different phases took (construction, solving, etc.)
       , timeOut       :: Maybe Int      -- ^ How much time to give to the solver. (In seconds)
       , printBase     :: Int            -- ^ Print integral literals in this base (2, 8, and 10, and 16 are supported.)
       , printRealPrec :: Int            -- ^ Print algebraic real values with this precision. (SReal, default: 16)
       , solverTweaks  :: [String]       -- ^ Additional lines of script to give to the solver (user specified)
       , satCmd        :: String         -- ^ Usually "(check-sat)". However, users might tweak it based on solver characteristics.
       , smtFile       :: Maybe FilePath -- ^ If Just, the generated SMT script will be put in this file (for debugging purposes mostly)
       , useSMTLib2    :: Bool           -- ^ If True, we'll treat the solver as using SMTLib2 input format. Otherwise, SMTLib1
       , solver        :: SMTSolver      -- ^ The actual SMT solver.
       , roundingMode  :: RoundingMode   -- ^ Rounding mode to use for floating-point conversions
       }

-- | An SMT engine
type SMTEngine = SMTConfig -> Bool -> [(Quantifier, NamedSymVar)] -> [(String, UnintKind)] -> [Either SW (SW, [SW])] -> String -> IO SMTResult

-- | An SMT solver
data SMTSolver = SMTSolver {
         name           :: String               -- ^ Printable name of the solver
       , executable     :: String               -- ^ The path to its executable
       , options        :: [String]             -- ^ Options to provide to the solver
       , engine         :: SMTEngine            -- ^ The solver engine, responsible for interpreting solver output
       , xformExitCode  :: ExitCode -> ExitCode -- ^ Should we re-interpret exit codes. Most solvers behave rationally, i.e., id will do. Some (like CVC4) don't.
       , capabilities   :: SolverCapabilities   -- ^ Various capabilities of the solver
       }

-- | A model, as returned by a solver
data SMTModel = SMTModel {
        modelAssocs    :: [(String, CW)]
     ,  modelArrays    :: [(String, [String])]  -- very crude!
     ,  modelUninterps :: [(String, [String])]  -- very crude!
     }
     deriving Show

-- | The result of an SMT solver call. Each constructor is tagged with
-- the 'SMTConfig' that created it so that further tools can inspect it
-- and build layers of results, if needed. For ordinary uses of the library,
-- this type should not be needed, instead use the accessor functions on
-- it. (Custom Show instances and model extractors.)
data SMTResult = Unsatisfiable SMTConfig            -- ^ Unsatisfiable
               | Satisfiable   SMTConfig SMTModel   -- ^ Satisfiable with model
               | Unknown       SMTConfig SMTModel   -- ^ Prover returned unknown, with a potential (possibly bogus) model
               | ProofError    SMTConfig [String]   -- ^ Prover errored out
               | TimeOut       SMTConfig            -- ^ Computation timed out (see the 'timeout' combinator)

-- | A script, to be passed to the solver.
data SMTScript = SMTScript {
          scriptBody  :: String        -- ^ Initial feed
        , scriptModel :: Maybe String  -- ^ Optional continuation script, if the result is sat
        }

-- | Extract the final configuration from a result
resultConfig :: SMTResult -> SMTConfig
resultConfig (Unsatisfiable c) = c
resultConfig (Satisfiable c _) = c
resultConfig (Unknown c _)     = c
resultConfig (ProofError c _)  = c
resultConfig (TimeOut c)       = c

instance NFData SMTResult where
  rnf (Unsatisfiable _)   = ()
  rnf (Satisfiable _ xs)  = rnf xs `seq` ()
  rnf (Unknown _ xs)      = rnf xs `seq` ()
  rnf (ProofError _ xs)   = rnf xs `seq` ()
  rnf (TimeOut _)         = ()

instance NFData SMTModel where
  rnf (SMTModel assocs unints uarrs) = rnf assocs `seq` rnf unints `seq` rnf uarrs `seq` ()

-- | A 'prove' call results in a 'ThmResult'
newtype ThmResult    = ThmResult    SMTResult

-- | A 'sat' call results in a 'SatResult'
-- The reason for having a separate 'SatResult' is to have a more meaningful 'Show' instance.
newtype SatResult    = SatResult    SMTResult

-- | An 'allSat' call results in a 'AllSatResult'. The boolean says whether
-- we should warn the user about prefix-existentials.
newtype AllSatResult = AllSatResult (Bool, [SMTResult])

instance Show ThmResult where
  show (ThmResult r) = showSMTResult "Q.E.D."
                                     "Unknown"     "Unknown. Potential counter-example:\n"
                                     "Falsifiable" "Falsifiable. Counter-example:\n" r

instance Show SatResult where
  show (SatResult r) = showSMTResult "Unsatisfiable"
                                     "Unknown"     "Unknown. Potential model:\n"
                                     "Satisfiable" "Satisfiable. Model:\n" r

-- NB. The Show instance of AllSatResults have to be careful in being lazy enough
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

-- | Parse a signed/sized value from a sequence of CWs
genParse :: Integral a => Kind -> [CW] -> Maybe (a, [CW])
genParse k (x@(CW _ (CWInteger i)):r) | kindOf x == k = Just (fromIntegral i, r)
genParse _ _                                          = Nothing

-- Base case, that comes in handy if there are no real variables
instance SatModel () where
  parseCWs xs = return ((), xs)

instance SatModel Bool where
  parseCWs xs = do (x, r) <- genParse (KBounded False 1) xs
                   return ((x :: Integer) /= 0, r)

instance SatModel Word8 where
  parseCWs = genParse (KBounded False 8)

instance SatModel Int8 where
  parseCWs = genParse (KBounded True 8)

instance SatModel Word16 where
  parseCWs = genParse (KBounded False 16)

instance SatModel Int16 where
  parseCWs = genParse (KBounded True 16)

instance SatModel Word32 where
  parseCWs = genParse (KBounded False 32)

instance SatModel Int32 where
  parseCWs = genParse (KBounded True 32)

instance SatModel Word64 where
  parseCWs = genParse (KBounded False 64)

instance SatModel Int64 where
  parseCWs = genParse (KBounded True 64)

instance SatModel Integer where
  parseCWs = genParse KUnbounded

instance SatModel AlgReal where
  parseCWs (CW KReal (CWAlgReal i) : r) = Just (i, r)
  parseCWs _                            = Nothing

instance SatModel CW where
  parseCWs (cw : r) = Just (cw, r)
  parseCWs []       = Nothing

-- when reading a list; go as long as we can (maximal-munch)
-- note that this never fails..
instance SatModel a => SatModel [a] where
  parseCWs [] = Just ([], [])
  parseCWs xs = case parseCWs xs of
                  Just (a, ys) -> case parseCWs ys of
                                    Just (as, zs) -> Just (a:as, zs)
                                    Nothing       -> Just ([], ys)
                  Nothing     -> Just ([], xs)

instance (SatModel a, SatModel b) => SatModel (a, b) where
  parseCWs as = do (a, bs) <- parseCWs as
                   (b, cs) <- parseCWs bs
                   return ((a, b), cs)

instance (SatModel a, SatModel b, SatModel c) => SatModel (a, b, c) where
  parseCWs as = do (a,      bs) <- parseCWs as
                   ((b, c), ds) <- parseCWs bs
                   return ((a, b, c), ds)

instance (SatModel a, SatModel b, SatModel c, SatModel d) => SatModel (a, b, c, d) where
  parseCWs as = do (a,         bs) <- parseCWs as
                   ((b, c, d), es) <- parseCWs bs
                   return ((a, b, c, d), es)

instance (SatModel a, SatModel b, SatModel c, SatModel d, SatModel e) => SatModel (a, b, c, d, e) where
  parseCWs as = do (a, bs)            <- parseCWs as
                   ((b, c, d, e), fs) <- parseCWs bs
                   return ((a, b, c, d, e), fs)

instance (SatModel a, SatModel b, SatModel c, SatModel d, SatModel e, SatModel f) => SatModel (a, b, c, d, e, f) where
  parseCWs as = do (a, bs)               <- parseCWs as
                   ((b, c, d, e, f), gs) <- parseCWs bs
                   return ((a, b, c, d, e, f), gs)

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

  -- | A simpler variant of 'getModel' to get a model out without the fuss.
  extractModel :: SatModel b => a -> Maybe b
  extractModel a = case getModel a of
                     Right (_, b) -> Just b
                     _            -> Nothing

-- | Return all the models from an 'allSat' call, similar to 'extractModel' but
-- is suitable for the case of multiple results.
extractModels :: SatModel a => AllSatResult -> [a]
extractModels (AllSatResult (_, xs)) = [ms | Right (_, ms) <- map getModel xs]

instance Modelable ThmResult where
  getModel    (ThmResult r) = getModel r
  modelExists (ThmResult r) = modelExists r

instance Modelable SatResult where
  getModel    (SatResult r) = getModel r
  modelExists (SatResult r) = modelExists r

instance Modelable SMTResult where
  getModel (Unsatisfiable _) = Left "SBV.getModel: Unsatisfiable result"
  getModel (Unknown _ m)     = Right (True, parseModelOut m)
  getModel (ProofError _ s)  = error $ unlines $ "Backend solver complains: " : s
  getModel (TimeOut _)       = Left "Timeout"
  getModel (Satisfiable _ m) = Right (False, parseModelOut m)
  modelExists (Satisfiable{}) = True
  modelExists (Unknown{})     = False -- don't risk it
  modelExists _               = False

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
pipeProcess :: SMTConfig -> String -> String -> [String] -> SMTScript -> (String -> String) -> IO (Either String [String])
pipeProcess cfg nm execName opts script cleanErrs = do
        mbExecPath <- findExecutable execName
        case mbExecPath of
          Nothing -> return $ Left $ "Unable to locate executable for " ++ nm
                                   ++ "\nExecutable specified: " ++ show execName
          Just execPath -> do (ec, contents, allErrors) <- runSolver cfg execPath opts script
                              let errors = dropWhile isSpace (cleanErrs allErrors)
                              case (null errors, xformExitCode (solver cfg) ec) of
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
        nmSolver = name smtSolver
    msg $ "Calling: " ++ show (unwords (exec:opts))
    case smtFile config of
      Nothing -> return ()
      Just f  -> do putStrLn $ "** Saving the generated script in file: " ++ show f
                    writeFile f (scriptBody script)
    contents <- timeIf isTiming nmSolver $ pipeProcess config nmSolver exec opts script cleanErrs
    msg $ nmSolver ++ " output:\n" ++ either id (intercalate "\n") contents
    case contents of
      Left e   -> return $ failure (lines e)
      Right xs -> return $ success (mergeSExpr xs)

-- | A variant of 'readProcessWithExitCode'; except it knows about continuation strings
-- and can speak SMT-Lib2 (just a little).
runSolver :: SMTConfig -> FilePath -> [String] -> SMTScript -> IO (ExitCode, String, String)
runSolver cfg execPath opts script
 | isNothing $ scriptModel script
 = let checkCmd | useSMTLib2 cfg = '\n' : satCmd cfg
                | True           = ""
   in readProcessWithExitCode execPath opts (scriptBody script ++ checkCmd)
 | True
 = do (send, ask, cleanUp) <- do
                (inh, outh, errh, pid) <- runInteractiveProcess execPath opts Nothing Nothing
                let send l    = hPutStr inh (l ++ "\n") >> hFlush inh
                    recv      = hGetLine outh `C.catch` (\(_ :: C.SomeException) -> return "")
                    ask l     = send l >> recv
                    cleanUp r = do outMVar <- newEmptyMVar
                                   out <- hGetContents outh
                                   _ <- forkIO $ C.evaluate (length out) >> putMVar outMVar ()
                                   err <- hGetContents errh
                                   _ <- forkIO $ C.evaluate (length err) >> putMVar outMVar ()
                                   hClose inh
                                   takeMVar outMVar
                                   takeMVar outMVar
                                   hClose outh
                                   hClose errh
                                   ex <- waitForProcess pid
                                   -- if the status is unknown, prepare for the possibility of not having a model
                                   -- TBD: This is rather crude and potentially Z3 specific
                                   return $ if "unknown" `isPrefixOf` r && "error" `isInfixOf` (out ++ err)
                                            then (ExitSuccess, r               , "")
                                            else (ex,          r ++ "\n" ++ out, err)
                return (send, ask, cleanUp)
      mapM_ send (lines (scriptBody script))
      r <- ask $ satCmd cfg
      when (any (`isPrefixOf` r) ["sat", "unknown"]) $ do
        let mls = lines (fromJust (scriptModel script))
        when (verbose cfg) $ do putStrLn "** Sending the following model extraction commands:"
                                mapM_ putStrLn mls
        mapM_ send mls
      cleanUp r

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
