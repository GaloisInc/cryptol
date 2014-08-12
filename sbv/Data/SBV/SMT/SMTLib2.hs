----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.SMT.SMTLib2
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Conversion of symbolic programs to SMTLib format, Using v2 of the standard
-----------------------------------------------------------------------------
{-# LANGUAGE PatternGuards #-}

module Data.SBV.SMT.SMTLib2(cvt, addNonEqConstraints) where

import Data.Bits     (bit)
import Data.Char     (intToDigit)
import Data.Function (on)
import Data.Ord      (comparing)
import qualified Data.Foldable as F (toList)
import qualified Data.Map      as M
import qualified Data.IntMap   as IM
import qualified Data.Set      as Set
import Data.List (intercalate, partition, groupBy, sortBy)
import Numeric (showIntAtBase, showHex)

import Data.SBV.BitVectors.AlgReals
import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.PrettyNum (showSMTFloat, showSMTDouble, smtRoundingMode)

-- | Add constraints to generate /new/ models. This function is used to query the SMT-solver, while
-- disallowing a previous model.
addNonEqConstraints :: RoundingMode -> [(Quantifier, NamedSymVar)] -> [[(String, CW)]] -> SMTLibPgm -> Maybe String
addNonEqConstraints rm qinps allNonEqConstraints (SMTLibPgm _ (aliasTable, pre, post))
  | null allNonEqConstraints
  = Just $ intercalate "\n" $ pre ++ post
  | null refutedModel
  = Nothing
  | True
  = Just $ intercalate "\n" $ pre
    ++ [ "; --- refuted-models ---" ]
    ++ refutedModel
    ++ post
 where refutedModel = concatMap (nonEqs rm) (map (map intName) nonEqConstraints)
       intName (s, c)
          | Just sw <- s `lookup` aliasTable = (show sw, c)
          | True                             = (s, c)
       -- with existentials, we only add top-level existentials to the refuted-models list
       nonEqConstraints = filter (not . null) $ map (filter (\(s, _) -> s `elem` topUnivs)) allNonEqConstraints
       topUnivs = [s | (_, (_, s)) <- takeWhile (\p -> fst p == EX) qinps]

nonEqs :: RoundingMode -> [(String, CW)] -> [String]
nonEqs rm scs = format $ interp ps ++ disallow (map eqClass uninterpClasses)
  where (ups, ps) = partition (isUninterpreted . snd) scs
        format []     =  []
        format [m]    =  ["(assert " ++ m ++ ")"]
        format (m:ms) =  ["(assert (or " ++ m]
                      ++ map ("            " ++) ms
                      ++ ["        ))"]
        -- Regular (or interpreted) sorts simply get a constraint that we disallow the current assignment
        interp = map $ nonEq rm
        -- Determine the equivalnce classes of uninterpreted sorts:
        uninterpClasses = filter (\l -> length l > 1) -- Only need this class if it has at least two members
                        . map (map fst)               -- throw away sorts, we only need the names
                        . groupBy ((==) `on` snd)     -- make sure they belong to the same sort and have the same value
                        . sortBy (comparing snd)      -- sort them according to their sorts first
                        $ ups                         -- take the uninterpreted sorts
        -- Uninterpreted sorts get a constraint that says the equivalence classes as determined by the solver are disallowed:
        eqClass :: [String] -> String
        eqClass [] = error "SBV.allSat.nonEqs: Impossible happened, disallow received an empty list"
        eqClass cs = "(= " ++ unwords cs ++ ")"
        -- Now, take the conjunction of equivalence classes and assert it's negation:
        disallow = map $ \ec -> "(not " ++ ec ++ ")"

nonEq :: RoundingMode -> (String, CW) -> String
nonEq rm (s, c) = "(not (= " ++ s ++ " " ++ cvtCW rm c ++ "))"

tbd :: String -> a
tbd e = error $ "SBV.SMTLib2: Not-yet-supported: " ++ e

-- | Translate a problem into an SMTLib2 script
cvt :: RoundingMode                 -- ^ User selected rounding mode to be used for floating point arithmetic
    -> Maybe Logic                  -- ^ SMT-Lib logic, if requested by the user
    -> SolverCapabilities           -- ^ capabilities of the current solver
    -> Set.Set Kind                 -- ^ kinds used
    -> Bool                         -- ^ is this a sat problem?
    -> [String]                     -- ^ extra comments to place on top
    -> [(Quantifier, NamedSymVar)]  -- ^ inputs
    -> [Either SW (SW, [SW])]       -- ^ skolemized version inputs
    -> [(SW, CW)]                   -- ^ constants
    -> [((Int, Kind, Kind), [SW])]  -- ^ auto-generated tables
    -> [(Int, ArrayInfo)]           -- ^ user specified arrays
    -> [(String, SBVType)]          -- ^ uninterpreted functions/constants
    -> [(String, [String])]         -- ^ user given axioms
    -> SBVPgm                       -- ^ assignments
    -> [SW]                         -- ^ extra constraints
    -> SW                           -- ^ output variable
    -> ([String], [String])
cvt rm smtLogic solverCaps kindInfo isSat comments inputs skolemInps consts tbls arrs uis axs (SBVPgm asgnsSeq) cstrs out = (pre, [])
  where -- the logic is an over-approaximation
        hasInteger = KUnbounded `Set.member` kindInfo
        hasReal    = KReal      `Set.member` kindInfo
        hasFloat   = KFloat     `Set.member` kindInfo
        hasDouble  = KDouble    `Set.member` kindInfo
        hasBVs     = not $ null [() | KBounded{} <- Set.toList kindInfo]
        sorts      = [s | KUninterpreted s <- Set.toList kindInfo]
        logic
           | Just l <- smtLogic
           = ["(set-logic " ++ show l ++ ") ; NB. User specified."]
           | hasDouble || hasFloat    -- NB. We don't check for quantifiers here, we probably should..
           = if hasBVs
             then ["(set-logic QF_FPABV)"]
             else ["(set-logic QF_FPA)"]
           | hasInteger || hasReal || not (null sorts)
           = case mbDefaultLogic solverCaps of
                Nothing -> ["; Has unbounded values (Int/Real) or sorts; no logic specified."]   -- combination, let the solver pick
                Just l  -> ["(set-logic " ++ l ++ ")"]
           | True
           = ["(set-logic " ++ qs ++ as ++ ufs ++ "BV)"]
          where qs  | null foralls && null axs = "QF_"  -- axioms are likely to contain quantifiers
                    | True                     = ""
                as  | null arrs                = ""
                    | True                     = "A"
                ufs | null uis && null tbls    = ""     -- we represent tables as UFs
                    | True                     = "UF"
        getModels
          | supportsProduceModels solverCaps = ["(set-option :produce-models true)"]
          | True                             = []
        pre  =  ["; Automatically generated by SBV. Do not edit."]
             ++ map ("; " ++) comments
             ++ getModels
             ++ logic
             ++ [ "; --- uninterpreted sorts ---" ]
             ++ map declSort sorts
             ++ [ "; --- literal constants ---" ]
             ++ concatMap (declConst (supportsMacros solverCaps)) consts
             ++ [ "; --- skolem constants ---" ]
             ++ [ "(declare-fun " ++ show s ++ " " ++ swFunType ss s ++ ")" ++ userName s | Right (s, ss) <- skolemInps]
             ++ [ "; --- constant tables ---" ]
             ++ concatMap constTable constTables
             ++ [ "; --- skolemized tables ---" ]
             ++ map (skolemTable (unwords (map swType foralls))) skolemTables
             ++ [ "; --- arrays ---" ]
             ++ concat arrayConstants
             ++ [ "; --- uninterpreted constants ---" ]
             ++ concatMap declUI uis
             ++ [ "; --- user given axioms ---" ]
             ++ map declAx axs
             ++ [ "; --- formula ---" ]
             ++ [if null foralls
                 then "(assert ; no quantifiers"
                 else "(assert (forall (" ++ intercalate "\n                 "
                                             ["(" ++ show s ++ " " ++ swType s ++ ")" | s <- foralls] ++ ")"]
             ++ map (letAlign . mkLet) asgns
             ++ map letAlign (if null delayedEqualities then [] else ("(and " ++ deH) : map (align 5) deTs)
             ++ [ impAlign (letAlign assertOut) ++ replicate noOfCloseParens ')' ]
        noOfCloseParens = length asgns + (if null foralls then 1 else 2) + (if null delayedEqualities then 0 else 1)
        (constTables, skolemTables) = ([(t, d) | (t, Left d) <- allTables], [(t, d) | (t, Right d) <- allTables])
        allTables = [(t, genTableData rm skolemMap (not (null foralls), forallArgs) (map fst consts) t) | t <- tbls]
        (arrayConstants, allArrayDelayeds) = unzip $ map (declArray (not (null foralls)) (map fst consts) skolemMap) arrs
        delayedEqualities@(~(deH:deTs)) = concatMap snd skolemTables ++ concat allArrayDelayeds
        foralls = [s | Left s <- skolemInps]
        forallArgs = concatMap ((" " ++) . show) foralls
        letAlign s
          | null foralls = "   " ++ s
          | True         = "            " ++ s
        impAlign s
          | null delayedEqualities = s
          | True                   = "     " ++ s
        align n s = replicate n ' ' ++ s
        -- if sat,   we assert cstrs /\ out
        -- if prove, we assert ~(cstrs => out) = cstrs /\ not out
        assertOut
           | null cstrs = o
           | True       = "(and " ++ unwords (map mkConj cstrs ++ [o]) ++ ")"
           where mkConj = cvtSW skolemMap
                 o | isSat =            mkConj out
                   | True  = "(not " ++ mkConj out ++ ")"
        skolemMap = M.fromList [(s, ss) | Right (s, ss) <- skolemInps, not (null ss)]
        tableMap  = IM.fromList $ map mkConstTable constTables ++ map mkSkTable skolemTables
          where mkConstTable (((t, _, _), _), _) = (t, "table" ++ show t)
                mkSkTable    (((t, _, _), _), _) = (t, "table" ++ show t ++ forallArgs)
        asgns = F.toList asgnsSeq
        mkLet (s, e) = "(let ((" ++ show s ++ " " ++ cvtExp rm skolemMap tableMap e ++ "))"
        declConst useDefFun (s, c)
          | useDefFun = ["(define-fun "   ++ varT ++ " " ++ cvtCW rm c ++ ")"]
          | True      = [ "(declare-fun " ++ varT ++ ")"
                        , "(assert (= "   ++ show s ++ " " ++ cvtCW rm c ++ "))"
                        ]
          where varT = show s ++ " " ++ swFunType [] s
        declSort s = "(declare-sort " ++ s ++ " 0)"
        userName s = case s `lookup` map snd inputs of
                        Just u  | show s /= u -> " ; tracks user variable " ++ show u
                        _ -> ""

declUI :: (String, SBVType) -> [String]
declUI (i, t) = ["(declare-fun " ++ i ++ " " ++ cvtType t ++ ")"]

-- NB. We perform no check to as to whether the axiom is meaningful in any way.
declAx :: (String, [String]) -> String
declAx (nm, ls) = (";; -- user given axiom: " ++ nm ++ "\n") ++ intercalate "\n" ls

constTable :: (((Int, Kind, Kind), [SW]), [String]) -> [String]
constTable (((i, ak, rk), _elts), is) = decl : map wrap is
  where t       = "table" ++ show i
        decl    = "(declare-fun " ++ t ++ " (" ++ smtType ak ++ ") " ++ smtType rk ++ ")"
        wrap  s = "(assert " ++ s ++ ")"

skolemTable :: String -> (((Int, Kind, Kind), [SW]), [String]) -> String
skolemTable qsIn (((i, ak, rk), _elts), _) = decl
  where qs   = if null qsIn then "" else qsIn ++ " "
        t    = "table" ++ show i
        decl = "(declare-fun " ++ t ++ " (" ++ qs ++ smtType ak ++ ") " ++ smtType rk ++ ")"

-- Left if all constants, Right if otherwise
genTableData :: RoundingMode -> SkolemMap -> (Bool, String) -> [SW] -> ((Int, Kind, Kind), [SW]) -> Either [String] [String]
genTableData rm skolemMap (_quantified, args) consts ((i, aknd, _), elts)
  | null post = Left  (map (topLevel . snd) pre)
  | True      = Right (map (nested   . snd) (pre ++ post))
  where ssw = cvtSW skolemMap
        (pre, post) = partition fst (zipWith mkElt elts [(0::Int)..])
        t           = "table" ++ show i
        mkElt x k   = (isReady, (idx, ssw x))
          where idx = cvtCW rm (mkConstCW aknd k)
                isReady = x `elem` consts
        topLevel (idx, v) = "(= (" ++ t ++ " " ++ idx ++ ") " ++ v ++ ")"
        nested   (idx, v) = "(= (" ++ t ++ args ++ " " ++ idx ++ ") " ++ v ++ ")"

-- TODO: We currently do not support non-constant arrays when quantifiers are present, as
-- we might have to skolemize those. Implement this properly.
-- The difficulty is with the ArrayReset/Mutate/Merge: We have to postpone an init if
-- the components are themselves postponed, so this cannot be implemented as a simple map.
declArray :: Bool -> [SW] -> SkolemMap -> (Int, ArrayInfo) -> ([String], [String])
declArray quantified consts skolemMap (i, (_, (aKnd, bKnd), ctx)) = (adecl : map wrap pre, map snd post)
  where topLevel = not quantified || case ctx of
                                       ArrayFree Nothing -> True
                                       ArrayFree (Just sw) -> sw `elem` consts
                                       ArrayReset _ sw     -> sw `elem` consts
                                       ArrayMutate _ a b   -> all (`elem` consts) [a, b]
                                       ArrayMerge c _ _    -> c `elem` consts
        (pre, post) = partition fst ctxInfo
        nm = "array_" ++ show i
        ssw sw
         | topLevel || sw `elem` consts
         = cvtSW skolemMap sw
         | True
         = tbd "Non-constant array initializer in a quantified context"
        adecl = "(declare-fun " ++ nm ++ " () (Array " ++ smtType aKnd ++ " " ++ smtType bKnd ++ "))"
        ctxInfo = case ctx of
                    ArrayFree Nothing   -> []
                    ArrayFree (Just sw) -> declA sw
                    ArrayReset _ sw     -> declA sw
                    ArrayMutate j a b -> [(all (`elem` consts) [a, b], "(= " ++ nm ++ " (store array_" ++ show j ++ " " ++ ssw a ++ " " ++ ssw b ++ "))")]
                    ArrayMerge  t j k -> [(t `elem` consts,            "(= " ++ nm ++ " (ite " ++ ssw t ++ " array_" ++ show j ++ " array_" ++ show k ++ "))")]
        declA sw = let iv = nm ++ "_freeInitializer"
                   in [ (True,             "(declare-fun " ++ iv ++ " () " ++ smtType aKnd ++ ")")
                      , (sw `elem` consts, "(= (select " ++ nm ++ " " ++ iv ++ ") " ++ ssw sw ++ ")")
                      ]
        wrap (False, s) = s
        wrap (True, s)  = "(assert " ++ s ++ ")"

swType :: SW -> String
swType s = smtType (kindOf s)

swFunType :: [SW] -> SW -> String
swFunType ss s = "(" ++ unwords (map swType ss) ++ ") " ++ swType s

smtType :: Kind -> String
smtType KBool              = "Bool"
smtType (KBounded _ sz)    = "(_ BitVec " ++ show sz ++ ")"
smtType KUnbounded         = "Int"
smtType KReal              = "Real"
smtType KFloat             = "(_ FP  8 24)"
smtType KDouble            = "(_ FP 11 53)"
smtType (KUninterpreted s) = s

cvtType :: SBVType -> String
cvtType (SBVType []) = error "SBV.SMT.SMTLib2.cvtType: internal: received an empty type!"
cvtType (SBVType xs) = "(" ++ unwords (map smtType body) ++ ") " ++ smtType ret
  where (body, ret) = (init xs, last xs)

type SkolemMap = M.Map  SW [SW]
type TableMap  = IM.IntMap String

cvtSW :: SkolemMap -> SW -> String
cvtSW skolemMap s
  | Just ss <- s `M.lookup` skolemMap
  = "(" ++ show s ++ concatMap ((" " ++) . show) ss ++ ")"
  | True
  = show s

-- Carefully code hex numbers, SMTLib is picky about lengths of hex constants. For the time
-- being, SBV only supports sizes that are multiples of 4, but the below code is more robust
-- in case of future extensions to support arbitrary sizes.
hex :: Int -> Integer -> String
hex 1  v = "#b" ++ show v
hex sz v
  | sz `mod` 4 == 0 = "#x" ++ pad (sz `div` 4) (showHex v "")
  | True            = "#b" ++ pad sz (showBin v "")
   where pad n s = replicate (n - length s) '0' ++ s
         showBin = showIntAtBase 2 intToDigit

cvtCW :: RoundingMode -> CW -> String
cvtCW rm x
  | isBoolean       x, CWInteger       w <- cwVal x = if w == 0 then "false" else "true"
  | isUninterpreted x, CWUninterpreted s <- cwVal x = s
  | isReal          x, CWAlgReal       r <- cwVal x = algRealToSMTLib2 r
  | isFloat         x, CWFloat         f <- cwVal x = showSMTFloat  rm f
  | isDouble        x, CWDouble        d <- cwVal x = showSMTDouble rm d
  | not (isBounded x), CWInteger       w <- cwVal x = if w >= 0 then show w else "(- " ++ show (abs w) ++ ")"
  | not (hasSign x)  , CWInteger       w <- cwVal x = hex (intSizeOf x) w
  -- signed numbers (with 2's complement representation) is problematic
  -- since there's no way to put a bvneg over a positive number to get minBound..
  -- Hence, we punt and use binary notation in that particular case
  | hasSign x        , CWInteger       w <- cwVal x = if w == negate (2 ^ intSizeOf x)
                                                      then mkMinBound (intSizeOf x)
                                                      else negIf (w < 0) $ hex (intSizeOf x) (abs w)
  | True = error $ "SBV.cvtCW: Impossible happened: Kind/Value disagreement on: " ++ show (kindOf x, x)

negIf :: Bool -> String -> String
negIf True  a = "(bvneg " ++ a ++ ")"
negIf False a = a

-- anamoly at the 2's complement min value! Have to use binary notation here
-- as there is no positive value we can provide to make the bvneg work.. (see above)
mkMinBound :: Int -> String
mkMinBound i = "#b1" ++ replicate (i-1) '0'

getTable :: TableMap -> Int -> String
getTable m i
  | Just tn <- i `IM.lookup` m = tn
  | True                       = error $ "SBV.SMTLib2: Cannot locate table " ++ show i

cvtExp :: RoundingMode -> SkolemMap -> TableMap -> SBVExpr -> String
cvtExp rm skolemMap tableMap expr@(SBVApp _ arguments) = sh expr
  where ssw = cvtSW skolemMap
        bvOp     = all isBounded arguments
        intOp    = any isInteger arguments
        realOp   = any isReal arguments
        doubleOp = any isDouble arguments
        floatOp  = any isFloat arguments
        boolOp   = all isBoolean arguments
        bad | intOp = error $ "SBV.SMTLib2: Unsupported operation on unbounded integers: " ++ show expr
            | True  = error $ "SBV.SMTLib2: Unsupported operation on real values: " ++ show expr
        ensureBVOrBool = bvOp || boolOp || bad
        ensureBV       = bvOp || bad
        addRM s = s ++ " " ++ smtRoundingMode rm
        lift2  o _ [x, y] = "(" ++ o ++ " " ++ x ++ " " ++ y ++ ")"
        lift2  o _ sbvs   = error $ "SBV.SMTLib2.sh.lift2: Unexpected arguments: "   ++ show (o, sbvs)
        -- lift a binary operation with rounding-mode added; used for floating-point arithmetic
        lift2WM o | doubleOp || floatOp = lift2 (addRM o)
                  | True                = lift2 o
        lift2B bOp vOp
          | boolOp = lift2 bOp
          | True   = lift2 vOp
        lift1B bOp vOp
          | boolOp = lift1 bOp
          | True   = lift1 vOp
        eqBV sgn sbvs
           | boolOp = lift2 "=" sgn sbvs
           | True   = "(= " ++ lift2 "bvcomp" sgn sbvs ++ " #b1)"
        neqBV sgn sbvs = "(not " ++ eqBV sgn sbvs ++ ")"
        equal sgn sbvs
          | doubleOp = lift2 "==" sgn sbvs
          | floatOp  = lift2 "==" sgn sbvs
          | True     = lift2 "=" sgn sbvs
        notEqual sgn sbvs
          | doubleOp = "(not " ++ equal sgn sbvs ++ ")"
          | floatOp  = "(not " ++ equal sgn sbvs ++ ")"
          | True     = lift2 "distinct" sgn sbvs
        lift2S oU oS sgn = lift2 (if sgn then oS else oU) sgn
        lift1  o _ [x]    = "(" ++ o ++ " " ++ x ++ ")"
        lift1  o _ sbvs   = error $ "SBV.SMT.SMTLib2.sh.lift1: Unexpected arguments: "   ++ show (o, sbvs)
        sh (SBVApp Ite [a, b, c]) = "(ite " ++ ssw a ++ " " ++ ssw b ++ " " ++ ssw c ++ ")"
        sh (SBVApp (LkUp (t, aKnd, _, l) i e) [])
          | needsCheck = "(ite " ++ cond ++ ssw e ++ " " ++ lkUp ++ ")"
          | True       = lkUp
          where needsCheck = case aKnd of
                              KBool            -> (2::Integer) > fromIntegral l
                              KBounded _ n     -> (2::Integer)^n > fromIntegral l
                              KUnbounded       -> True
                              KReal            -> error "SBV.SMT.SMTLib2.cvtExp: unexpected real valued index"
                              KFloat           -> error "SBV.SMT.SMTLib2.cvtExp: unexpected float valued index"
                              KDouble          -> error "SBV.SMT.SMTLib2.cvtExp: unexpected double valued index"
                              KUninterpreted s -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected uninterpreted valued index: " ++ s
                lkUp = "(" ++ getTable tableMap t ++ " " ++ ssw i ++ ")"
                cond
                 | hasSign i = "(or " ++ le0 ++ " " ++ gtl ++ ") "
                 | True      = gtl ++ " "
                (less, leq) = case aKnd of
                                KBool            -> error "SBV.SMT.SMTLib2.cvtExp: unexpected boolean valued index"
                                KBounded{}       -> if hasSign i then ("bvslt", "bvsle") else ("bvult", "bvule")
                                KUnbounded       -> ("<", "<=")
                                KReal            -> ("<", "<=")
                                KFloat           -> ("<", "<=")
                                KDouble          -> ("<", "<=")
                                KUninterpreted s -> error $ "SBV.SMT.SMTLib2.cvtExp: unexpected uninterpreted valued index: " ++ s
                mkCnst = cvtCW rm . mkConstCW (kindOf i)
                le0  = "(" ++ less ++ " " ++ ssw i ++ " " ++ mkCnst 0 ++ ")"
                gtl  = "(" ++ leq  ++ " " ++ mkCnst l ++ " " ++ ssw i ++ ")"
        sh (SBVApp (ArrEq i j) []) = "(= array_" ++ show i ++ " array_" ++ show j ++")"
        sh (SBVApp (ArrRead i) [a]) = "(select array_" ++ show i ++ " " ++ ssw a ++ ")"
        sh (SBVApp (Uninterpreted nm) [])   = nm
        sh (SBVApp (Uninterpreted nm) args) = "(" ++ nm' ++ " " ++ unwords (map ssw args) ++ ")"
          where -- slight hack needed here to take advantage of custom floating-point functions.. sigh.
                fpSpecials = ["squareRoot", "fusedMA"]
                nm' | (floatOp || doubleOp) && (nm `elem` fpSpecials) = addRM nm
                    | True                                            = nm
        sh (SBVApp (Extract 0 0) [a])   -- special SInteger -> SReal conversion
          | kindOf a == KUnbounded
          = "(to_real " ++ ssw a ++ ")"
        sh (SBVApp (Extract i j) [a]) | ensureBV = "((_ extract " ++ show i ++ " " ++ show j ++ ") " ++ ssw a ++ ")"
        sh (SBVApp (Rol i) [a])
           | bvOp  = rot  ssw "rotate_left"  i a
           | intOp = sh (SBVApp (Shl i) [a])       -- Haskell treats rotateL as shiftL for unbounded values
           | True  = bad
        sh (SBVApp (Ror i) [a])
           | bvOp  = rot  ssw "rotate_right" i a
           | intOp = sh (SBVApp (Shr i) [a])     -- Haskell treats rotateR as shiftR for unbounded values
           | True  = bad
        sh (SBVApp (Shl i) [a])
           | bvOp   = shft rm ssw "bvshl"  "bvshl"  i a
           | i < 0  = sh (SBVApp (Shr (-i)) [a])  -- flip sign/direction
           | intOp  = "(* " ++ ssw a ++ " " ++ show (bit i :: Integer) ++ ")"  -- Implement shiftL by multiplication by 2^i
           | True   = bad
        sh (SBVApp (Shr i) [a])
           | bvOp  = shft rm ssw "bvlshr" "bvashr" i a
           | i < 0 = sh (SBVApp (Shl (-i)) [a])  -- flip sign/direction
           | intOp = "(div " ++ ssw a ++ " " ++ show (bit i :: Integer) ++ ")"  -- Implement shiftR by division by 2^i
           | True  = bad
        sh (SBVApp op args)
          | Just f <- lookup op smtBVOpTable, ensureBVOrBool
          = f (any hasSign args) (map ssw args)
          where -- The first 4 operators below do make sense for Integer's in Haskell, but there's
                -- no obvious counterpart for them in the SMTLib translation.
                -- TODO: provide support for these.
                smtBVOpTable = [ (And,  lift2B "and" "bvand")
                               , (Or,   lift2B "or"  "bvor")
                               , (XOr,  lift2B "xor" "bvxor")
                               , (Not,  lift1B "not" "bvnot")
                               , (Join, lift2 "concat")
                               ]
        sh inp@(SBVApp op args)
          | intOp, Just f <- lookup op smtOpIntTable
          = f True (map ssw args)
          | bvOp, Just f <- lookup op smtOpBVTable
          = f (any hasSign args) (map ssw args)
          | realOp, Just f <- lookup op smtOpRealTable
          = f (any hasSign args) (map ssw args)
          | floatOp || doubleOp, Just f <- lookup op smtOpFloatDoubleTable
          = f (any hasSign args) (map ssw args)
          | Just f <- lookup op uninterpretedTable
          = f (map ssw args)
          | True
          = error $ "SBV.SMT.SMTLib2.cvtExp.sh: impossible happened; can't translate: " ++ show inp
          where smtOpBVTable  = [ (Plus,          lift2   "bvadd")
                                , (Minus,         lift2   "bvsub")
                                , (Times,         lift2   "bvmul")
                                , (Quot,          lift2S  "bvudiv" "bvsdiv")
                                , (Rem,           lift2S  "bvurem" "bvsrem")
                                , (Equal,         eqBV)
                                , (NotEqual,      neqBV)
                                , (LessThan,      lift2S  "bvult" "bvslt")
                                , (GreaterThan,   lift2S  "bvugt" "bvsgt")
                                , (LessEq,        lift2S  "bvule" "bvsle")
                                , (GreaterEq,     lift2S  "bvuge" "bvsge")
                                ]
                smtOpRealTable =  smtIntRealShared
                               ++ [ (Quot,        lift2WM "/")
                                  ]
                smtOpIntTable  = smtIntRealShared
                               ++ [ (Quot,        lift2   "div")
                                  , (Rem,         lift2   "mod")
                                  ]
                smtOpFloatDoubleTable = smtIntRealShared
                                  ++ [(Quot, lift2WM "/")]
                smtIntRealShared  = [ (Plus,          lift2WM "+")
                                    , (Minus,         lift2WM "-")
                                    , (Times,         lift2WM "*")
                                    , (Equal,         equal)
                                    , (NotEqual,      notEqual)
                                    , (LessThan,      lift2S  "<"  "<")
                                    , (GreaterThan,   lift2S  ">"  ">")
                                    , (LessEq,        lift2S  "<=" "<=")
                                    , (GreaterEq,     lift2S  ">=" ">=")
                                    ]
                -- equality is the only thing that works on uninterpreted sorts
                uninterpretedTable = [ (Equal,    lift2S "="        "="        True)
                                     , (NotEqual, lift2S "distinct" "distinct" True)
                                     ]

rot :: (SW -> String) -> String -> Int -> SW -> String
rot ssw o c x = "((_ " ++ o ++ " " ++ show c ++ ") " ++ ssw x ++ ")"

shft :: RoundingMode -> (SW -> String) -> String -> String -> Int -> SW -> String
shft rm ssw oW oS c x = "(" ++ o ++ " " ++ ssw x ++ " " ++ cvtCW rm c' ++ ")"
   where s  = hasSign x
         c' = mkConstCW (kindOf x) c
         o  = if s then oS else oW
