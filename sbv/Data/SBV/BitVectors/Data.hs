-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.BitVectors.Data
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Internal data-structures for the sbv library
-----------------------------------------------------------------------------

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE PatternGuards              #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE NamedFieldPuns             #-}

module Data.SBV.BitVectors.Data
 ( SBool, SWord8, SWord16, SWord32, SWord64
 , SInt8, SInt16, SInt32, SInt64, SInteger, SReal, SFloat, SDouble
 , nan, infinity, sNaN, sInfinity, RoundingMode(..), smtLibSquareRoot, smtLibFusedMA
 , SymWord(..)
 , CW(..), CWVal(..), AlgReal(..), cwSameType, cwIsBit, cwToBool
 , mkConstCW ,liftCW2, mapCW, mapCW2
 , SW(..), trueSW, falseSW, trueCW, falseCW, normCW
 , SBV(..), NodeId(..), mkSymSBV, mkSymSBVWithRandom
 , ArrayContext(..), ArrayInfo, SymArray(..), SFunArray(..), mkSFunArray, SArray(..), arrayUIKind
 , sbvToSW, sbvToSymSW, forceSWArg
 , SBVExpr(..), newExpr
 , cache, Cached, uncache, uncacheAI, HasKind(..)
 , Op(..), NamedSymVar, UnintKind(..), getTableIndex, SBVPgm(..), Symbolic, SExecutable(..), runSymbolic, runSymbolic', State, getPathCondition, extendPathCondition
 , inProofMode, SBVRunMode(..), Kind(..), Outputtable(..), Result(..)
 , Logic(..), SMTLibLogic(..)
 , getTraceInfo, getConstraints, addConstraint
 , SBVType(..), newUninterpreted, unintFnUIKind, addAxiom
 , Quantifier(..), needsExistentials
 , SMTLibPgm(..), SMTLibVersion(..)
 , SolverCapabilities(..)
 , extractSymbolicSimulationState
 , SMTScript(..), Solver(..), SMTSolver(..), SMTResult(..), SMTModel(..), SMTConfig(..), getSBranchRunConfig
 ) where

import Control.DeepSeq      (NFData(..))
import Control.Applicative  (Applicative)
import Control.Monad        (when)
import Control.Monad.Reader (MonadReader, ReaderT, ask, runReaderT)
import Control.Monad.Trans  (MonadIO, liftIO)
import Data.Char            (isAlpha, isAlphaNum)
import Data.Generics        (Data(..), dataTypeName, dataTypeOf, tyconUQname)
import Data.Int             (Int8, Int16, Int32, Int64)
import Data.Word            (Word8, Word16, Word32, Word64)
import Data.IORef           (IORef, newIORef, modifyIORef, readIORef, writeIORef)
import Data.List            (intercalate, sortBy)
import Data.Maybe           (isJust, fromJust)

import qualified Data.IntMap       as IMap (IntMap, empty, size, toAscList, lookup, insert, insertWith)
import qualified Data.Map          as Map  (Map, empty, toList, size, insert, lookup)
import qualified Data.Set          as Set  (Set, empty, toList, insert)
import qualified Data.Foldable     as F    (toList)
import qualified Data.Sequence     as S    (Seq, empty, (|>))

import System.Exit           (ExitCode(..))
import System.Mem.StableName
import System.Random

import Data.SBV.BitVectors.AlgReals
import Data.SBV.Utils.Lib

-- | A constant value
data CWVal = CWAlgReal       AlgReal    -- ^ algebraic real
           | CWInteger       Integer    -- ^ bit-vector/unbounded integer
           | CWFloat         Float      -- ^ float
           | CWDouble        Double     -- ^ double
           | CWUninterpreted String     -- ^ value of an uninterpreted kind

-- We cannot simply derive Eq/Ord for CWVal, since CWAlgReal doesn't have proper
-- instances for these when values are infinitely precise reals. However, we do
-- need a structural eq/ord for Map indexes; so define custom ones here:
instance Eq CWVal where
  CWAlgReal a       == CWAlgReal b       = a `algRealStructuralEqual` b
  CWInteger a       == CWInteger b       = a == b
  CWUninterpreted a == CWUninterpreted b = a == b
  CWFloat a         == CWFloat b         = a == b
  CWDouble a        == CWDouble b        = a == b
  _                 == _                 = False

instance Ord CWVal where
  CWAlgReal a       `compare` CWAlgReal b       = a `algRealStructuralCompare` b
  CWAlgReal _       `compare` CWInteger _       = LT
  CWAlgReal _       `compare` CWFloat _         = LT
  CWAlgReal _       `compare` CWDouble _        = LT
  CWAlgReal _       `compare` CWUninterpreted _ = LT

  CWInteger _       `compare` CWAlgReal _       = GT
  CWInteger a       `compare` CWInteger b       = a `compare` b
  CWInteger _       `compare` CWFloat _         = LT
  CWInteger _       `compare` CWDouble _        = LT
  CWInteger _       `compare` CWUninterpreted _ = LT

  CWFloat _         `compare` CWAlgReal _       = GT
  CWFloat _         `compare` CWInteger _       = GT
  CWFloat a         `compare` CWFloat b         = a `compare` b
  CWFloat _         `compare` CWDouble _        = LT
  CWFloat _         `compare` CWUninterpreted _ = LT

  CWDouble _        `compare` CWAlgReal _       = GT
  CWDouble _        `compare` CWInteger _       = GT
  CWDouble _        `compare` CWFloat _         = GT
  CWDouble a        `compare` CWDouble b        = a `compare` b
  CWDouble _        `compare` CWUninterpreted _ = LT

  CWUninterpreted _ `compare` CWAlgReal _       = GT
  CWUninterpreted _ `compare` CWInteger _       = GT
  CWUninterpreted _ `compare` CWFloat _         = GT
  CWUninterpreted _ `compare` CWDouble _        = GT
  CWUninterpreted a `compare` CWUninterpreted b = a `compare` b

-- | 'CW' represents a concrete word of a fixed size:
-- Endianness is mostly irrelevant (see the 'FromBits' class).
-- For signed words, the most significant digit is considered to be the sign.
data CW = CW { cwKind   :: !Kind
             , cwVal    :: !CWVal
             }
        deriving (Eq, Ord)

-- | Are two CW's of the same type?
cwSameType :: CW -> CW -> Bool
cwSameType x y = cwKind x == cwKind y

-- | Is this a bit?
cwIsBit :: CW -> Bool
cwIsBit x = case cwKind x of
              KBool -> True
              _     -> False

-- | Convert a CW to a Haskell boolean (NB. Assumes input is well-kinded)
cwToBool :: CW -> Bool
cwToBool x = cwVal x /= CWInteger 0

-- | Normalize a CW. Essentially performs modular arithmetic to make sure the
-- value can fit in the given bit-size. Note that this is rather tricky for
-- negative values, due to asymmetry. (i.e., an 8-bit negative number represents
-- values in the range -128 to 127; thus we have to be careful on the negative side.)
normCW :: CW -> CW
normCW c@(CW (KBounded signed sz) (CWInteger v)) = c { cwVal = CWInteger norm }
 where norm | sz == 0 = 0
            | signed  = let rg = 2 ^ (sz - 1)
                        in case divMod v rg of
                                  (a, b) | even a -> b
                                  (_, b)          -> b - rg
            | True    = v `mod` (2 ^ sz)
normCW c = c

-- | Kind of symbolic value
data Kind = KBool
          | KBounded Bool Int
          | KUnbounded
          | KReal
          | KUninterpreted String
          | KFloat
          | KDouble
          deriving (Eq, Ord)

instance Show Kind where
  show KBool              = "SBool"
  show (KBounded False n) = "SWord" ++ show n
  show (KBounded True n)  = "SInt"  ++ show n
  show KUnbounded         = "SInteger"
  show KReal              = "SReal"
  show (KUninterpreted s) = s
  show KFloat             = "SFloat"
  show KDouble            = "SDouble"

-- | A symbolic node id
newtype NodeId = NodeId Int deriving (Eq, Ord)

-- | A symbolic word, tracking it's signedness and size.
data SW = SW Kind NodeId deriving (Eq, Ord)

-- | Forcing an argument; this is a necessary evil to make sure all the arguments
-- to an uninterpreted function and sBranch test conditions are evaluated before called;
-- the semantics of uinterpreted functions is necessarily strict; deviating from Haskell's
forceSWArg :: SW -> IO ()
forceSWArg (SW k n) = k `seq`  n `seq` return ()

-- | Quantifiers: forall or exists. Note that we allow
-- arbitrary nestings.
data Quantifier = ALL | EX deriving Eq

-- | Are there any existential quantifiers?
needsExistentials :: [Quantifier] -> Bool
needsExistentials = (EX `elem`)

-- | Constant False as a SW. Note that this value always occupies slot -2.
falseSW :: SW
falseSW = SW KBool $ NodeId (-2)

-- | Constant False as a SW. Note that this value always occupies slot -1.
trueSW :: SW
trueSW  = SW KBool $ NodeId (-1)

-- | Constant False as a CW. We represent it using the integer value 0.
falseCW :: CW
falseCW = CW KBool (CWInteger 0)

-- | Constant True as a CW. We represent it using the integer value 1.
trueCW :: CW
trueCW  = CW KBool (CWInteger 1)

-- | A simple type for SBV computations, used mainly for uninterpreted constants.
-- We keep track of the signedness/size of the arguments. A non-function will
-- have just one entry in the list.
newtype SBVType = SBVType [Kind]
             deriving (Eq, Ord)

-- | how many arguments does the type take?
typeArity :: SBVType -> Int
typeArity (SBVType xs) = length xs - 1

instance Show SBVType where
  show (SBVType []) = error "SBV: internal error, empty SBVType"
  show (SBVType xs) = intercalate " -> " $ map show xs

-- | Symbolic operations
data Op = Plus | Times | Minus
        | Quot | Rem
        | Equal | NotEqual
        | LessThan | GreaterThan | LessEq | GreaterEq
        | Ite
        | And | Or  | XOr | Not
        | Shl Int | Shr Int | Rol Int | Ror Int
        | Extract Int Int -- Extract i j: extract bits i to j. Least significant bit is 0 (big-endian)
        | Join  -- Concat two words to form a bigger one, in the order given
        | LkUp (Int, Kind, Kind, Int) !SW !SW   -- (table-index, arg-type, res-type, length of the table) index out-of-bounds-value
        | ArrEq   Int Int
        | ArrRead Int
        | Uninterpreted String
        deriving (Eq, Ord)

-- | SMT-Lib's square-root over floats/doubles. We piggy back on to the uninterpreted function mechanism
-- to implement these; which is not a terrible idea; although the use of the constructor 'Uninterpreted'
-- might be confusing. This function will *not* be uninterpreted in reality, as QF_FPA will define it. It's
-- a bit of a shame, but much easier to implement it this way.
smtLibSquareRoot :: Op
smtLibSquareRoot = Uninterpreted "squareRoot"

-- | SMT-Lib's fusedMA over floats/doubles. Similar to the 'smtLibSquareRoot'. Note that we cannot implement
-- this function in Haskell as precision loss would be inevitable. Maybe Haskell will eventually add this op
-- to the Num class.
smtLibFusedMA :: Op
smtLibFusedMA = Uninterpreted "fusedMA"

-- | A symbolic expression
data SBVExpr = SBVApp !Op ![SW]
             deriving (Eq, Ord)

-- | A class for capturing values that have a sign and a size (finite or infinite)
-- minimal complete definition: kindOf. This class can be automatically derived
-- for data-types that have a 'Data' instance; this is useful for creating uninterpreted
-- sorts.
class HasKind a where
  kindOf          :: a -> Kind
  hasSign         :: a -> Bool
  intSizeOf       :: a -> Int
  isBoolean       :: a -> Bool
  isBounded       :: a -> Bool
  isReal          :: a -> Bool
  isFloat         :: a -> Bool
  isDouble        :: a -> Bool
  isInteger       :: a -> Bool
  isUninterpreted :: a -> Bool
  showType        :: a -> String
  -- defaults
  hasSign x = case kindOf x of
                  KBool            -> False
                  KBounded b _     -> b
                  KUnbounded       -> True
                  KReal            -> True
                  KFloat           -> True
                  KDouble          -> True
                  KUninterpreted{} -> False
  intSizeOf x = case kindOf x of
                  KBool            -> error "SBV.HasKind.intSizeOf((S)Bool)"
                  KBounded _ s     -> s
                  KUnbounded       -> error "SBV.HasKind.intSizeOf((S)Integer)"
                  KReal            -> error "SBV.HasKind.intSizeOf((S)Real)"
                  KFloat           -> error "SBV.HasKind.intSizeOf((S)Float)"
                  KDouble          -> error "SBV.HasKind.intSizeOf((S)Double)"
                  KUninterpreted s -> error $ "SBV.HasKind.intSizeOf: Uninterpreted sort: " ++ s
  isBoolean       x | KBool{}          <- kindOf x = True
                    | True                         = False
  isBounded       x | KBounded{}       <- kindOf x = True
                    | True                         = False
  isReal          x | KReal{}          <- kindOf x = True
                    | True                         = False
  isFloat         x | KFloat{}         <- kindOf x = True
                    | True                         = False
  isDouble        x | KDouble{}        <- kindOf x = True
                    | True                         = False
  isInteger      x  | KUnbounded{}     <- kindOf x = True
                    | True                         = False
  isUninterpreted x | KUninterpreted{} <- kindOf x = True
                    | True                         = False
  showType = show . kindOf

  -- default signature for uninterpreted kinds
  default kindOf :: Data a => a -> Kind
  kindOf = KUninterpreted . tyconUQname . dataTypeName . dataTypeOf

instance HasKind Bool    where kindOf _ = KBool
instance HasKind Int8    where kindOf _ = KBounded True  8
instance HasKind Word8   where kindOf _ = KBounded False 8
instance HasKind Int16   where kindOf _ = KBounded True  16
instance HasKind Word16  where kindOf _ = KBounded False 16
instance HasKind Int32   where kindOf _ = KBounded True  32
instance HasKind Word32  where kindOf _ = KBounded False 32
instance HasKind Int64   where kindOf _ = KBounded True  64
instance HasKind Word64  where kindOf _ = KBounded False 64
instance HasKind Integer where kindOf _ = KUnbounded
instance HasKind AlgReal where kindOf _ = KReal
instance HasKind Float   where kindOf _ = KFloat
instance HasKind Double  where kindOf _ = KDouble

-- | Lift a unary function thruough a CW
liftCW :: (AlgReal -> b) -> (Integer -> b) -> (Float -> b) -> (Double -> b) -> (String -> b) -> CW -> b
liftCW f _ _ _ _ (CW _ (CWAlgReal v))       = f v
liftCW _ f _ _ _ (CW _ (CWInteger v))       = f v
liftCW _ _ f _ _ (CW _ (CWFloat v))         = f v
liftCW _ _ _ f _ (CW _ (CWDouble v))        = f v
liftCW _ _ _ _ f (CW _ (CWUninterpreted v)) = f v

-- | Lift a binary function through a CW
liftCW2 :: (AlgReal -> AlgReal -> b) -> (Integer -> Integer -> b) -> (Float -> Float -> b) -> (Double -> Double -> b) -> (String -> String -> b) -> CW -> CW -> b
liftCW2 r i f d u x y = case (cwVal x, cwVal y) of
                         (CWAlgReal a,       CWAlgReal b)       -> r a b
                         (CWInteger a,       CWInteger b)       -> i a b
                         (CWFloat a,         CWFloat b)         -> f a b
                         (CWDouble a,        CWDouble b)        -> d a b
                         (CWUninterpreted a, CWUninterpreted b) -> u a b
                         _                                      -> error $ "SBV.liftCW2: impossible, incompatible args received: " ++ show (x, y)

-- | Map a unary function through a CW
mapCW :: (AlgReal -> AlgReal) -> (Integer -> Integer) -> (Float -> Float) -> (Double -> Double) -> (String -> String) -> CW -> CW
mapCW r i f d u x  = normCW $ CW (cwKind x) $ case cwVal x of
                                               CWAlgReal a       -> CWAlgReal       (r a)
                                               CWInteger a       -> CWInteger       (i a)
                                               CWFloat a         -> CWFloat         (f a)
                                               CWDouble a        -> CWDouble        (d a)
                                               CWUninterpreted a -> CWUninterpreted (u a)

-- | Map a binary function through a CW
mapCW2 :: (AlgReal -> AlgReal -> AlgReal) -> (Integer -> Integer -> Integer) -> (Float -> Float -> Float) -> (Double -> Double -> Double) -> (String -> String -> String) -> CW -> CW -> CW
mapCW2 r i f d u x y = case (cwSameType x y, cwVal x, cwVal y) of
                        (True, CWAlgReal a,       CWAlgReal b)       -> normCW $ CW (cwKind x) (CWAlgReal       (r a b))
                        (True, CWInteger a,       CWInteger b)       -> normCW $ CW (cwKind x) (CWInteger       (i a b))
                        (True, CWFloat a,         CWFloat b)         -> normCW $ CW (cwKind x) (CWFloat         (f a b))
                        (True, CWDouble a,        CWDouble b)        -> normCW $ CW (cwKind x) (CWDouble        (d a b))
                        (True, CWUninterpreted a, CWUninterpreted b) -> normCW $ CW (cwKind x) (CWUninterpreted (u a b))
                        _                                            -> error $ "SBV.mapCW2: impossible, incompatible args received: " ++ show (x, y)

instance HasKind CW where
  kindOf = cwKind

instance HasKind SW where
  kindOf (SW k _) = k

instance Show CW where
  show w | cwIsBit w = show (cwToBool w)
  show w             = liftCW show show show show id w ++ " :: " ++ showType w

instance Show SW where
  show (SW _ (NodeId n))
    | n < 0 = "s_" ++ show (abs n)
    | True  = 's' : show n

instance Show Op where
  show (Shl i) = "<<"  ++ show i
  show (Shr i) = ">>"  ++ show i
  show (Rol i) = "<<<" ++ show i
  show (Ror i) = ">>>" ++ show i
  show (Extract i j) = "choose [" ++ show i ++ ":" ++ show j ++ "]"
  show (LkUp (ti, at, rt, l) i e)
        = "lookup(" ++ tinfo ++ ", " ++ show i ++ ", " ++ show e ++ ")"
        where tinfo = "table" ++ show ti ++ "(" ++ show at ++ " -> " ++ show rt ++ ", " ++ show l ++ ")"
  show (ArrEq i j)   = "array_" ++ show i ++ " == array_" ++ show j
  show (ArrRead i)   = "select array_" ++ show i
  show (Uninterpreted i) = "[uninterpreted] " ++ i
  show op
    | Just s <- op `lookup` syms = s
    | True                       = error "impossible happened; can't find op!"
    where syms = [ (Plus, "+"), (Times, "*"), (Minus, "-")
                 , (Quot, "quot")
                 , (Rem,  "rem")
                 , (Equal, "=="), (NotEqual, "/=")
                 , (LessThan, "<"), (GreaterThan, ">"), (LessEq, "<"), (GreaterEq, ">")
                 , (Ite, "if_then_else")
                 , (And, "&"), (Or, "|"), (XOr, "^"), (Not, "~")
                 , (Join, "#")
                 ]

-- | To improve hash-consing, take advantage of commutative operators by
-- reordering their arguments.
reorder :: SBVExpr -> SBVExpr
reorder s = case s of
              SBVApp op [a, b] | isCommutative op && a > b -> SBVApp op [b, a]
              _ -> s
  where isCommutative :: Op -> Bool
        isCommutative o = o `elem` [Plus, Times, Equal, NotEqual, And, Or, XOr]

instance Show SBVExpr where
  show (SBVApp Ite [t, a, b]) = unwords ["if", show t, "then", show a, "else", show b]
  show (SBVApp (Shl i) [a])   = unwords [show a, "<<", show i]
  show (SBVApp (Shr i) [a])   = unwords [show a, ">>", show i]
  show (SBVApp (Rol i) [a])   = unwords [show a, "<<<", show i]
  show (SBVApp (Ror i) [a])   = unwords [show a, ">>>", show i]
  show (SBVApp op  [a, b])    = unwords [show a, show op, show b]
  show (SBVApp op  args)      = unwords (show op : map show args)

-- | A program is a sequence of assignments
newtype SBVPgm = SBVPgm {pgmAssignments :: (S.Seq (SW, SBVExpr))}

-- | 'NamedSymVar' pairs symbolic words and user given/automatically generated names
type NamedSymVar = (SW, String)

-- | 'UnintKind' pairs array names and uninterpreted constants with their "kinds"
-- used mainly for printing counterexamples
data UnintKind = UFun Int String | UArr Int String      -- in each case, arity and the aliasing name
 deriving Show

-- | Result of running a symbolic computation
data Result = Result (Set.Set Kind)                -- kinds used in the program
                     [(String, CW)]                -- quick-check counter-example information (if any)
                     [(String, [String])]          -- uninterpeted code segments
                     [(Quantifier, NamedSymVar)]   -- inputs (possibly existential)
                     [(SW, CW)]                    -- constants
                     [((Int, Kind, Kind), [SW])]   -- tables (automatically constructed) (tableno, index-type, result-type) elts
                     [(Int, ArrayInfo)]            -- arrays (user specified)
                     [(String, SBVType)]           -- uninterpreted constants
                     [(String, [String])]          -- axioms
                     SBVPgm                        -- assignments
                     [SW]                          -- additional constraints (boolean)
                     [SW]                          -- outputs

-- | Extract the constraints from a result
getConstraints :: Result -> [SW]
getConstraints (Result _ _ _ _ _ _ _ _ _ _ cstrs _) = cstrs

-- | Extract the traced-values from a result (quick-check)
getTraceInfo :: Result -> [(String, CW)]
getTraceInfo (Result _ tvals _ _ _ _ _ _ _ _ _ _) = tvals

instance Show Result where
  show (Result _ _ _ _ cs _ _ [] [] _ [] [r])
    | Just c <- r `lookup` cs
    = show c
  show (Result kinds _ cgs is cs ts as uis axs xs cstrs os)  = intercalate "\n" $
                   (if null usorts then [] else "SORTS" : map ("  " ++) usorts)
                ++ ["INPUTS"]
                ++ map shn is
                ++ ["CONSTANTS"]
                ++ map shc cs
                ++ ["TABLES"]
                ++ map sht ts
                ++ ["ARRAYS"]
                ++ map sha as
                ++ ["UNINTERPRETED CONSTANTS"]
                ++ map shui uis
                ++ ["USER GIVEN CODE SEGMENTS"]
                ++ concatMap shcg cgs
                ++ ["AXIOMS"]
                ++ map shax axs
                ++ ["DEFINE"]
                ++ map (\(s, e) -> "  " ++ shs s ++ " = " ++ show e) (F.toList (pgmAssignments xs))
                ++ ["CONSTRAINTS"]
                ++ map (("  " ++) . show) cstrs
                ++ ["OUTPUTS"]
                ++ map (("  " ++) . show) os
    where usorts = [s | KUninterpreted s <- Set.toList kinds]
          shs sw = show sw ++ " :: " ++ showType sw
          sht ((i, at, rt), es)  = "  Table " ++ show i ++ " : " ++ show at ++ "->" ++ show rt ++ " = " ++ show es
          shc (sw, cw) = "  " ++ show sw ++ " = " ++ show cw
          shcg (s, ss) = ("Variable: " ++ s) : map ("  " ++) ss
          shn (q, (sw, nm)) = "  " ++ ni ++ " :: " ++ showType sw ++ ex ++ alias
            where ni = show sw
                  ex | q == ALL = ""
                     | True     = ", existential"
                  alias | ni == nm = ""
                        | True     = ", aliasing " ++ show nm
          sha (i, (nm, (ai, bi), ctx)) = "  " ++ ni ++ " :: " ++ show ai ++ " -> " ++ show bi ++ alias
                                       ++ "\n     Context: "     ++ show ctx
            where ni = "array_" ++ show i
                  alias | ni == nm = ""
                        | True     = ", aliasing " ++ show nm
          shui (nm, t) = "  [uninterpreted] " ++ nm ++ " :: " ++ show t
          shax (nm, ss) = "  -- user defined axiom: " ++ nm ++ "\n  " ++ intercalate "\n  " ss

-- | The context of a symbolic array as created
data ArrayContext = ArrayFree (Maybe SW)     -- ^ A new array, with potential initializer for each cell
                  | ArrayReset Int SW        -- ^ An array created from another array by fixing each element to another value
                  | ArrayMutate Int SW SW    -- ^ An array created by mutating another array at a given cell
                  | ArrayMerge  SW Int Int   -- ^ An array created by symbolically merging two other arrays

instance Show ArrayContext where
  show (ArrayFree Nothing)  = " initialized with random elements"
  show (ArrayFree (Just s)) = " initialized with " ++ show s ++ " :: " ++ showType s
  show (ArrayReset i s)     = " reset array_" ++ show i ++ " with " ++ show s ++ " :: " ++ showType s
  show (ArrayMutate i a b)  = " cloned from array_" ++ show i ++ " with " ++ show a ++ " :: " ++ showType a ++ " |-> " ++ show b ++ " :: " ++ showType b
  show (ArrayMerge s i j)   = " merged arrays " ++ show i ++ " and " ++ show j ++ " on condition " ++ show s

-- | Expression map, used for hash-consing
type ExprMap   = Map.Map SBVExpr SW

-- | Constants are stored in a map, for hash-consing
type CnstMap   = Map.Map CW SW

-- | Kinds used in the program; used for determining the final SMT-Lib logic to pick
type KindSet = Set.Set Kind

-- | Tables generated during a symbolic run
type TableMap  = Map.Map [SW] (Int, Kind, Kind)

-- | Representation for symbolic arrays
type ArrayInfo = (String, (Kind, Kind), ArrayContext)

-- | Arrays generated during a symbolic run
type ArrayMap  = IMap.IntMap ArrayInfo

-- | Uninterpreted-constants generated during a symbolic run
type UIMap     = Map.Map String SBVType

-- | Code-segments for Uninterpreted-constants, as given by the user
type CgMap     = Map.Map String [String]

-- | Cached values, implementing sharing
type Cache a   = IMap.IntMap [(StableName (State -> IO a), a)]

-- | Convert an SBV-type to the kind-of uninterpreted value it represents
unintFnUIKind :: (String, SBVType) -> (String, UnintKind)
unintFnUIKind (s, t) = (s, UFun (typeArity t) s)

-- | Convert an array value type to the kind-of uninterpreted value it represents
arrayUIKind :: (Int, ArrayInfo) -> Maybe (String, UnintKind)
arrayUIKind (i, (nm, _, ctx)) 
  | external ctx = Just ("array_" ++ show i, UArr 1 nm) -- arrays are always 1-dimensional in the SMT-land. (Unless encoded explicitly)
  | True         = Nothing
  where external (ArrayFree{})   = True
        external (ArrayReset{})  = False
        external (ArrayMutate{}) = False
        external (ArrayMerge{})  = False

-- | Different means of running a symbolic piece of code
data SBVRunMode = Proof (Bool, Maybe SMTConfig) -- ^ Symbolic simulation mode, for proof purposes. Bool is True if it's a sat instance. SMTConfig is used for 'sBranch' calls.
                | CodeGen                       -- ^ Code generation mode
                | Concrete StdGen               -- ^ Concrete simulation mode. The StdGen is for the pConstrain acceptance in cross runs

-- | Is this a concrete run? (i.e., quick-check or test-generation like)
isConcreteMode :: SBVRunMode -> Bool
isConcreteMode (Concrete _) = True
isConcreteMode (Proof{})    = False
isConcreteMode CodeGen      = False

-- | The state of the symbolic interpreter
data State  = State { runMode       :: SBVRunMode
                    , pathCond      :: SBool
                    , rStdGen       :: IORef StdGen
                    , rCInfo        :: IORef [(String, CW)]
                    , rctr          :: IORef Int
                    , rUsedKinds    :: IORef KindSet
                    , rinps         :: IORef [(Quantifier, NamedSymVar)]
                    , rConstraints  :: IORef [SW]
                    , routs         :: IORef [SW]
                    , rtblMap       :: IORef TableMap
                    , spgm          :: IORef SBVPgm
                    , rconstMap     :: IORef CnstMap
                    , rexprMap      :: IORef ExprMap
                    , rArrayMap     :: IORef ArrayMap
                    , rUIMap        :: IORef UIMap
                    , rCgMap        :: IORef CgMap
                    , raxioms       :: IORef [(String, [String])]
                    , rSWCache      :: IORef (Cache SW)
                    , rAICache      :: IORef (Cache Int)
                    }

-- | Get the current path condition
getPathCondition :: State -> SBool
getPathCondition = pathCond

-- | Extend the path condition with the given test value.
extendPathCondition :: State -> (SBool -> SBool) -> State
extendPathCondition st f = st{pathCond = f (pathCond st)}

-- | Are we running in proof mode?
inProofMode :: State -> Bool
inProofMode s = case runMode s of
                  Proof{}    -> True
                  CodeGen    -> False
                  Concrete{} -> False

-- | If in proof mode, get the underlying configuration (used for 'sBranch')
getSBranchRunConfig :: State -> Maybe SMTConfig
getSBranchRunConfig st = case runMode st of
                           Proof (_, s)  -> s
                           _             -> Nothing

-- | The "Symbolic" value. Either a constant (@Left@) or a symbolic
-- value (@Right Cached@). Note that caching is essential for making
-- sure sharing is preserved. The parameter 'a' is phantom, but is
-- extremely important in keeping the user interface strongly typed.
data SBV a = SBV !Kind !(Either CW (Cached SW))

-- | A symbolic boolean/bit
type SBool   = SBV Bool

-- | 8-bit unsigned symbolic value
type SWord8  = SBV Word8

-- | 16-bit unsigned symbolic value
type SWord16 = SBV Word16

-- | 32-bit unsigned symbolic value
type SWord32 = SBV Word32

-- | 64-bit unsigned symbolic value
type SWord64 = SBV Word64

-- | 8-bit signed symbolic value, 2's complement representation
type SInt8   = SBV Int8

-- | 16-bit signed symbolic value, 2's complement representation
type SInt16  = SBV Int16

-- | 32-bit signed symbolic value, 2's complement representation
type SInt32  = SBV Int32

-- | 64-bit signed symbolic value, 2's complement representation
type SInt64  = SBV Int64

-- | Infinite precision signed symbolic value
type SInteger = SBV Integer

-- | Infinite precision symbolic algebraic real value
type SReal = SBV AlgReal

-- | IEEE-754 single-precision floating point numbers
type SFloat = SBV Float

-- | IEEE-754 double-precision floating point numbers
type SDouble = SBV Double

-- | Not-A-Number for 'Double' and 'Float'. Surprisingly, Haskell
-- Prelude doesn't have this value defined, so we provide it here.
nan :: Floating a => a
nan = 0/0

-- | Infinity for 'Double' and 'Float'. Surprisingly, Haskell
-- Prelude doesn't have this value defined, so we provide it here.
infinity :: Floating a => a
infinity = 1/0

-- | Symbolic variant of Not-A-Number. This value will inhabit both
-- 'SDouble' and 'SFloat'.
sNaN :: (Floating a, SymWord a) => SBV a
sNaN = literal nan

-- | Symbolic variant of infinity. This value will inhabit both
-- 'SDouble' and 'SFloat'.
sInfinity :: (Floating a, SymWord a) => SBV a
sInfinity = literal infinity

-- | Rounding mode to be used for the IEEE floating-point operations.
-- Note that Haskell's default is 'RoundNearestTiesToEven'. If you use
-- a different rounding mode, then the counter-examples you get may not
-- match what you observe in Haskell.
data RoundingMode = RoundNearestTiesToEven  -- ^ Round to nearest representable floating point value.
                                            -- If precisely at half-way, pick the even number.
                                            -- (In this context, /even/ means the lowest-order bit is zero.)
                  | RoundNearestTiesToAway  -- ^ Round to nearest representable floating point value.
                                            -- If precisely at half-way, pick the number further away from 0.
                                            -- (That is, for positive values, pick the greater; for negative values, pick the smaller.)
                  | RoundTowardPositive     -- ^ Round towards positive infinity. (Also known as rounding-up or ceiling.)
                  | RoundTowardNegative     -- ^ Round towards negative infinity. (Also known as rounding-down or floor.)
                  | RoundTowardZero         -- ^ Round towards zero. (Also known as truncation.)

-- Not particularly "desirable", but will do if needed
instance Show (SBV a) where
  show (SBV _ (Left c))  = show c
  show (SBV k (Right _)) = "<symbolic> :: " ++ show k

-- Equality constraint on SBV values. Not desirable since we can't really compare two
-- symbolic values, but will do.
instance Eq (SBV a) where
  SBV _ (Left a) == SBV _ (Left b) = a == b
  a == b = error $ "Comparing symbolic bit-vectors; Use (.==) instead. Received: " ++ show (a, b)
  SBV _ (Left a) /= SBV _ (Left b) = a /= b
  a /= b = error $ "Comparing symbolic bit-vectors; Use (./=) instead. Received: " ++ show (a, b)

instance HasKind a => HasKind (SBV a) where
  kindOf (SBV k _) = k

-- | Increment the variable counter
incCtr :: State -> IO Int
incCtr s = do ctr <- readIORef (rctr s)
              let i = ctr + 1
              i `seq` writeIORef (rctr s) i
              return ctr

-- | Generate a random value, for quick-check and test-gen purposes
throwDice :: State -> IO Double
throwDice st = do g <- readIORef (rStdGen st)
                  let (r, g') = randomR (0, 1) g
                  writeIORef (rStdGen st) g'
                  return r

-- | Create a new uninterpreted symbol, possibly with user given code
newUninterpreted :: State -> String -> SBVType -> Maybe [String] -> IO ()
newUninterpreted st nm t mbCode
  | null nm || not (isAlpha (head nm)) || not (all validChar (tail nm))
  = error $ "Bad uninterpreted constant name: " ++ show nm ++ ". Must be a valid identifier."
  | True = do
        uiMap <- readIORef (rUIMap st)
        case nm `Map.lookup` uiMap of
          Just t' -> if t /= t'
                     then error $  "Uninterpreted constant " ++ show nm ++ " used at incompatible types\n"
                                ++ "      Current type      : " ++ show t ++ "\n"
                                ++ "      Previously used at: " ++ show t'
                     else return ()
          Nothing -> do modifyIORef (rUIMap st) (Map.insert nm t)
                        when (isJust mbCode) $ modifyIORef (rCgMap st) (Map.insert nm (fromJust mbCode))
  where validChar x = isAlphaNum x || x `elem` "_"

-- | Create a new SW
newSW :: State -> Kind -> IO (SW, String)
newSW st k = do ctr <- incCtr st
                let sw = SW k (NodeId ctr)
                registerKind st k
                return (sw, 's' : show ctr)
{-# INLINE newSW #-}

registerKind :: State -> Kind -> IO ()
registerKind st k
  | KUninterpreted sortName <- k, sortName `elem` reserved
  = error $ "SBV: " ++ show sortName ++ " is a reserved sort; please use a different name."
  | True
  = modifyIORef (rUsedKinds st) (Set.insert k)
 where reserved = ["Int", "Real", "List", "Array", "Bool", "NUMERAL", "DECIMAL", "STRING", "FP"]  -- Reserved by SMT-Lib

-- | Create a new constant; hash-cons as necessary
newConst :: State -> CW -> IO SW
newConst st c = do
  constMap <- readIORef (rconstMap st)
  case c `Map.lookup` constMap of
    Just sw -> return sw
    Nothing -> do let k = kindOf c
                  (sw, _) <- newSW st k
                  modifyIORef (rconstMap st) (Map.insert c sw)
                  return sw
{-# INLINE newConst #-}

-- | Create a new table; hash-cons as necessary
getTableIndex :: State -> Kind -> Kind -> [SW] -> IO Int
getTableIndex st at rt elts = do
  tblMap <- readIORef (rtblMap st)
  case elts `Map.lookup` tblMap of
    Just (i, _, _)  -> return i
    Nothing         -> do let i = Map.size tblMap
                          modifyIORef (rtblMap st) (Map.insert elts (i, at, rt))
                          return i

-- | Create a constant word from an integral
mkConstCW :: Integral a => Kind -> a -> CW
mkConstCW KBool              a = normCW $ CW KBool      (CWInteger (toInteger a))
mkConstCW k@(KBounded{})     a = normCW $ CW k          (CWInteger (toInteger a))
mkConstCW KUnbounded         a = normCW $ CW KUnbounded (CWInteger (toInteger a))
mkConstCW KReal              a = normCW $ CW KReal      (CWAlgReal (fromInteger (toInteger a)))
mkConstCW KFloat             a = normCW $ CW KFloat     (CWFloat   (fromInteger (toInteger a)))
mkConstCW KDouble            a = normCW $ CW KDouble    (CWDouble  (fromInteger (toInteger a)))
mkConstCW (KUninterpreted s) a = error $ "Unexpected call to mkConstCW with uninterpreted kind: " ++ s ++ " with value: " ++ show (toInteger a)

-- | Create a new expression; hash-cons as necessary
newExpr :: State -> Kind -> SBVExpr -> IO SW
newExpr st k app = do
   let e = reorder app
   exprMap <- readIORef (rexprMap st)
   case e `Map.lookup` exprMap of
     Just sw -> return sw
     Nothing -> do (sw, _) <- newSW st k
                   modifyIORef (spgm st)     (\(SBVPgm xs) -> SBVPgm (xs S.|> (sw, e)))
                   modifyIORef (rexprMap st) (Map.insert e sw)
                   return sw
{-# INLINE newExpr #-}

-- | Convert a symbolic value to a symbolic-word
sbvToSW :: State -> SBV a -> IO SW
sbvToSW st (SBV _ (Left c))  = newConst st c
sbvToSW st (SBV _ (Right f)) = uncache f st

-------------------------------------------------------------------------
-- * Symbolic Computations
-------------------------------------------------------------------------
-- | A Symbolic computation. Represented by a reader monad carrying the
-- state of the computation, layered on top of IO for creating unique
-- references to hold onto intermediate results.
newtype Symbolic a = Symbolic (ReaderT State IO a)
                   deriving (Applicative, Functor, Monad, MonadIO, MonadReader State)

-- | Create a symbolic value, based on the quantifier we have. If an explicit quantifier is given, we just use that.
-- If not, then we pick existential for SAT calls and universal for everything else.
mkSymSBV :: forall a. (Random a, SymWord a) => Maybe Quantifier -> Kind -> Maybe String -> Symbolic (SBV a)
mkSymSBV = mkSymSBVWithRandom randomIO

mkSymSBVWithRandom :: forall a. SymWord a => IO (SBV a) -> Maybe Quantifier -> Kind -> Maybe String -> Symbolic (SBV a)
mkSymSBVWithRandom rand mbQ k mbNm = do
        st <- ask
        let q = case (mbQ, runMode st) of
                  (Just x,  _)                -> x   -- user given, just take it
                  (Nothing, Concrete{})       -> ALL -- concrete simulation, pick universal
                  (Nothing, Proof (True, _))  -> EX  -- sat mode, pick existential
                  (Nothing, Proof (False, _)) -> ALL -- proof mode, pick universal
                  (Nothing, CodeGen)          -> ALL -- code generation, pick universal
        case runMode st of
          Concrete _ | q == EX -> case mbNm of
                                    Nothing -> error $ "Cannot quick-check in the presence of existential variables, type: " ++ showType (undefined :: SBV a)
                                    Just nm -> error $ "Cannot quick-check in the presence of existential variable " ++ nm ++ " :: " ++ showType (undefined :: SBV a)
          Concrete _           -> do v@(SBV _ (Left cw)) <- liftIO rand
                                     liftIO $ modifyIORef (rCInfo st) ((maybe "_" id mbNm, cw):)
                                     return v
          _          -> do (sw, internalName) <- liftIO $ newSW st k
                           let nm = maybe internalName id mbNm
                           liftIO $ modifyIORef (rinps st) ((q, (sw, nm)):)
                           return $ SBV k $ Right $ cache (const (return sw))

-- | Convert a symbolic value to an SW, inside the Symbolic monad
sbvToSymSW :: SBV a -> Symbolic SW
sbvToSymSW sbv = do
        st <- ask
        liftIO $ sbvToSW st sbv

-- | A class representing what can be returned from a symbolic computation.
class Outputtable a where
  -- | Mark an interim result as an output. Useful when constructing Symbolic programs
  -- that return multiple values, or when the result is programmatically computed.
  output :: a -> Symbolic a

instance Outputtable (SBV a) where
  output i@(SBV _ (Left c)) = do
          st <- ask
          sw <- liftIO $ newConst st c
          liftIO $ modifyIORef (routs st) (sw:)
          return i
  output i@(SBV _ (Right f)) = do
          st <- ask
          sw <- liftIO $ uncache f st
          liftIO $ modifyIORef (routs st) (sw:)
          return i

instance Outputtable a => Outputtable [a] where
  output = mapM output

instance Outputtable () where
  output = return

instance (Outputtable a, Outputtable b) => Outputtable (a, b) where
  output = mlift2 (,) output output

instance (Outputtable a, Outputtable b, Outputtable c) => Outputtable (a, b, c) where
  output = mlift3 (,,) output output output

instance (Outputtable a, Outputtable b, Outputtable c, Outputtable d) => Outputtable (a, b, c, d) where
  output = mlift4 (,,,) output output output output

instance (Outputtable a, Outputtable b, Outputtable c, Outputtable d, Outputtable e) => Outputtable (a, b, c, d, e) where
  output = mlift5 (,,,,) output output output output output

instance (Outputtable a, Outputtable b, Outputtable c, Outputtable d, Outputtable e, Outputtable f) => Outputtable (a, b, c, d, e, f) where
  output = mlift6 (,,,,,) output output output output output output

instance (Outputtable a, Outputtable b, Outputtable c, Outputtable d, Outputtable e, Outputtable f, Outputtable g) => Outputtable (a, b, c, d, e, f, g) where
  output = mlift7 (,,,,,,) output output output output output output output

instance (Outputtable a, Outputtable b, Outputtable c, Outputtable d, Outputtable e, Outputtable f, Outputtable g, Outputtable h) => Outputtable (a, b, c, d, e, f, g, h) where
  output = mlift8 (,,,,,,,) output output output output output output output output

-- | Add a user specified axiom to the generated SMT-Lib file. The first argument is a mere
-- string, use for commenting purposes. The second argument is intended to hold the multiple-lines
-- of the axiom text as expressed in SMT-Lib notation. Note that we perform no checks on the axiom
-- itself, to see whether it's actually well-formed or is sensical by any means.
-- A separate formalization of SMT-Lib would be very useful here.
addAxiom :: String -> [String] -> Symbolic ()
addAxiom nm ax = do
        st <- ask
        liftIO $ modifyIORef (raxioms st) ((nm, ax) :)

-- | Run a symbolic computation in Proof mode and return a 'Result'. The boolean
-- argument indicates if this is a sat instance or not.
runSymbolic :: (Bool, Maybe SMTConfig) -> Symbolic a -> IO Result
runSymbolic b c = snd `fmap` runSymbolic' (Proof b) c

-- | Run a symbolic computation, and return a extra value paired up with the 'Result'
runSymbolic' :: SBVRunMode -> Symbolic a -> IO (a, Result)
runSymbolic' currentRunMode (Symbolic c) = do
   ctr       <- newIORef (-2) -- start from -2; False and True will always occupy the first two elements
   cInfo     <- newIORef []
   pgm       <- newIORef (SBVPgm S.empty)
   emap      <- newIORef Map.empty
   cmap      <- newIORef Map.empty
   inps      <- newIORef []
   outs      <- newIORef []
   tables    <- newIORef Map.empty
   arrays    <- newIORef IMap.empty
   uis       <- newIORef Map.empty
   cgs       <- newIORef Map.empty
   axioms    <- newIORef []
   swCache   <- newIORef IMap.empty
   aiCache   <- newIORef IMap.empty
   usedKinds <- newIORef Set.empty
   cstrs     <- newIORef []
   rGen      <- case currentRunMode of
                  Concrete g -> newIORef g
                  _          -> newStdGen >>= newIORef
   let st = State { runMode      = currentRunMode
                  , pathCond     = SBV KBool (Left trueCW)
                  , rStdGen      = rGen
                  , rCInfo       = cInfo
                  , rctr         = ctr
                  , rUsedKinds   = usedKinds
                  , rinps        = inps
                  , routs        = outs
                  , rtblMap      = tables
                  , spgm         = pgm
                  , rconstMap    = cmap
                  , rArrayMap    = arrays
                  , rexprMap     = emap
                  , rUIMap       = uis
                  , rCgMap       = cgs
                  , raxioms      = axioms
                  , rSWCache     = swCache
                  , rAICache     = aiCache
                  , rConstraints = cstrs
                  }
   _ <- newConst st falseCW -- s(-2) == falseSW
   _ <- newConst st trueCW  -- s(-1) == trueSW
   r <- runReaderT c st
   res <- extractSymbolicSimulationState st
   return (r, res)

-- | Grab the program from a running symbolic simulation state. This is useful for internal purposes, for
-- instance when implementing 'sBranch'.
extractSymbolicSimulationState :: State -> IO Result
extractSymbolicSimulationState st@State{ spgm=pgm, rinps=inps, routs=outs, rtblMap=tables, rArrayMap=arrays, rUIMap=uis, raxioms=axioms
                                       , rUsedKinds=usedKinds, rCgMap=cgs, rCInfo=cInfo, rConstraints = cstrs} = do
   SBVPgm rpgm  <- readIORef pgm
   inpsO <- reverse `fmap` readIORef inps
   outsO <- reverse `fmap` readIORef outs
   let swap (a, b) = (b, a)
       cmp  (a, _) (b, _) = a `compare` b
   cnsts <- (sortBy cmp . map swap . Map.toList) `fmap` readIORef (rconstMap st)
   tbls  <- (sortBy (\((x, _, _), _) ((y, _, _), _) -> x `compare` y) . map swap . Map.toList) `fmap` readIORef tables
   arrs  <- IMap.toAscList `fmap` readIORef arrays
   unint <- Map.toList `fmap` readIORef uis
   axs   <- reverse `fmap` readIORef axioms
   knds  <- readIORef usedKinds
   cgMap <- Map.toList `fmap` readIORef cgs
   traceVals <- reverse `fmap` readIORef cInfo
   extraCstrs <- reverse `fmap` readIORef cstrs
   return $ Result knds traceVals cgMap inpsO cnsts tbls arrs unint axs (SBVPgm rpgm) extraCstrs outsO

-------------------------------------------------------------------------------
-- * Symbolic Words
-------------------------------------------------------------------------------
-- | A 'SymWord' is a potential symbolic bitvector that can be created instances of
-- to be fed to a symbolic program. Note that these methods are typically not needed
-- in casual uses with 'prove', 'sat', 'allSat' etc, as default instances automatically
-- provide the necessary bits.
class (HasKind a, Ord a) => SymWord a where
  -- | Create a user named input (universal)
  forall :: String -> Symbolic (SBV a)
  -- | Create an automatically named input
  forall_ :: Symbolic (SBV a)
  -- | Get a bunch of new words
  mkForallVars :: Int -> Symbolic [SBV a]
  -- | Create an existential variable
  exists  :: String -> Symbolic (SBV a)
  -- | Create an automatically named existential variable
  exists_ :: Symbolic (SBV a)
  -- | Create a bunch of existentials
  mkExistVars :: Int -> Symbolic [SBV a]
  -- | Create a free variable, universal in a proof, existential in sat
  free :: String -> Symbolic (SBV a)
  -- | Create an unnamed free variable, universal in proof, existential in sat
  free_ :: Symbolic (SBV a)
  -- | Create a bunch of free vars
  mkFreeVars :: Int -> Symbolic [SBV a]
  -- | Similar to free; Just a more convenient name
  symbolic  :: String -> Symbolic (SBV a)
  -- | Similar to mkFreeVars; but automatically gives names based on the strings
  symbolics :: [String] -> Symbolic [SBV a]
  -- | Turn a literal constant to symbolic
  literal :: a -> SBV a
  -- | Extract a literal, if the value is concrete
  unliteral :: SBV a -> Maybe a
  -- | Extract a literal, from a CW representation
  fromCW :: CW -> a
  -- | Is the symbolic word concrete?
  isConcrete :: SBV a -> Bool
  -- | Is the symbolic word really symbolic?
  isSymbolic :: SBV a -> Bool
  -- | Does it concretely satisfy the given predicate?
  isConcretely :: SBV a -> (a -> Bool) -> Bool
  -- | max/minbounds, if available. Note that we don't want
  -- to impose "Bounded" on our class as Integer is not Bounded but it is a SymWord
  mbMaxBound, mbMinBound :: Maybe a
  -- | One stop allocator
  mkSymWord :: Maybe Quantifier -> Maybe String -> Symbolic (SBV a)

  -- minimal complete definition, Nothing.
  -- Giving no instances is ok when defining an uninterpreted sort, but otherwise you really
  -- want to define: mbMaxBound, mbMinBound, literal, fromCW, mkSymWord
  forall   = mkSymWord (Just ALL) . Just
  forall_  = mkSymWord (Just ALL)   Nothing
  exists   = mkSymWord (Just EX)  . Just
  exists_  = mkSymWord (Just EX)    Nothing
  free     = mkSymWord Nothing    . Just
  free_    = mkSymWord Nothing      Nothing
  mkForallVars n = mapM (const forall_) [1 .. n]
  mkExistVars n  = mapM (const exists_) [1 .. n]
  mkFreeVars n   = mapM (const free_)   [1 .. n]
  symbolic       = free
  symbolics      = mapM symbolic
  unliteral (SBV _ (Left c))  = Just $ fromCW c
  unliteral _                 = Nothing
  isConcrete (SBV _ (Left _)) = True
  isConcrete _                = False
  isSymbolic = not . isConcrete
  isConcretely s p
    | Just i <- unliteral s = p i
    | True                  = False
  -- Followings, you really want to define them unless the instance is for an uninterpreted sort
  mbMaxBound = Nothing
  mbMinBound = Nothing
  literal x = error $ "Cannot create symbolic literals for kind: " ++ show (kindOf x)
  fromCW cw = error $ "Cannot convert CW " ++ show cw ++ " to kind " ++ show (kindOf (undefined :: a))

  default mkSymWord :: Data a => Maybe Quantifier -> Maybe String -> Symbolic (SBV a)
  mkSymWord mbQ mbNm = do
        let sortName = tyconUQname . dataTypeName . dataTypeOf $ (undefined :: a)
        st <- ask
        let k = KUninterpreted sortName
        liftIO $ registerKind st k
        let q = case (mbQ, runMode st) of
                  (Just x,  _)                -> x
                  (Nothing, Proof (True, _))  -> EX
                  (Nothing, Proof (False, _)) -> ALL
                  (Nothing, Concrete{})       -> error $ "SBV: Uninterpreted sort " ++ sortName ++ " can not be used in concrete simulation mode."
                  (Nothing, CodeGen)          -> error $ "SBV: Uninterpreted sort " ++ sortName ++ " can not be used in code-generation mode."
        ctr <- liftIO $ incCtr st
        let sw = SW k (NodeId ctr)
            nm = maybe ('s':show ctr) id mbNm
        liftIO $ modifyIORef (rinps st) ((q, (sw, nm)):)
        return $ SBV k $ Right $ cache (const (return sw))

instance (Random a, SymWord a) => Random (SBV a) where
  randomR (l, h) g = case (unliteral l, unliteral h) of
                       (Just lb, Just hb) -> let (v, g') = randomR (lb, hb) g in (literal (v :: a), g')
                       _                  -> error $ "SBV.Random: Cannot generate random values with symbolic bounds"
  random         g = let (v, g') = random g in (literal (v :: a) , g')
---------------------------------------------------------------------------------
-- * Symbolic Arrays
---------------------------------------------------------------------------------

-- | Flat arrays of symbolic values
-- An @array a b@ is an array indexed by the type @'SBV' a@, with elements of type @'SBV' b@
-- If an initial value is not provided in 'newArray_' and 'newArray' methods, then the elements
-- are left unspecified, i.e., the solver is free to choose any value. This is the right thing
-- to do if arrays are used as inputs to functions to be verified, typically. 
--
-- While it's certainly possible for user to create instances of 'SymArray', the
-- 'SArray' and 'SFunArray' instances already provided should cover most use cases
-- in practice. (There are some differences between these models, however, see the corresponding
-- declaration.)
--
--
-- Minimal complete definition: All methods are required, no defaults.
class SymArray array where
  -- | Create a new array, with an optional initial value
  newArray_      :: (HasKind a, HasKind b) => Maybe (SBV b) -> Symbolic (array a b)
  -- | Create a named new array, with an optional initial value
  newArray       :: (HasKind a, HasKind b) => String -> Maybe (SBV b) -> Symbolic (array a b)
  -- | Read the array element at @a@
  readArray      :: array a b -> SBV a -> SBV b
  -- | Reset all the elements of the array to the value @b@
  resetArray     :: SymWord b => array a b -> SBV b -> array a b
  -- | Update the element at @a@ to be @b@
  writeArray     :: SymWord b => array a b -> SBV a -> SBV b -> array a b
  -- | Merge two given arrays on the symbolic condition
  -- Intuitively: @mergeArrays cond a b = if cond then a else b@.
  -- Merging pushes the if-then-else choice down on to elements
  mergeArrays    :: SymWord b => SBV Bool -> array a b -> array a b -> array a b

-- | Arrays implemented in terms of SMT-arrays: <http://goedel.cs.uiowa.edu/smtlib/theories/ArraysEx.smt2>
--
--   * Maps directly to SMT-lib arrays
--
--   * Reading from an unintialized value is OK and yields an uninterpreted result
--
--   * Can check for equality of these arrays
--
--   * Cannot quick-check theorems using @SArray@ values
--
--   * Typically slower as it heavily relies on SMT-solving for the array theory
--
data SArray a b = SArray (Kind, Kind) (Cached ArrayIndex)

-- | An array index is simple an int value
type ArrayIndex = Int

instance (HasKind a, HasKind b) => Show (SArray a b) where
  show (SArray{}) = "SArray<" ++ showType (undefined :: a) ++ ":" ++ showType (undefined :: b) ++ ">"

instance SymArray SArray where
  newArray_  = declNewSArray (\t -> "array_" ++ show t)
  newArray n = declNewSArray (const n)
  readArray (SArray (_, bk) f) a = SBV bk $ Right $ cache r
     where r st = do arr <- uncacheAI f st
                     i   <- sbvToSW st a
                     newExpr st bk (SBVApp (ArrRead arr) [i])
  resetArray (SArray ainfo f) b = SArray ainfo $ cache g
     where g st = do amap <- readIORef (rArrayMap st)
                     val <- sbvToSW st b
                     i <- uncacheAI f st
                     let j = IMap.size amap
                     j `seq` modifyIORef (rArrayMap st) (IMap.insert j ("array_" ++ show j, ainfo, ArrayReset i val))
                     return j
  writeArray (SArray ainfo f) a b = SArray ainfo $ cache g
     where g st = do arr  <- uncacheAI f st
                     addr <- sbvToSW st a
                     val  <- sbvToSW st b
                     amap <- readIORef (rArrayMap st)
                     let j = IMap.size amap
                     j `seq` modifyIORef (rArrayMap st) (IMap.insert j ("array_" ++ show j, ainfo, ArrayMutate arr addr val))
                     return j
  mergeArrays t (SArray ainfo a) (SArray _ b) = SArray ainfo $ cache h
    where h st = do ai <- uncacheAI a st
                    bi <- uncacheAI b st
                    ts <- sbvToSW st t
                    amap <- readIORef (rArrayMap st)
                    let k = IMap.size amap
                    k `seq` modifyIORef (rArrayMap st) (IMap.insert k ("array_" ++ show k, ainfo, ArrayMerge ts ai bi))
                    return k

-- | Declare a new symbolic array, with a potential initial value
declNewSArray :: forall a b. (HasKind a, HasKind b) => (Int -> String) -> Maybe (SBV b) -> Symbolic (SArray a b)
declNewSArray mkNm mbInit = do
   let aknd = kindOf (undefined :: a)
       bknd = kindOf (undefined :: b)
   st <- ask
   amap <- liftIO $ readIORef $ rArrayMap st
   let i = IMap.size amap
       nm = mkNm i
   actx <- liftIO $ case mbInit of
                     Nothing   -> return $ ArrayFree Nothing
                     Just ival -> sbvToSW st ival >>= \sw -> return $ ArrayFree (Just sw)
   liftIO $ modifyIORef (rArrayMap st) (IMap.insert i (nm, (aknd, bknd), actx))
   return $ SArray (aknd, bknd) $ cache $ const $ return i

-- | Arrays implemented internally as functions
--
--    * Internally handled by the library and not mapped to SMT-Lib
--
--    * Reading an uninitialized value is considered an error (will throw exception)
--
--    * Cannot check for equality (internally represented as functions)
--
--    * Can quick-check
--
--    * Typically faster as it gets compiled away during translation
--
data SFunArray a b = SFunArray (SBV a -> SBV b)

instance (HasKind a, HasKind b) => Show (SFunArray a b) where
  show (SFunArray _) = "SFunArray<" ++ showType (undefined :: a) ++ ":" ++ showType (undefined :: b) ++ ">"

-- | Lift a function to an array. Useful for creating arrays in a pure context. (Otherwise use `newArray`.)
mkSFunArray :: (SBV a -> SBV b) -> SFunArray a b
mkSFunArray = SFunArray

-- | Handling constraints
imposeConstraint :: SBool -> Symbolic ()
imposeConstraint c = do st <- ask
                        case runMode st of
                          CodeGen -> error "SBV: constraints are not allowed in code-generation"
                          _       -> do liftIO $ do v <- sbvToSW st c
                                                    modifyIORef (rConstraints st) (v:)

-- | Add a constraint with a given probability
addConstraint :: Maybe Double -> SBool -> SBool -> Symbolic ()
addConstraint Nothing  c _  = imposeConstraint c
addConstraint (Just t) c c'
  | t < 0 || t > 1
  = error $ "SBV: pConstrain: Invalid probability threshold: " ++ show t ++ ", must be in [0, 1]."
  | True
  = do st <- ask
       when (not (isConcreteMode (runMode st))) $ error "SBV: pConstrain only allowed in 'genTest' or 'quickCheck' contexts."
       case () of
         () | t > 0 && t < 1 -> liftIO (throwDice st) >>= \d -> imposeConstraint (if d <= t then c else c')
            | t > 0          -> imposeConstraint c
            | True           -> imposeConstraint c'

---------------------------------------------------------------------------------
-- * Cached values
---------------------------------------------------------------------------------

-- | We implement a peculiar caching mechanism, applicable to the use case in
-- implementation of SBV's.  Whenever we do a state based computation, we do
-- not want to keep on evaluating it in the then-current state. That will
-- produce essentially a semantically equivalent value. Thus, we want to run
-- it only once, and reuse that result, capturing the sharing at the Haskell
-- level. This is similar to the "type-safe observable sharing" work, but also
-- takes into the account of how symbolic simulation executes.
--
-- See Andy Gill's type-safe obervable sharing trick for the inspiration behind
-- this technique: <http://ittc.ku.edu/~andygill/paper.php?label=DSLExtract09>
--
-- Note that this is *not* a general memo utility!
newtype Cached a = Cached (State -> IO a)

-- | Cache a state-based computation
cache :: (State -> IO a) -> Cached a
cache = Cached

-- | Uncache a previously cached computation
uncache :: Cached SW -> State -> IO SW
uncache = uncacheGen rSWCache

-- | Uncache, retrieving array indexes
uncacheAI :: Cached ArrayIndex -> State -> IO ArrayIndex
uncacheAI = uncacheGen rAICache

-- | Generic uncaching. Note that this is entirely safe, since we do it in the IO monad.
uncacheGen :: (State -> IORef (Cache a)) -> Cached a -> State -> IO a
uncacheGen getCache (Cached f) st = do
        let rCache = getCache st
        stored <- readIORef rCache
        sn <- f `seq` makeStableName f
        let h = hashStableName sn
        case maybe Nothing (sn `lookup`) (h `IMap.lookup` stored) of
          Just r  -> return r
          Nothing -> do r <- f st
                        r `seq` modifyIORef rCache (IMap.insertWith (++) h [(sn, r)])
                        return r

-- | Representation of SMTLib Program versions, currently we only know of versions 1 and 2.
-- (NB. Eventually, we should just drop SMTLib1.)
data SMTLibVersion = SMTLib1
                   | SMTLib2
                   deriving Eq

-- | Representation of an SMT-Lib program. In between pre and post goes the refuted models
data SMTLibPgm = SMTLibPgm SMTLibVersion  ( [(String, SW)]          -- alias table
                                          , [String]                -- pre: declarations.
                                          , [String])               -- post: formula
instance NFData SMTLibVersion where rnf _ = ()
instance NFData SMTLibPgm     where rnf _ = ()

instance Show SMTLibPgm where
  show (SMTLibPgm _ (_, pre, post)) = intercalate "\n" $ pre ++ post

-- Other Technicalities..
instance NFData CW where
  rnf (CW x y) = x `seq` y `seq` ()

instance NFData Result where
  rnf (Result kindInfo qcInfo cgs inps consts tbls arrs uis axs pgm cstr outs)
        = rnf kindInfo `seq` rnf qcInfo `seq` rnf cgs  `seq` rnf inps
                       `seq` rnf consts `seq` rnf tbls `seq` rnf arrs
                       `seq` rnf uis    `seq` rnf axs  `seq` rnf pgm
                       `seq` rnf cstr   `seq` rnf outs
instance NFData Kind           where rnf _ = ()
instance NFData ArrayContext   where rnf _ = ()
instance NFData SW             where rnf _ = ()
instance NFData SBVExpr        where rnf _ = ()
instance NFData Quantifier     where rnf _ = ()
instance NFData SBVType        where rnf _ = ()
instance NFData UnintKind      where rnf _ = ()
instance NFData a => NFData (Cached a) where
  rnf (Cached f) = f `seq` ()
instance NFData a => NFData (SBV a) where
  rnf (SBV x y) = rnf x `seq` rnf y `seq` ()
instance NFData SBVPgm where rnf _ = ()

instance NFData SMTResult where
  rnf (Unsatisfiable _)   = ()
  rnf (Satisfiable _ xs)  = rnf xs `seq` ()
  rnf (Unknown _ xs)      = rnf xs `seq` ()
  rnf (ProofError _ xs)   = rnf xs `seq` ()
  rnf (TimeOut _)         = ()

instance NFData SMTModel where
  rnf (SMTModel assocs unints uarrs) = rnf assocs `seq` rnf unints `seq` rnf uarrs `seq` ()

instance NFData SMTScript where
  rnf (SMTScript b m) = rnf b `seq` rnf m `seq` ()

-- | SMT-Lib logics. If left unspecified SBV will pick the logic based on what it determines is needed. However, the
-- user can override this choice using the 'useLogic' parameter to the configuration. This is especially handy if
-- one is experimenting with custom logics that might be supported on new solvers.
data SMTLibLogic
  = AUFLIA    -- ^ Formulas over the theory of linear integer arithmetic and arrays extended with free sort and function symbols but restricted to arrays with integer indices and values
  | AUFLIRA   -- ^ Linear formulas with free sort and function symbols over one- and two-dimentional arrays of integer index and real value
  | AUFNIRA   -- ^ Formulas with free function and predicate symbols over a theory of arrays of arrays of integer index and real value
  | LRA       -- ^ Linear formulas in linear real arithmetic
  | UFLRA     -- ^ Linear real arithmetic with uninterpreted sort and function symbols. 
  | UFNIA     -- ^ Non-linear integer arithmetic with uninterpreted sort and function symbols. 
  | QF_ABV    -- ^ Quantifier-free formulas over the theory of bitvectors and bitvector arrays
  | QF_AUFBV  -- ^ Quantifier-free formulas over the theory of bitvectors and bitvector arrays extended with free sort and function symbols
  | QF_AUFLIA -- ^ Quantifier-free linear formulas over the theory of integer arrays extended with free sort and function symbols
  | QF_AX     -- ^ Quantifier-free formulas over the theory of arrays with extensionality
  | QF_BV     -- ^ Quantifier-free formulas over the theory of fixed-size bitvectors
  | QF_IDL    -- ^ Difference Logic over the integers. Boolean combinations of inequations of the form x - y < b where x and y are integer variables and b is an integer constant
  | QF_LIA    -- ^ Unquantified linear integer arithmetic. In essence, Boolean combinations of inequations between linear polynomials over integer variables
  | QF_LRA    -- ^ Unquantified linear real arithmetic. In essence, Boolean combinations of inequations between linear polynomials over real variables. 
  | QF_NIA    -- ^ Quantifier-free integer arithmetic. 
  | QF_NRA    -- ^ Quantifier-free real arithmetic. 
  | QF_RDL    -- ^ Difference Logic over the reals. In essence, Boolean combinations of inequations of the form x - y < b where x and y are real variables and b is a rational constant. 
  | QF_UF     -- ^ Unquantified formulas built over a signature of uninterpreted (i.e., free) sort and function symbols. 
  | QF_UFBV   -- ^ Unquantified formulas over bitvectors with uninterpreted sort function and symbols. 
  | QF_UFIDL  -- ^ Difference Logic over the integers (in essence) but with uninterpreted sort and function symbols. 
  | QF_UFLIA  -- ^ Unquantified linear integer arithmetic with uninterpreted sort and function symbols. 
  | QF_UFLRA  -- ^ Unquantified linear real arithmetic with uninterpreted sort and function symbols. 
  | QF_UFNRA  -- ^ Unquantified non-linear real arithmetic with uninterpreted sort and function symbols. 
  | QF_FPABV  -- ^ Quantifier-free formulas over the theory of floating point numbers, arrays, and bit-vectors
  | QF_FPA    -- ^ Quantifier-free formulas over the theory of floating point numbers
  deriving Show

-- | Chosen logic for the solver
data Logic = PredefinedLogic SMTLibLogic  -- ^ Use one of the logics as defined by the standard
           | CustomLogic     String       -- ^ Use this name for the logic

instance Show Logic where
  show (PredefinedLogic l) = show l
  show (CustomLogic     s) = s

-- | Translation tricks needed for specific capabilities afforded by each solver
data SolverCapabilities = SolverCapabilities {
         capSolverName              :: String       -- ^ Name of the solver
       , mbDefaultLogic             :: Maybe String -- ^ set-logic string to use in case not automatically determined (if any)
       , supportsMacros             :: Bool         -- ^ Does the solver understand SMT-Lib2 macros?
       , supportsProduceModels      :: Bool         -- ^ Does the solver understand produce-models option setting
       , supportsQuantifiers        :: Bool         -- ^ Does the solver understand SMT-Lib2 style quantifiers?
       , supportsUninterpretedSorts :: Bool         -- ^ Does the solver understand SMT-Lib2 style uninterpreted-sorts
       , supportsUnboundedInts      :: Bool         -- ^ Does the solver support unbounded integers?
       , supportsReals              :: Bool         -- ^ Does the solver support reals?
       , supportsFloats             :: Bool         -- ^ Does the solver support single-precision floating point numbers?
       , supportsDoubles            :: Bool         -- ^ Does the solver support double-precision floating point numbers?
       }

-- | Solver configuration. See also 'z3', 'yices', 'cvc4', 'boolector', 'mathSAT', etc. which are instantiations of this type for those solvers, with
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
         verbose        :: Bool             -- ^ Debug mode
       , timing         :: Bool             -- ^ Print timing information on how long different phases took (construction, solving, etc.)
       , sBranchTimeOut :: Maybe Int        -- ^ How much time to give to the solver for each call of 'sBranch' check. (In seconds. Default: No limit.)
       , timeOut        :: Maybe Int        -- ^ How much time to give to the solver. (In seconds. Default: No limit.)
       , printBase      :: Int              -- ^ Print integral literals in this base (2, 8, 10, and 16 are supported.)
       , printRealPrec  :: Int              -- ^ Print algebraic real values with this precision. (SReal, default: 16)
       , solverTweaks   :: [String]         -- ^ Additional lines of script to give to the solver (user specified)
       , satCmd         :: String           -- ^ Usually "(check-sat)". However, users might tweak it based on solver characteristics.
       , smtFile        :: Maybe FilePath   -- ^ If Just, the generated SMT script will be put in this file (for debugging purposes mostly)
       , useSMTLib2     :: Bool             -- ^ If True, we'll treat the solver as using SMTLib2 input format. Otherwise, SMTLib1
       , solver         :: SMTSolver        -- ^ The actual SMT solver.
       , roundingMode   :: RoundingMode     -- ^ Rounding mode to use for floating-point conversions
       , useLogic       :: Maybe Logic      -- ^ If Nothing, pick automatically. Otherwise, either use the given one, or use the custom string.
       }

instance Show SMTConfig where
  show = show . solver

-- | A model, as returned by a solver
data SMTModel = SMTModel {
        modelAssocs    :: [(String, CW)]        -- ^ Mapping of symbolic values to constants.
     ,  modelArrays    :: [(String, [String])]  -- ^ Arrays, very crude; only works with Yices.
     ,  modelUninterps :: [(String, [String])]  -- ^ Uninterpreted funcs; very crude; only works with Yices.
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

-- | An SMT engine
type SMTEngine = SMTConfig -> Bool -> [(Quantifier, NamedSymVar)] -> [(String, UnintKind)] -> [Either SW (SW, [SW])] -> String -> IO SMTResult

-- | Solvers that SBV is aware of
data Solver = Z3
            | Yices
            | Boolector
            | CVC4
            | MathSAT
            deriving (Show, Enum, Bounded)

-- | An SMT solver
data SMTSolver = SMTSolver {
         name           :: Solver               -- ^ The solver in use
       , executable     :: String               -- ^ The path to its executable
       , options        :: [String]             -- ^ Options to provide to the solver
       , engine         :: SMTEngine            -- ^ The solver engine, responsible for interpreting solver output
       , xformExitCode  :: ExitCode -> ExitCode -- ^ Should we re-interpret exit codes. Most solvers behave rationally, i.e., id will do. Some (like CVC4) don't.
       , capabilities   :: SolverCapabilities   -- ^ Various capabilities of the solver
       }

instance Show SMTSolver where
   show = show . name

-- | Symbolically executable program fragments. This class is mainly used for 'safe' calls, and is sufficently populated internally to cover most use
-- cases. Users can extend it as they wish to allow 'safe' checks for SBV programs that return/take types that are user-defined.
class SExecutable a where
   sName_ :: a -> Symbolic ()
   sName  :: [String] -> a -> Symbolic ()

instance NFData a => SExecutable (Symbolic a) where
   sName_   a = a >>= \r -> rnf r `seq` return ()
   sName []   = sName_
   sName xs   = error $ "SBV.SExecutable.sName: Extra unmapped name(s): " ++ intercalate ", " xs

instance NFData a => SExecutable (SBV a) where
   sName_   v = sName_ (output v)
   sName xs v = sName xs (output v)

-- Unit output
instance SExecutable () where
   sName_   () = sName_   (output ())
   sName xs () = sName xs (output ())

-- List output
instance (NFData a, SymWord a) => SExecutable [SBV a] where
   sName_   vs = sName_   (output vs)
   sName xs vs = sName xs (output vs)

-- 2 Tuple output
instance (NFData a, SymWord a, NFData b, SymWord b) => SExecutable (SBV a, SBV b) where
  sName_ (a, b) = sName_ (output a >> output b)
  sName _       = sName_

-- 3 Tuple output
instance (NFData a, SymWord a, NFData b, SymWord b, NFData c, SymWord c) => SExecutable (SBV a, SBV b, SBV c) where
  sName_ (a, b, c) = sName_ (output a >> output b >> output c)
  sName _          = sName_

-- 4 Tuple output
instance (NFData a, SymWord a, NFData b, SymWord b, NFData c, SymWord c, NFData d, SymWord d) => SExecutable (SBV a, SBV b, SBV c, SBV d) where
  sName_ (a, b, c, d) = sName_ (output a >> output b >> output c >> output c >> output d)
  sName _             = sName_

-- 5 Tuple output
instance (NFData a, SymWord a, NFData b, SymWord b, NFData c, SymWord c, NFData d, SymWord d, NFData e, SymWord e) => SExecutable (SBV a, SBV b, SBV c, SBV d, SBV e) where
  sName_ (a, b, c, d, e) = sName_ (output a >> output b >> output c >> output d >> output e)
  sName _                = sName_

-- 6 Tuple output
instance (NFData a, SymWord a, NFData b, SymWord b, NFData c, SymWord c, NFData d, SymWord d, NFData e, SymWord e, NFData f, SymWord f) => SExecutable (SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) where
  sName_ (a, b, c, d, e, f) = sName_ (output a >> output b >> output c >> output d >> output e >> output f)
  sName _                   = sName_

-- 7 Tuple output
instance (NFData a, SymWord a, NFData b, SymWord b, NFData c, SymWord c, NFData d, SymWord d, NFData e, SymWord e, NFData f, SymWord f, NFData g, SymWord g) => SExecutable (SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) where
  sName_ (a, b, c, d, e, f, g) = sName_ (output a >> output b >> output c >> output d >> output e >> output f >> output g)
  sName _                      = sName_

-- Functions
instance (SymWord a, SExecutable p) => SExecutable (SBV a -> p) where
   sName_        k = forall_   >>= \a -> sName_   $ k a
   sName (s:ss)  k = forall s  >>= \a -> sName ss $ k a
   sName []      k = sName_ k

-- 2 Tuple input
instance (SymWord a, SymWord b, SExecutable p) => SExecutable ((SBV a, SBV b) -> p) where
  sName_        k = forall_  >>= \a -> sName_   $ \b -> k (a, b)
  sName (s:ss)  k = forall s >>= \a -> sName ss $ \b -> k (a, b)
  sName []      k = sName_ k

-- 3 Tuple input
instance (SymWord a, SymWord b, SymWord c, SExecutable p) => SExecutable ((SBV a, SBV b, SBV c) -> p) where
  sName_       k  = forall_  >>= \a -> sName_   $ \b c -> k (a, b, c)
  sName (s:ss) k  = forall s >>= \a -> sName ss $ \b c -> k (a, b, c)
  sName []     k  = sName_ k

-- 4 Tuple input
instance (SymWord a, SymWord b, SymWord c, SymWord d, SExecutable p) => SExecutable ((SBV a, SBV b, SBV c, SBV d) -> p) where
  sName_        k = forall_  >>= \a -> sName_   $ \b c d -> k (a, b, c, d)
  sName (s:ss)  k = forall s >>= \a -> sName ss $ \b c d -> k (a, b, c, d)
  sName []      k = sName_ k

-- 5 Tuple input
instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SExecutable p) => SExecutable ((SBV a, SBV b, SBV c, SBV d, SBV e) -> p) where
  sName_        k = forall_  >>= \a -> sName_   $ \b c d e -> k (a, b, c, d, e)
  sName (s:ss)  k = forall s >>= \a -> sName ss $ \b c d e -> k (a, b, c, d, e)
  sName []      k = sName_ k

-- 6 Tuple input
instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SymWord f, SExecutable p) => SExecutable ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) -> p) where
  sName_        k = forall_  >>= \a -> sName_   $ \b c d e f -> k (a, b, c, d, e, f)
  sName (s:ss)  k = forall s >>= \a -> sName ss $ \b c d e f -> k (a, b, c, d, e, f)
  sName []      k = sName_ k

-- 7 Tuple input
instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SymWord f, SymWord g, SExecutable p) => SExecutable ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) -> p) where
  sName_        k = forall_  >>= \a -> sName_   $ \b c d e f g -> k (a, b, c, d, e, f, g)
  sName (s:ss)  k = forall s >>= \a -> sName ss $ \b c d e f g -> k (a, b, c, d, e, f, g)
  sName []      k = sName_ k
