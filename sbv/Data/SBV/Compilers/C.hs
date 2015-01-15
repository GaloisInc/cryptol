-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Compilers.C
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Compilation of symbolic programs to C
-----------------------------------------------------------------------------

{-# LANGUAGE PatternGuards #-}

module Data.SBV.Compilers.C(compileToC, compileToCLib, compileToC', compileToCLib') where

import Control.DeepSeq                (rnf)
import Data.Char                      (isSpace)
import Data.List                      (nub, intercalate)
import Data.Maybe                     (isJust, isNothing, fromJust)
import qualified Data.Foldable as F   (toList)
import qualified Data.Set      as Set (member, toList)
import System.FilePath                (takeBaseName, replaceExtension)
import System.Random
import Text.PrettyPrint.HughesPJ

import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.PrettyNum (shex, showCFloat, showCDouble)
import Data.SBV.Compilers.CodeGen

---------------------------------------------------------------------------
-- * API
---------------------------------------------------------------------------

-- | Given a symbolic computation, render it as an equivalent collection of files
-- that make up a C program:
--
--   * The first argument is the directory name under which the files will be saved. To save
--     files in the current directory pass @'Just' \".\"@. Use 'Nothing' for printing to stdout.
--
--   * The second argument is the name of the C function to generate.
--
--   * The final argument is the function to be compiled.
--
-- Compilation will also generate a @Makefile@,  a header file, and a driver (test) program, etc.
compileToC :: Maybe FilePath -> String -> SBVCodeGen () -> IO ()
compileToC mbDirName nm f = compileToC' nm f >>= renderCgPgmBundle mbDirName

-- | Lower level version of 'compileToC', producing a 'CgPgmBundle'
compileToC' :: String -> SBVCodeGen () -> IO CgPgmBundle
compileToC' nm f = do rands <- randoms `fmap` newStdGen
                      codeGen SBVToC (defaultCgConfig { cgDriverVals = rands }) nm f

-- | Create code to generate a library archive (.a) from given symbolic functions. Useful when generating code
-- from multiple functions that work together as a library.
--
--   * The first argument is the directory name under which the files will be saved. To save
--     files in the current directory pass @'Just' \".\"@. Use 'Nothing' for printing to stdout.
--
--   * The second argument is the name of the archive to generate.
--
--   * The third argument is the list of functions to include, in the form of function-name/code pairs, similar
--     to the second and third arguments of 'compileToC', except in a list.
compileToCLib :: Maybe FilePath -> String -> [(String, SBVCodeGen ())] -> IO ()
compileToCLib mbDirName libName comps = compileToCLib' libName comps >>= renderCgPgmBundle mbDirName

-- | Lower level version of 'compileToCLib', producing a 'CgPgmBundle'
compileToCLib' :: String -> [(String, SBVCodeGen ())] -> IO CgPgmBundle
compileToCLib' libName comps = mergeToLib libName `fmap` mapM (uncurry compileToC') comps

---------------------------------------------------------------------------
-- * Implementation
---------------------------------------------------------------------------

-- token for the target language
data SBVToC = SBVToC

instance CgTarget SBVToC where
  targetName _ = "C"
  translate _  = cgen

-- Unexpected input, or things we will probably never support
die :: String -> a
die msg = error $ "SBV->C: Unexpected: " ++ msg

-- Unsupported features, or features TBD
tbd :: String -> a
tbd msg = error $ "SBV->C: Not yet supported: " ++ msg

cgen :: CgConfig -> String -> CgState -> Result -> CgPgmBundle
cgen cfg nm st sbvProg
   -- we rnf the main pg and the sig to make sure any exceptions in type conversion pop-out early enough
   -- this is purely cosmetic, of course..
   = rnf (render sig) `seq` rnf (render (vcat body)) `seq` result
  where result = CgPgmBundle bundleKind
                        $ filt [ ("Makefile",  (CgMakefile flags, [genMake (cgGenDriver cfg) nm nmd flags]))
                               , (nm  ++ ".h", (CgHeader [sig],   [genHeader bundleKind nm [sig] extProtos]))
                               , (nmd ++ ".c", (CgDriver,         genDriver cfg randVals nm ins outs mbRet))
                               , (nm  ++ ".c", (CgSource,         body))
                               ]
        body = genCProg cfg nm sig sbvProg ins outs mbRet extDecls
        bundleKind = (cgInteger cfg, cgReal cfg)
        randVals = cgDriverVals cfg
        filt xs  = [c | c@(_, (k, _)) <- xs, need k]
          where need k | isCgDriver   k = cgGenDriver cfg
                       | isCgMakefile k = cgGenMakefile cfg
                       | True           = True
        nmd      = nm ++ "_driver"
        sig      = pprCFunHeader nm ins outs mbRet
        ins      = cgInputs st
        outs     = cgOutputs st
        mbRet    = case cgReturns st of
                     []           -> Nothing
                     [CgAtomic o] -> Just o
                     [CgArray _]  -> tbd "Non-atomic return values"
                     _            -> tbd "Multiple return values"
        extProtos = case cgPrototypes st of
                     [] -> empty
                     xs -> vcat $ text "/* User given prototypes: */" : map text xs
        extDecls  = case cgDecls st of
                     [] -> empty
                     xs -> vcat $ text "/* User given declarations: */" : map text xs ++ [text ""]
        flags    = cgLDFlags st

-- | Pretty print a functions type. If there is only one output, we compile it
-- as a function that returns that value. Otherwise, we compile it as a void function
-- that takes return values as pointers to be updated.
pprCFunHeader :: String -> [(String, CgVal)] -> [(String, CgVal)] -> Maybe SW -> Doc
pprCFunHeader fn ins outs mbRet = retType <+> text fn <> parens (fsep (punctuate comma (map mkParam ins ++ map mkPParam outs)))
  where retType = case mbRet of
                   Nothing -> text "void"
                   Just sw -> pprCWord False sw

mkParam, mkPParam :: (String, CgVal) -> Doc
mkParam  (n, CgAtomic sw)     = pprCWord True  sw <+> text n
mkParam  (_, CgArray  [])     = die "mkParam: CgArray with no elements!"
mkParam  (n, CgArray  (sw:_)) = pprCWord True  sw <+> text "*" <> text n
mkPParam (n, CgAtomic sw)     = pprCWord False sw <+> text "*" <> text n
mkPParam (_, CgArray  [])     = die "mPkParam: CgArray with no elements!"
mkPParam (n, CgArray  (sw:_)) = pprCWord False sw <+> text "*" <> text n

-- | Renders as "const SWord8 s0", etc. the first parameter is the width of the typefield
declSW :: Int -> SW -> Doc
declSW w sw = text "const" <+> pad (showCType sw) <+> text (show sw)
  where pad s = text $ s ++ replicate (w - length s) ' '

-- | Renders as "s0", etc, or the corresponding constant
showSW :: CgConfig -> [(SW, CW)] -> SW -> Doc
showSW cfg consts sw
  | sw == falseSW                 = text "false"
  | sw == trueSW                  = text "true"
  | Just cw <- sw `lookup` consts = mkConst cfg cw
  | True                          = text $ show sw

-- | Words as it would map to a C word
pprCWord :: HasKind a => Bool -> a -> Doc
pprCWord cnst v = (if cnst then text "const" else empty) <+> text (showCType v)

showCType :: HasKind a => a -> String
showCType = show . kindOf

-- | The printf specifier for the type
specifier :: CgConfig -> SW -> Doc
specifier cfg sw = case kindOf sw of
                     KBool         -> spec (False, 1)
                     KBounded b i  -> spec (b, i)
                     KUnbounded    -> spec (True, fromJust (cgInteger cfg))
                     KReal         -> specF (fromJust (cgReal cfg))
                     KFloat        -> specF CgFloat
                     KDouble       -> specF CgDouble
                     KUserSort s _ -> die $ "uninterpreted sort: " ++ s
  where spec :: (Bool, Int) -> Doc
        spec (False,  1) = text "%d"
        spec (False,  8) = text "%\"PRIu8\""
        spec (True,   8) = text "%\"PRId8\""
        spec (False, 16) = text "0x%04\"PRIx16\"U"
        spec (True,  16) = text "%\"PRId16\""
        spec (False, 32) = text "0x%08\"PRIx32\"UL"
        spec (True,  32) = text "%\"PRId32\"L"
        spec (False, 64) = text "0x%016\"PRIx64\"ULL"
        spec (True,  64) = text "%\"PRId64\"LL"
        spec (s, sz)     = die $ "Format specifier at type " ++ (if s then "SInt" else "SWord") ++ show sz
        specF :: CgSRealType -> Doc
        specF CgFloat      = text "%f"
        specF CgDouble     = text "%f"
        specF CgLongDouble = text "%Lf"

-- | Make a constant value of the given type. We don't check for out of bounds here, as it should not be needed.
--   There are many options here, using binary, decimal, etc. We simply
--   8-bit or less constants using decimal; otherwise we use hex.
--   Note that this automatically takes care of the boolean (1-bit) value problem, since it
--   shows the result as an integer, which is OK as far as C is concerned.
mkConst :: CgConfig -> CW -> Doc
mkConst cfg  (CW KReal (CWAlgReal (AlgRational _ r))) = double (fromRational r :: Double) <> sRealSuffix (fromJust (cgReal cfg))
  where sRealSuffix CgFloat      = text "F"
        sRealSuffix CgDouble     = empty
        sRealSuffix CgLongDouble = text "L"
mkConst cfg (CW KUnbounded       (CWInteger i)) = showSizedConst i (True, fromJust (cgInteger cfg))
mkConst _   (CW (KBounded sg sz) (CWInteger i)) = showSizedConst i (sg,   sz)
mkConst _   (CW KFloat (CWFloat f))             = text $ showCFloat f
mkConst _   (CW KDouble (CWDouble d))           = text $ showCDouble d
mkConst _   cw                                  = die $ "mkConst: " ++ show cw

showSizedConst :: Integer -> (Bool, Int) -> Doc
showSizedConst i   (False,  1) = text (if i == 0 then "false" else "true")
showSizedConst i   (False,  8) = integer i
showSizedConst i   (True,   8) = integer i
showSizedConst i t@(False, 16) = text (shex False True t i) <> text "U"
showSizedConst i t@(True,  16) = text (shex False True t i)
showSizedConst i t@(False, 32) = text (shex False True t i) <> text "UL"
showSizedConst i t@(True,  32) = text (shex False True t i) <> text "L"
showSizedConst i t@(False, 64) = text (shex False True t i) <> text "ULL"
showSizedConst i t@(True,  64) = text (shex False True t i) <> text "LL"
showSizedConst i   (True,  1)  = die $ "Signed 1-bit value " ++ show i
showSizedConst i   (s, sz)     = die $ "Constant " ++ show i ++ " at type " ++ (if s then "SInt" else "SWord") ++ show sz

-- | Generate a makefile. The first argument is True if we have a driver.
genMake :: Bool -> String -> String -> [String] -> Doc
genMake ifdr fn dn ldFlags = foldr1 ($$) [l | (True, l) <- lns]
 where ifld = not (null ldFlags)
       ld | ifld = text "${LDFLAGS}"
          | True = empty
       lns = [ (True, text "# Makefile for" <+> nm <> text ". Automatically generated by SBV. Do not edit!")
             , (True, text "")
             , (True, text "# include any user-defined .mk file in the current directory.")
             , (True, text "-include *.mk")
             , (True, text "")
             , (True, text "CC=gcc")
             , (True, text "CCFLAGS?=-Wall -O3 -DNDEBUG -fomit-frame-pointer")
             , (ifld, text "LDFLAGS?=" <> text (unwords ldFlags))
             , (True, text "")
             , (ifdr, text "all:" <+> nmd)
             , (ifdr, text "")
             , (True, nmo <> text (": " ++ ppSameLine (hsep [nmc, nmh])))
             , (True, text "\t${CC} ${CCFLAGS}" <+> text "-c $< -o $@")
             , (True, text "")
             , (ifdr, nmdo <> text ":" <+> nmdc)
             , (ifdr, text "\t${CC} ${CCFLAGS}" <+> text "-c $< -o $@")
             , (ifdr, text "")
             , (ifdr, nmd <> text (": " ++ ppSameLine (hsep [nmo, nmdo])))
             , (ifdr, text "\t${CC} ${CCFLAGS}" <+> text "$^ -o $@" <+> ld)
             , (ifdr, text "")
             , (True, text "clean:")
             , (True, text "\trm -f *.o")
             , (True, text "")
             , (ifdr, text "veryclean: clean")
             , (ifdr, text "\trm -f" <+> nmd)
             , (ifdr, text "")
             ]
       nm   = text fn
       nmd  = text dn
       nmh  = nm <> text ".h"
       nmc  = nm <> text ".c"
       nmo  = nm <> text ".o"
       nmdc = nmd <> text ".c"
       nmdo = nmd <> text ".o"

-- | Generate the header
genHeader :: (Maybe Int, Maybe CgSRealType) -> String -> [Doc] -> Doc -> Doc
genHeader (ik, rk) fn sigs protos =
     text "/* Header file for" <+> nm <> text ". Automatically generated by SBV. Do not edit! */"
  $$ text ""
  $$ text "#ifndef" <+> tag
  $$ text "#define" <+> tag
  $$ text ""
  $$ text "#include <inttypes.h>"
  $$ text "#include <stdint.h>"
  $$ text "#include <stdbool.h>"
  $$ text "#include <math.h>"
  $$ text ""
  $$ text "/* The boolean type */"
  $$ text "typedef bool SBool;"
  $$ text ""
  $$ text "/* The float type */"
  $$ text "typedef float SFloat;"
  $$ text ""
  $$ text "/* The double type */"
  $$ text "typedef double SDouble;"
  $$ text ""
  $$ text "/* Unsigned bit-vectors */"
  $$ text "typedef uint8_t  SWord8 ;"
  $$ text "typedef uint16_t SWord16;"
  $$ text "typedef uint32_t SWord32;"
  $$ text "typedef uint64_t SWord64;"
  $$ text ""
  $$ text "/* Signed bit-vectors */"
  $$ text "typedef int8_t  SInt8 ;"
  $$ text "typedef int16_t SInt16;"
  $$ text "typedef int32_t SInt32;"
  $$ text "typedef int64_t SInt64;"
  $$ text ""
  $$ imapping
  $$ rmapping
  $$ text ("/* Entry point prototype" ++ plu ++ ": */")
  $$ vcat (map (<> semi) sigs)
  $$ text ""
  $$ protos
  $$ text "#endif /*" <+> tag <+> text "*/"
  $$ text ""
 where nm  = text fn
       tag = text "__" <> nm <> text "__HEADER_INCLUDED__"
       plu = if length sigs /= 1 then "s" else ""
       imapping = case ik of
                    Nothing -> empty
                    Just i  ->    text "/* User requested mapping for SInteger.                                 */"
                               $$ text "/* NB. Loss of precision: Target type is subject to modular arithmetic. */"
                               $$ text ("typedef SInt" ++ show i ++ " SInteger;")
                               $$ text ""
       rmapping = case rk of
                    Nothing -> empty
                    Just t  ->    text "/* User requested mapping for SReal.                          */"
                               $$ text "/* NB. Loss of precision: Target type is subject to rounding. */"
                               $$ text ("typedef " ++ show t ++ " SReal;")
                               $$ text ""

sepIf :: Bool -> Doc
sepIf b = if b then text "" else empty

-- | Generate an example driver program
genDriver :: CgConfig -> [Integer] -> String -> [(String, CgVal)] -> [(String, CgVal)] -> Maybe SW -> [Doc]
genDriver cfg randVals fn inps outs mbRet = [pre, header, body, post]
 where pre    =  text "/* Example driver program for" <+> nm <> text ". */"
              $$ text "/* Automatically generated by SBV. Edit as you see fit! */"
              $$ text ""
              $$ text "#include <inttypes.h>"
              $$ text "#include <stdint.h>"
              $$ text "#include <stdbool.h>"
              $$ text "#include <math.h>"
              $$ text "#include <stdio.h>"
       header =  text "#include" <+> doubleQuotes (nm <> text ".h")
              $$ text ""
              $$ text "int main(void)"
              $$ text "{"
       body   =  text ""
              $$ nest 2 (   vcat (map mkInp pairedInputs)
                      $$ vcat (map mkOut outs)
                      $$ sepIf (not (null [() | (_, _, CgArray{}) <- pairedInputs]) || not (null outs))
                      $$ call
                      $$ text ""
                      $$ (case mbRet of
                              Just sw -> text "printf" <> parens (printQuotes (fcall <+> text "=" <+> specifier cfg sw <> text "\\n")
                                                                              <> comma <+> resultVar) <> semi
                              Nothing -> text "printf" <> parens (printQuotes (fcall <+> text "->\\n")) <> semi)
                      $$ vcat (map display outs)
                      )
       post   =   text ""
              $+$ nest 2 (text "return 0" <> semi)
              $$  text "}"
              $$  text ""
       nm = text fn
       pairedInputs = matchRands (map abs randVals) inps
       matchRands _      []                                 = []
       matchRands []     _                                  = die "Run out of driver values!"
       matchRands (r:rs) ((n, CgAtomic sw)            : cs) = ([mkRVal sw r], n, CgAtomic sw) : matchRands rs cs
       matchRands _      ((n, CgArray [])             : _ ) = die $ "Unsupported empty array input " ++ show n
       matchRands rs     ((n, a@(CgArray sws@(sw:_))) : cs)
          | length frs /= l                                 = die "Run out of driver values!"
          | True                                            = (map (mkRVal sw) frs, n, a) : matchRands srs cs
          where l          = length sws
                (frs, srs) = splitAt l rs
       mkRVal sw r = mkConst cfg $ mkConstCW (kindOf sw) r
       mkInp (_,  _, CgAtomic{})         = empty  -- constant, no need to declare
       mkInp (_,  n, CgArray [])         = die $ "Unsupported empty array value for " ++ show n
       mkInp (vs, n, CgArray sws@(sw:_)) =  pprCWord True sw <+> text n <> brackets (int (length sws)) <+> text "= {"
                                                      $$ nest 4 (fsep (punctuate comma (align vs)))
                                                      $$ text "};"
                                         $$ text ""
                                         $$ text "printf" <> parens (printQuotes (text "Contents of input array" <+> text n <> text ":\\n")) <> semi
                                         $$ display (n, CgArray sws)
                                         $$ text ""
       mkOut (v, CgAtomic sw)            = pprCWord False sw <+> text v <> semi
       mkOut (v, CgArray [])             = die $ "Unsupported empty array value for " ++ show v
       mkOut (v, CgArray sws@(sw:_))     = pprCWord False sw <+> text v <> brackets (int (length sws)) <> semi
       resultVar = text "__result"
       call = case mbRet of
                Nothing -> fcall <> semi
                Just sw -> pprCWord True sw <+> resultVar <+> text "=" <+> fcall <> semi
       fcall = nm <> parens (fsep (punctuate comma (map mkCVal pairedInputs ++ map mkOVal outs)))
       mkCVal ([v], _, CgAtomic{}) = v
       mkCVal (vs,  n, CgAtomic{}) = die $ "Unexpected driver value computed for " ++ show n ++ render (hcat vs)
       mkCVal (_,   n, CgArray{})  = text n
       mkOVal (n, CgAtomic{})      = text "&" <> text n
       mkOVal (n, CgArray{})       = text n
       display (n, CgAtomic sw)         = text "printf" <> parens (printQuotes (text " " <+> text n <+> text "=" <+> specifier cfg sw
                                                                                <> text "\\n") <> comma <+> text n) <> semi
       display (n, CgArray [])         =  die $ "Unsupported empty array value for " ++ show n
       display (n, CgArray sws@(sw:_)) =   text "int" <+> nctr <> semi
                                        $$ text "for(" <> nctr <+> text "= 0;" <+> nctr <+> text "<" <+> int (length sws) <+> text "; ++" <> nctr <> text ")"
                                        $$ nest 2 (text "printf" <> parens (printQuotes (text " " <+> entrySpec <+> text "=" <+> spec <> text "\\n")
                                                                 <> comma <+> nctr <+> comma <> entry) <> semi)
                  where nctr      = text n <> text "_ctr"
                        entry     = text n <> text "[" <> nctr <> text "]"
                        entrySpec = text n <> text "[%d]"
                        spec      = specifier cfg sw

-- | Generate the C program
genCProg :: CgConfig -> String -> Doc -> Result -> [(String, CgVal)] -> [(String, CgVal)] -> Maybe SW -> Doc -> [Doc]
genCProg cfg fn proto (Result kindInfo _tvals cgs ins preConsts tbls arrs _ _ (SBVPgm asgns) cstrs _) inVars outVars mbRet extDecls
  | isNothing (cgInteger cfg) && KUnbounded `Set.member` kindInfo
  = error $ "SBV->C: Unbounded integers are not supported by the C compiler."
          ++ "\nUse 'cgIntegerSize' to specify a fixed size for SInteger representation."
  | isNothing (cgReal cfg) && KReal `Set.member` kindInfo
  = error $ "SBV->C: SReal values are not supported by the C compiler."
          ++ "\nUse 'cgSRealType' to specify a custom type for SReal representation."
  | not (null usorts)
  = error $ "SBV->C: Cannot compile functions with uninterpreted sorts: " ++ intercalate ", " usorts
  | not (null cstrs)
  = tbd "Explicit constraints"
  | not (null arrs)
  = tbd "User specified arrays"
  | needsExistentials (map fst ins)
  = error "SBV->C: Cannot compile functions with existentially quantified variables."
  | True
  = [pre, header, post]
 where usorts = [s | KUserSort s _ <- Set.toList kindInfo]
       pre    =  text "/* File:" <+> doubleQuotes (nm <> text ".c") <> text ". Automatically generated by SBV. Do not edit! */"
              $$ text ""
              $$ text "#include <inttypes.h>"
              $$ text "#include <stdint.h>"
              $$ text "#include <stdbool.h>"
              $$ text "#include <math.h>"
       header = text "#include" <+> doubleQuotes (nm <> text ".h")
       post   = text ""
             $$ vcat (map codeSeg cgs)
             $$ extDecls
             $$ proto
             $$ text "{"
             $$ text ""
             $$ nest 2 (   vcat (concatMap (genIO True) inVars)
                        $$ vcat (merge (map genTbl tbls) (map genAsgn assignments))
                        $$ sepIf (not (null assignments) || not (null tbls))
                        $$ vcat (concatMap (genIO False) outVars)
                        $$ maybe empty mkRet mbRet
                       )
             $$ text "}"
             $$ text ""
       nm = text fn
       assignments = F.toList asgns
       codeSeg (fnm, ls) =  text "/* User specified custom code for" <+> doubleQuotes (text fnm) <+> text "*/"
                         $$ vcat (map text ls)
                         $$ text ""
       typeWidth = getMax 0 [len (kindOf s) | (s, _) <- assignments]
                where len (KReal{})           = 5
                      len (KFloat{})          = 6 -- SFloat
                      len (KDouble{})         = 7 -- SDouble
                      len (KUnbounded{})      = 8
                      len KBool               = 5 -- SBool
                      len (KBounded False n)  = 5 + length (show n) -- SWordN
                      len (KBounded True  n)  = 4 + length (show n) -- SIntN
                      len (KUserSort s _)     = die $ "Uninterpreted sort: " ++ s
                      getMax 8 _      = 8  -- 8 is the max we can get with SInteger, so don't bother looking any further
                      getMax m []     = m
                      getMax m (x:xs) = getMax (m `max` x) xs
       consts = (falseSW, falseCW) : (trueSW, trueCW) : preConsts
       isConst s = isJust (lookup s consts)
       genIO :: Bool -> (String, CgVal) -> [Doc]
       genIO True  (cNm, CgAtomic sw) = [declSW typeWidth sw  <+> text "=" <+> text cNm <> semi]
       genIO False (cNm, CgAtomic sw) = [text "*" <> text cNm <+> text "=" <+> showSW cfg consts sw <> semi]
       genIO isInp (cNm, CgArray sws) = zipWith genElt sws [(0::Int)..]
         where genElt sw i
                 | isInp = declSW typeWidth sw <+> text "=" <+> text entry       <> semi
                 | True  = text entry          <+> text "=" <+> showSW cfg consts sw <> semi
                 where entry = cNm ++ "[" ++ show i ++ "]"
       mkRet sw = text "return" <+> showSW cfg consts sw <> semi
       genTbl :: ((Int, Kind, Kind), [SW]) -> (Int, Doc)
       genTbl ((i, _, k), elts) =  (location, static <+> text "const" <+> text (show k) <+> text ("table" ++ show i) <> text "[] = {"
                                              $$ nest 4 (fsep (punctuate comma (align (map (showSW cfg consts) elts))))
                                              $$ text "};")
         where static   = if location == -1 then text "static" else empty
               location = maximum (-1 : map getNodeId elts)
       getNodeId s@(SW _ (NodeId n)) | isConst s = -1
                                     | True      = n
       genAsgn :: (SW, SBVExpr) -> (Int, Doc)
       genAsgn (sw, n) = (getNodeId sw, declSW typeWidth sw <+> text "=" <+> ppExpr cfg consts n <> semi)
       -- merge tables intermixed with assignments, paying attention to putting tables as
       -- early as possible.. Note that the assignment list (second argument) is sorted on its order
       merge :: [(Int, Doc)] -> [(Int, Doc)] -> [Doc]
       merge []               as                  = map snd as
       merge ts               []                  = map snd ts
       merge ts@((i, t):trest) as@((i', a):arest)
         | i < i'                                 = t : merge trest as
         | True                                   = a : merge ts arest

ppExpr :: CgConfig -> [(SW, CW)] -> SBVExpr -> Doc
ppExpr cfg consts (SBVApp op opArgs) = p op (map (showSW cfg consts) opArgs)
  where rtc = cgRTC cfg
        cBinOps = [ (Plus, "+"),  (Times, "*"), (Minus, "-")
                  , (Equal, "=="), (NotEqual, "!="), (LessThan, "<"), (GreaterThan, ">"), (LessEq, "<="), (GreaterEq, ">=")
                  , (And, "&"), (Or, "|"), (XOr, "^")
                  ]
        uninterpret "fp.sqrt" as = let f = case kindOf (head opArgs) of
                                               KFloat  -> text "sqrtf"
                                               KDouble -> text "sqrt"
                                               k       -> die $ "squareRoot on unexpected kind: " ++ show k
                                   in f <> parens (fsep (punctuate comma as))
        uninterpret "fp.fma"  as = let f = case kindOf (head opArgs) of
                                                KFloat  -> text "fmaf"
                                                KDouble -> text "fma"
                                                k       -> die $ "fusedMA on unexpected kind: " ++ show k
                                   in f <> parens (fsep (punctuate comma as))
        uninterpret s []         = text "/* Uninterpreted constant */" <+> text s
        uninterpret s as         = text "/* Uninterpreted function */" <+> text s <> parens (fsep (punctuate comma as))
        p (ArrRead _)       _  = tbd "User specified arrays (ArrRead)"
        p (ArrEq _ _)       _  = tbd "User specified arrays (ArrEq)"
        p (Uninterpreted s) as = uninterpret s as
        p (Extract i j) [a]    = extract i j (head opArgs) a
        p Join [a, b]          = join (let (s1 : s2 : _) = opArgs in (s1, s2, a, b))
        p (Rol i) [a]          = rotate True  i a (head opArgs)
        p (Ror i) [a]          = rotate False i a (head opArgs)
        p (Shl i) [a]          = shift  True  i a (head opArgs)
        p (Shr i) [a]          = shift  False i a (head opArgs)
        p Not [a]              = case kindOf (head opArgs) of
                                   -- be careful about booleans, bitwise complement is not correct for them!
                                   KBool -> text "!" <> a
                                   _     -> text "~" <> a
        p Ite [a, b, c] = a <+> text "?" <+> b <+> text ":" <+> c
        p (LkUp (t, k, _, len) ind def) []
          | not rtc                    = lkUp -- ignore run-time-checks per user request
          | needsCheckL && needsCheckR = cndLkUp checkBoth
          | needsCheckL                = cndLkUp checkLeft
          | needsCheckR                = cndLkUp checkRight
          | True                       = lkUp
          where [index, defVal] = map (showSW cfg consts) [ind, def]
                lkUp = text "table" <> int t <> brackets (showSW cfg consts ind)
                cndLkUp cnd = cnd <+> text "?" <+> defVal <+> text ":" <+> lkUp
                checkLeft  = index <+> text "< 0"
                checkRight = index <+> text ">=" <+> int len
                checkBoth  = parens (checkLeft <+> text "||" <+> checkRight)
                canOverflow True  sz = (2::Integer)^(sz-1)-1 >= fromIntegral len
                canOverflow False sz = (2::Integer)^sz    -1 >= fromIntegral len
                (needsCheckL, needsCheckR) = case k of
                                               KBool           -> (False, canOverflow False (1::Int))
                                               KBounded sg sz  -> (sg, canOverflow sg sz)
                                               KReal           -> die "array index with real value"
                                               KFloat          -> die "array index with float value"
                                               KDouble         -> die "array index with double value"
                                               KUnbounded      -> case cgInteger cfg of
                                                                    Nothing -> (True, True) -- won't matter, it'll be rejected later
                                                                    Just i  -> (True, canOverflow True i)
                                               KUserSort s _   -> die $ "Uninterpreted sort: " ++ s
        -- Div/Rem should be careful on 0, in the SBV world x `div` 0 is 0, x `rem` 0 is x
        -- NB: Quot is supposed to truncate toward 0; Not clear to me if C guarantees this behavior.
        -- Brief googling suggests C99 does indeed truncate toward 0, but other C compilers might differ.
        p Quot [a, b] = parens (b <+> text "== 0") <+> text "?" <+> text "0" <+> text ":" <+> parens (a <+> text "/" <+> b)
        p Rem  [a, b] = parens (b <+> text "== 0") <+> text "?" <+>    a     <+> text ":" <+> parens (a <+> text "%" <+> b)
        p UNeg [a]    = parens (text "-" <+> a)
        p Abs  [a]    = let f = case kindOf (head opArgs) of
                                  KFloat  -> text "fabsf"
                                  KDouble -> text "fabs"
                                  _       -> text "abs"
                        in f <> parens a
        p o [a, b]
          | Just co <- lookup o cBinOps
          = a <+> text co <+> b
        p o args = die $ "Received operator " ++ show o ++ " applied to " ++ show args
        shift toLeft i a s
          | i < 0   = shift (not toLeft) (-i) a s
          | i == 0  = a
          | True    = case kindOf s of
                        KBounded _ sz | i >= sz -> mkConst cfg $ mkConstCW (kindOf s) (0::Integer)
                        KReal                   -> tbd $ "Shift for real quantity: " ++ show (toLeft, i, s)
                        _                       -> a <+> text cop <+> int i
          where cop | toLeft = "<<"
                    | True   = ">>"
        rotate toLeft i a s
          | i < 0   = rotate (not toLeft) (-i) a s
          | i == 0  = a
          | True    = case kindOf s of
                        KBounded True _             -> tbd $ "Rotation of signed quantities: " ++ show (toLeft, i, s)
                        KBounded False sz | i >= sz -> rotate toLeft (i `mod` sz) a s
                        KBounded False sz           ->     parens (a <+> text cop  <+> int i)
                                                      <+> text "|"
                                                      <+> parens (a <+> text cop' <+> int (sz - i))
                        KUnbounded                  -> shift toLeft i a s -- For SInteger, rotate is the same as shift in Haskell
                        _                           -> tbd $ "Rotation for unbounded quantity: " ++ show (toLeft, i, s)
          where (cop, cop') | toLeft = ("<<", ">>")
                            | True   = (">>", "<<")
        -- TBD: below we only support the values that SBV actually currently generates.
        -- we would need to add new ones if we generate others. (Check instances in Data/SBV/BitVectors/Splittable.hs).
        extract hi lo i a = case (hi, lo, kindOf i) of
                              ( 0,  0, KUnbounded)        -> text "(SReal)" <+> a  -- special SInteger -> SReal conversion
                              (63, 32, KBounded False 64) -> text "(SWord32)" <+> parens (a <+> text ">> 32")
                              (31,  0, KBounded False 64) -> text "(SWord32)" <+> a
                              (31, 16, KBounded False 32) -> text "(SWord16)" <+> parens (a <+> text ">> 16")
                              (15,  0, KBounded False 32) -> text "(SWord16)" <+> a
                              (15,  8, KBounded False 16) -> text "(SWord8)"  <+> parens (a <+> text ">> 8")
                              ( 7,  0, KBounded False 16) -> text "(SWord8)"  <+> a
                              -- the followings are used by sign-conversions. (Check instances in Data/SBV/BitVectors/SignCast.hs).
                              (63,  0, KBounded False 64) -> text "(SInt64)"  <+> a
                              (63,  0, KBounded True  64) -> text "(SWord64)" <+> a
                              (31,  0, KBounded False 32) -> text "(SInt32)"  <+> a
                              (31,  0, KBounded True  32) -> text "(SWord32)" <+> a
                              (15,  0, KBounded False 16) -> text "(SInt16)"  <+> a
                              (15,  0, KBounded True  16) -> text "(SWord16)" <+> a
                              ( 7,  0, KBounded False  8) -> text "(SInt8)"   <+> a
                              ( 7,  0, KBounded True   8) -> text "(SWord8)"  <+> a
                              ( _,  _, k                ) -> tbd $ "extract with " ++ show (hi, lo, k, i)
        -- TBD: ditto here for join, just like extract above
        join (i, j, a, b) = case (kindOf i, kindOf j) of
                              (KBounded False  8, KBounded False  8) -> parens (parens (text "(SWord16)" <+> a) <+> text "<< 8")  <+> text "|" <+> parens (text "(SWord16)" <+> b)
                              (KBounded False 16, KBounded False 16) -> parens (parens (text "(SWord32)" <+> a) <+> text "<< 16") <+> text "|" <+> parens (text "(SWord32)" <+> b)
                              (KBounded False 32, KBounded False 32) -> parens (parens (text "(SWord64)" <+> a) <+> text "<< 32") <+> text "|" <+> parens (text "(SWord64)" <+> b)
                              (k1,                k2)                -> tbd $ "join with " ++ show ((k1, i), (k2, j))

-- same as doubleQuotes, except we have to make sure there are no line breaks..
-- Otherwise breaks the generated code.. sigh
printQuotes :: Doc -> Doc
printQuotes d = text $ '"' : ppSameLine d ++ "\""

-- Remove newlines.. Useful when generating Makefile and such
ppSameLine :: Doc -> String
ppSameLine = trim . render
 where trim ""        = ""
       trim ('\n':cs) = ' ' : trim (dropWhile isSpace cs)
       trim (c:cs)    = c   : trim cs

-- Align a bunch of docs to occupy the exact same length by padding in the left by space
-- this is ugly and inefficient, but easy to code..
align :: [Doc] -> [Doc]
align ds = map (text . pad) ss
  where ss    = map render ds
        l     = maximum (0 : map length ss)
        pad s = replicate (l - length s) ' ' ++ s

-- | Merge a bunch of bundles to generate code for a library
mergeToLib :: String -> [CgPgmBundle] -> CgPgmBundle
mergeToLib libName bundles
  | length nubKinds /= 1
  = error $  "Cannot merge programs with differing SInteger/SReal mappings. Received the following kinds:\n"
          ++ unlines (map show nubKinds)
  | True
  = CgPgmBundle bundleKind $ sources ++ libHeader : [libDriver | anyDriver] ++ [libMake | anyMake]
  where kinds       = [k | CgPgmBundle k _ <- bundles]
        nubKinds    = nub kinds
        bundleKind  = head nubKinds
        files       = concat [fs | CgPgmBundle _ fs <- bundles]
        sigs        = concat [ss | (_, (CgHeader ss, _)) <- files]
        anyMake     = not (null [() | (_, (CgMakefile{}, _)) <- files])
        drivers     = [ds | (_, (CgDriver, ds)) <- files]
        anyDriver   = not (null drivers)
        mkFlags     = nub (concat [xs | (_, (CgMakefile xs, _)) <- files])
        sources     = [(f, (CgSource, [pre, libHInclude, post])) | (f, (CgSource, [pre, _, post])) <- files]
        sourceNms   = map fst sources
        libHeader   = (libName ++ ".h", (CgHeader sigs, [genHeader bundleKind libName sigs empty]))
        libHInclude = text "#include" <+> text (show (libName ++ ".h"))
        libMake     = ("Makefile", (CgMakefile mkFlags, [genLibMake anyDriver libName sourceNms mkFlags]))
        libDriver   = (libName ++ "_driver.c", (CgDriver, mergeDrivers libName libHInclude (zip (map takeBaseName sourceNms) drivers)))

-- | Create a Makefile for the library
genLibMake :: Bool -> String -> [String] -> [String] -> Doc
genLibMake ifdr libName fs ldFlags = foldr1 ($$) [l | (True, l) <- lns]
 where ifld = not (null ldFlags)
       ld | ifld = text "${LDFLAGS}"
          | True = empty
       lns = [ (True, text "# Makefile for" <+> nm <> text ". Automatically generated by SBV. Do not edit!")
             , (True,  text "")
             , (True,  text "# include any user-defined .mk file in the current directory.")
             , (True,  text "-include *.mk")
             , (True,  text "")
             , (True,  text "CC=gcc")
             , (True,  text "CCFLAGS?=-Wall -O3 -DNDEBUG -fomit-frame-pointer")
             , (ifld,  text "LDFLAGS?=" <> text (unwords ldFlags))
             , (True,  text "AR=ar")
             , (True,  text "ARFLAGS=cr")
             , (True,  text "")
             , (not ifdr,  text ("all: " ++ liba))
             , (ifdr,      text ("all: " ++ unwords [liba, libd]))
             , (True,  text "")
             , (True,  text liba <> text (": " ++ unwords os))
             , (True,  text "\t${AR} ${ARFLAGS} $@ $^")
             , (True,  text "")
             , (ifdr,  text libd <> text (": " ++ unwords [libd ++ ".c", libh]))
             , (ifdr,  text ("\t${CC} ${CCFLAGS} $< -o $@ " ++ liba) <+> ld)
             , (ifdr,  text "")
             , (True,  vcat (zipWith mkObj os fs))
             , (True,  text "clean:")
             , (True,  text "\trm -f *.o")
             , (True,  text "")
             , (True,  text "veryclean: clean")
             , (not ifdr,  text "\trm -f" <+> text liba)
             , (ifdr,      text "\trm -f" <+> text (unwords [liba, libd]))
             , (True,  text "")
             ]
       nm = text libName
       liba = libName ++ ".a"
       libh = libName ++ ".h"
       libd = libName ++ "_driver"
       os   = map (`replaceExtension` ".o") fs
       mkObj o f =  text o <> text (": " ++ unwords [f, libh])
                 $$ text "\t${CC} ${CCFLAGS} -c $< -o $@"
                 $$ text ""

-- | Create a driver for a library
mergeDrivers :: String -> Doc -> [(FilePath, [Doc])] -> [Doc]
mergeDrivers libName inc ds = pre : concatMap mkDFun ds ++ [callDrivers (map fst ds)]
  where pre =  text "/* Example driver program for" <+> text libName <> text ". */"
            $$ text "/* Automatically generated by SBV. Edit as you see fit! */"
            $$ text ""
            $$ text "#include <inttypes.h>"
            $$ text "#include <stdint.h>"
            $$ text "#include <stdbool.h>"
            $$ text "#include <math.h>"
            $$ text "#include <stdio.h>"
            $$ inc
        mkDFun (f, [_pre, _header, body, _post]) = [header, body, post]
           where header =  text ""
                        $$ text ("void " ++ f ++ "_driver(void)")
                        $$ text "{"
                 post   =  text "}"
        mkDFun (f, _) = die $ "mergeDrivers: non-conforming driver program for " ++ show f
        callDrivers fs =   text ""
                       $$  text "int main(void)"
                       $$  text "{"
                       $+$ nest 2 (vcat (map call fs))
                       $$  nest 2 (text "return 0;")
                       $$  text "}"
        call f =  text psep
               $$ text ptag
               $$ text psep
               $$ text (f ++ "_driver();")
               $$ text ""
           where tag  = "** Driver run for " ++ f ++ ":"
                 ptag = "printf(\"" ++ tag ++ "\\n\");"
                 lsep = replicate (length tag) '='
                 psep = "printf(\"" ++ lsep ++ "\\n\");"
