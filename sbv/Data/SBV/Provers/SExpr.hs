-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Provers.SExpr
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Parsing of S-expressions (mainly used for parsing SMT-Lib get-value output)
-----------------------------------------------------------------------------

module Data.SBV.Provers.SExpr where

import Control.Monad.Error ()             -- for Monad (Either String) instance
import Data.Char           (isDigit, ord)
import Data.List           (isPrefixOf)
import Numeric             (readInt, readDec, readHex, fromRat)

import Data.SBV.BitVectors.AlgReals
import Data.SBV.BitVectors.Data (nan, infinity)

-- | ADT S-Expression format, suitable for representing get-model output of SMT-Lib
data SExpr = ECon    String
           | ENum    Integer
           | EReal   AlgReal
           | EFloat  Float
           | EDouble Double
           | EApp    [SExpr]
           deriving Show

-- | Parse a string into an SExpr, potentially failing with an error message
parseSExpr :: String -> Either String SExpr
parseSExpr inp = do (sexp, extras) <- parse inpToks
                    if null extras
                       then return sexp
                       else die "Extra tokens after valid input"
  where inpToks = let cln ""          sofar = sofar
                      cln ('(':r)     sofar = cln r (" ( " ++ sofar)
                      cln (')':r)     sofar = cln r (" ) " ++ sofar)
                      cln (':':':':r) sofar = cln r (" :: " ++ sofar)
                      cln (c:r)       sofar = cln r (c:sofar)
                  in reverse (map reverse (words (cln inp "")))
        die w = fail $  "SBV.Provers.SExpr: Failed to parse S-Expr: " ++ w
                     ++ "\n*** Input : <" ++ inp ++ ">"
        parse []         = die "ran out of tokens"
        parse ("(":toks) = do (f, r) <- parseApp toks []
                              f' <- cvt (EApp f)
                              return (f', r)
        parse (")":_)    = die "extra tokens after close paren"
        parse [tok]      = do t <- pTok tok
                              return (t, [])
        parse _          = die "ill-formed s-expr"
        parseApp []         _     = die "failed to grab s-expr application"
        parseApp (")":toks) sofar = return (reverse sofar, toks)
        parseApp ("(":toks) sofar = do (f, r) <- parse ("(":toks)
                                       parseApp r (f : sofar)
        parseApp (tok:toks) sofar = do t <- pTok tok
                                       parseApp toks (t : sofar)
        pTok "false"              = return $ ENum 0
        pTok "true"               = return $ ENum 1
        pTok ('0':'b':r)          = mkNum $ readInt 2 (`elem` "01") (\c -> ord c - ord '0') r
        pTok ('b':'v':r)          = mkNum $ readDec (takeWhile (/= '[') r)
        pTok ('#':'b':r)          = mkNum $ readInt 2 (`elem` "01") (\c -> ord c - ord '0') r
        pTok ('#':'x':r)          = mkNum $ readHex r
        pTok n
          | not (null n) && isDigit (head n)
          = if '.' `elem` n then getReal n
            else mkNum  $ readDec n
        pTok n                 = return $ ECon n
        mkNum [(n, "")] = return $ ENum n
        mkNum _         = die "cannot read number"
        getReal n = return $ EReal $ mkPolyReal (Left (exact, n'))
          where exact = not ("?" `isPrefixOf` reverse n)
                n' | exact = n
                   | True  = init n
        -- simplify numbers and root-obj values
        cvt (EApp [ECon "/", EReal a, EReal b])                    = return $ EReal (a / b)
        cvt (EApp [ECon "/", EReal a, ENum  b])                    = return $ EReal (a             / fromInteger b)
        cvt (EApp [ECon "/", ENum  a, EReal b])                    = return $ EReal (fromInteger a /             b)
        cvt (EApp [ECon "/", ENum  a, ENum  b])                    = return $ EReal (fromInteger a / fromInteger b)
        cvt (EApp [ECon "-", EReal a])                             = return $ EReal (-a)
        cvt (EApp [ECon "-", ENum a])                              = return $ ENum  (-a)
        -- bit-vector value as CVC4 prints: (_ bv0 16) for instance
        cvt (EApp [ECon "_", ENum a, ENum _b])                     = return $ ENum a
        cvt (EApp [ECon "root-obj", EApp (ECon "+":trms), ENum k]) = do ts <- mapM getCoeff trms
                                                                        return $ EReal $ mkPolyReal (Right (k, ts))
        cvt (EApp [ECon "as", n, EApp [ECon "_", ECon "FP", ENum 11, ENum 53]]) = getDouble n
        cvt (EApp [ECon "as", n, EApp [ECon "_", ECon "FP", ENum  8, ENum 24]]) = getFloat  n
        cvt x                                                      = return x
        getCoeff (EApp [ECon "*", ENum k, EApp [ECon "^", ECon "x", ENum p]]) = return (k, p)  -- kx^p
        getCoeff (EApp [ECon "*", ENum k,                 ECon "x"        ] ) = return (k, 1)  -- kx
        getCoeff (                        EApp [ECon "^", ECon "x", ENum p] ) = return (1, p)  --  x^p
        getCoeff (                                        ECon "x"          ) = return (1, 1)  --  x
        getCoeff (                ENum k                                    ) = return (k, 0)  -- k
        getCoeff x = die $ "Cannot parse a root-obj,\nProcessing term: " ++ show x
        getDouble (ECon s)  = case (s, rdFP (dropWhile (== '+') s)) of
                                ("plusInfinity",  _     ) -> return $ EDouble infinity
                                ("minusInfinity", _     ) -> return $ EDouble (-infinity)
                                ("NaN",           _     ) -> return $ EDouble nan
                                (_,               Just v) -> return $ EDouble v
                                _                         -> die $ "Cannot parse a double value from: " ++ s
        getDouble (EReal r) = return $ EDouble $ fromRat $ toRational r
        getDouble x         = die $ "Cannot parse a double value from: " ++ show x
        getFloat (ECon s)   = case (s, rdFP (dropWhile (== '+') s)) of
                                ("plusInfinity",  _     ) -> return $ EFloat infinity
                                ("minusInfinity", _     ) -> return $ EFloat (-infinity)
                                ("NaN",           _     ) -> return $ EFloat nan
                                (_,               Just v) -> return $ EFloat v
                                _                         -> die $ "Cannot parse a float value from: " ++ s
        getFloat (EReal r)  = return $ EFloat $ fromRat $ toRational r
        getFloat x          = die $ "Cannot parse a float value from: " ++ show x

-- | Parses the Z3 floating point formatted numbers like so: 1.321p5/1.2123e9 etc.
rdFP :: (Read a, RealFloat a) => String -> Maybe a
rdFP s = case break (`elem` "pe") s of
           (m, 'p':e) -> rd m >>= \m' -> rd e >>= \e' -> return $ m' * ( 2 ** e')
           (m, 'e':e) -> rd m >>= \m' -> rd e >>= \e' -> return $ m' * (10 ** e')
           (m, "")    -> rd m
           _          -> Nothing
 where rd v = case reads v of
                [(n, "")] -> Just n
                _         -> Nothing
