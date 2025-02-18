{- |
This module follows the convention found in <https://git-scm.com/docs/gitignore>
-}
module Cryptol.Project.WildMatch (wildmatch) where

import Data.Char
import System.FilePath

-- | `wildmatch p x` checks if file `x` matches pattern `p`.
wildmatch :: String -> FilePath -> Bool
wildmatch mbNegP x
  -- When a pattern contains a path separator, it matches the whole path
  | '/' `elem` p = mbNeg (matchP (ensureLeadingSlash p) (ensureLeadingSlash x))
  -- When the pattern contains no path separator it only matches the filename
  | otherwise    = mbNeg (matchP p (takeFileName x))
  where
  (mbNeg,p) =
    case mbNegP of
      '!':rest -> (not,rest)
      _        -> (id,mbNegP)


-- | Normalize a path pattern to start with a leading slash for consistency later
ensureLeadingSlash :: String -> String
ensureLeadingSlash ('/':p) = '/':p
ensureLeadingSlash p       = '/':p

------------------
-- Path processing
------------------

matchP :: String -> FilePath -> Bool

matchP "/**" _ = True -- Accepts everything

matchP ('/':'*':'*':'/':p) ('/':xs) =
  matchP ('/':p) ('/':xs) ||
  matchP ('/':'*':'*':'/':p) (dropWhile ('/'/=) xs)

matchP ('/':'*':'*':'/':_p) _ = False

-- escaped characters match literally
matchP ('\\':a:p) (x:xs) = a==x && matchP p xs
matchP ('\\':_)   ""     = False

-- match zero or more component characters
matchP ('*':p) (x:xs) = matchP p (x:xs) || ('/' /= x) && matchP ('*':p) xs
matchP ('*':p) ""     = matchP p ""

-- match zero or one component characters
matchP ('?':p) (x : xs) = matchP p (x : xs) || ('/' /= x) && matchP p xs
matchP ('?':p) ""       = matchP p ""

-- process a character class
matchP ('[':p) (x:xs)
  | x == '/'                         = False
  | Just (f, p') <- parseCharClass p = f x && matchP p' xs
matchP ('[':_) _                     = False

-- literal match
matchP (a:p) (x:xs) = a==x && matchP p xs
matchP (_a:_p) ""   = False

matchP "" xs        = null xs

-----------------------------
-- Character class processing
-----------------------------

parseCharClass :: String -> Maybe (Char -> Bool, String)

-- leading ! negates a character class
parseCharClass ('!':p) =
 do (f, p') <- parseCharClass1 True p
    Just (not . f, p')
parseCharClass p = parseCharClass1 True p

-- A ] in the first position is a literal match
parseCharClass1 :: Bool -> [Char] -> Maybe (Char -> Bool, [Char])
parseCharClass1 False (']':p) =
  Just (const False, p)

parseCharClass1 first (x:'-':y:p)
  | first || x /= ']', y /= ']' = cc (\c -> x <= c && c <= y) p

parseCharClass1 _ ('[':':':p) =
  case span (\x -> 'a' <= x && x <= 'z') p of
    ("alnum", ':':']':p1) -> cc isAlphaNum p1
    ("cntrl", ':':']':p1) -> cc isControl p1
    ("lower", ':':']':p1) -> cc isLower p1
    ("space", ':':']':p1) -> cc isSpace p1
    ("alpha", ':':']':p1) -> cc isAlpha p1
    ("digit", ':':']':p1) -> cc isDigit p1
    ("print", ':':']':p1) -> cc isPrint p1
    ("upper", ':':']':p1) -> cc isUpper p1
    ("blank", ':':']':p1) -> cc (`elem` " \t") p1
    ("graph", ':':']':p1) -> cc (\x -> isAlphaNum x || isPunctuation x) p1
    ("punct", ':':']':p1) -> cc isPunctuation p1
    ("xdigit", ':':']':p1) -> cc isHexDigit p1
    (_       , ':':']':_) -> Nothing
    _ -> cc ('['==) (':':p)

parseCharClass1 _ (x:p) = cc (x==) p
parseCharClass1 _ ""    = Nothing

-- Helper for continuing to build a character class matcher
cc :: (Char -> Bool) -> [Char] -> Maybe (Char -> Bool, [Char])
cc f p =
 do (g, p') <- parseCharClass1 False p
    Just (\x -> f x || g x, p')
