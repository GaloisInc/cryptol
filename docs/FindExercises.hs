#!/usr/bin/env runhaskell
{-# Language RecordWildCards #-}
module Main(main) where

import Data.List(isPrefixOf)


main :: IO ()
main = interact (pp . findExercises)
  where
  pp (es,as)        = unlines $ ppMany "Exercises" es ++
                                ppMany "Answers" as
  ppMany h xs       = h : "-------------" : map ppEnv xs
  ppEnv Env { .. }  = envName ++ ":" ++ show envStart ++ "--" ++ show envEnd ++
                      "(" ++ show (info envLines) ++ ")"
  info              = length . findVerbatim




--------------------------------------------------------------------------------
data Line = Line { lineNo :: Int, lineText :: String }

data Env = Env
  { envName           :: String
  , envStart, envEnd  :: Int       -- location in latex, includes \begin \end
  , envLines          :: [Line]
  }

findExercises :: String -> ([Env],[Env])
findExercises = noEx [] [] () . zipWith toLine [1..] . lines
  where toLine lineNo lineText = Line { .. }

type ExS s = [Env] -> [Env] -> s -> [Line] -> ([Env],[Env])

noEx :: ExS ()
noEx es as _ xs =
  case xs of
    [] -> (es,as)
    Line { .. } : more
      | Just nm <- startExercise lineText -> inEx  es as (lineNo, nm, []) more
      | Just nm <- startAnswer lineText   -> inAns es as (lineNo, nm, []) more
      | otherwise                         -> noEx  es as ()               more

inEx :: ExS (Int,String,[Line])
inEx es as (envStart,envName,ls) xs =
  case xs of
    [] -> error $ unwords [ show envStart ++ ":"
                          , "Unterminated exercise", show envName ]
    l : more
      | endExercise (lineText l) ->
        let ex = Env { envLines = reverse ls, envEnd = lineNo l, .. }
        in noEx (ex : es) as () more
      | otherwise -> inEx es as (envStart,envName,l:ls) more

inAns :: ExS (Int,String,[Line])
inAns es as (envStart,envName,ls) xs =
  case xs of
    [] -> error $ unwords [ show envStart ++ ":"
                          , "Unterminated answer", show envName ]
    l : more
      | endAnswer (lineText l) ->
        let ex = Env { envLines = reverse ls, envEnd = lineNo l, .. }
        in noEx es (ex : as) () more
      | otherwise -> inAns es as (envStart,envName,l:ls) more


findVerbatim :: [Line] -> [Env]
findVerbatim ls =
  case break (startVerbatim . lineText) ls of
    (_,l:more) ->
      case break (endVerbatim . lineText) more of
        (ls,e:rest) ->
          Env { envName = "Verbatim"
              , envStart  = lineNo l
              , envEnd    = lineNo e
              , envLines  = ls
              } : findVerbatim rest
        _ -> error (show (lineNo l) ++ ": Unterminated verbatim")
    _ -> []

--------------------------------------------------------------------------------



--------------------------------------------------------------------------------
startVerbatim :: String -> Bool
startVerbatim x = pref `isPrefixOf` x
  where
  pref = "\\begin{Verbatim}"

endVerbatim :: String -> Bool
endVerbatim x = pref `isPrefixOf` x
  where
  pref = "\\end{Verbatim}"

startExercise :: String -> Maybe String
startExercise x
  | pref `isPrefixOf` x = Just name
  | otherwise           = Nothing
  where
  pref  = "\\begin{Exercise}\\label{ex:"
  name  = takeWhile (/= '}') (drop (length pref) x)

endExercise :: String -> Bool
endExercise x = pref `isPrefixOf` x
  where
  pref = "\\end{Exercise}"


startAnswer :: String -> Maybe String
startAnswer x
  | pref `isPrefixOf` x = Just name
  | otherwise           = Nothing
  where
  pref  = "\\begin{Answer}\\ansref{ex:"
  name  = takeWhile (/= '}') (drop (length pref) x)

endAnswer :: String -> Bool
endAnswer x = pref `isPrefixOf` x
  where
  pref = "\\end{Answer}"

