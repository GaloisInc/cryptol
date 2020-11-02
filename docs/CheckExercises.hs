module Main(main) where

import qualified Text.LaTeX.Base.Parser as LP

import Options.Applicative

data Opts = Opts { latexFile :: FilePath }
  deriving Show

optsParser :: Parser Opts
optsParser = Opts
  <$> strArgument (help "path to latex file")

main :: IO ()
main = do
  opts <- execParser p
  eLatex <- LP.parseLaTeXFile (latexFile opts)
  case eLatex of
    Left err -> print err
    Right _ -> putStrLn "Successful"
  where p = info (optsParser <**> helper)
            ( fullDesc
              <> progDesc "Test the exercises in a cryptol LaTeX file"
              <> header "check-exercises -- test cryptol exercises"
            )
