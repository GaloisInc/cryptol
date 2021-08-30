{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}

module CryptolServer.CallRandom
  where

import System.Random

import Data.Aeson as JSON hiding (Encoding, Value, decode)
import qualified Data.Aeson as JSON
import Data.Typeable (Proxy(..), typeRep)

import Control.Monad.IO.Class (MonadIO(..))

import Argo (makeJSONRPCException)
import qualified Argo.Doc as Doc

import Cryptol.ModuleSystem (checkExpr)
import Cryptol.TypeCheck.Solve (defaultReplExpr)
import Cryptol.TypeCheck.Subst (apSubst, listParamSubst)
import qualified Cryptol.TypeCheck.Type as CT
import qualified Cryptol.Parser.AST as P
import Cryptol.Utils.PP (pretty)

import CryptolServer
import CryptolServer.Data.Expression
import CryptolServer.Data.Type
import CryptolServer.EvalExpr (evalExpression')
import CryptolServer.Exceptions

callRandomDescr :: Doc.Block
callRandomDescr =
  Doc.Paragraph
    [Doc.Text "Evaluate the result of calling a Cryptol function on randomized parameters."]

getEntropy :: MonadIO m => Integer -> m [Bool]
getEntropy w
  | w > 0 = (:) <$> randomIO <*> getEntropy (w - 1)
  | otherwise = pure []

funTypeTake :: Int -> CT.Type -> [CT.Type]
funTypeTake n t
   | n > 0
   , Just (dom, cod) <- CT.tIsFun t
   = dom : funTypeTake (n - 1) cod
   | otherwise = []

randTermOfType :: CT.Type -> CryptolCommand (P.Expr P.PName)
randTermOfType t
  | Just (n, b) <- CT.tIsSeq t
  , CT.tIsBit b
  , Just w <- CT.tIsNum n = do
      entropy <- getEntropy w
      getExpr (Sequence $ Bit <$> entropy)
  | otherwise = raise $ makeJSONRPCException 20300 "Can't generate random term of argument type" (Nothing :: Maybe ())

callRandom :: CallRandomParams -> CryptolCommand JSON.Value
callRandom (CallRandomParams rawFun randCount rawArgs) =
  do fun <- getExpr rawFun
     (_expr, funty, funschema) <- liftModuleCmd (checkExpr fun)
     s <- getTCSolver
     liftIO (defaultReplExpr s funty funschema) >>= \case
       Nothing -> raise (evalPolyErr funschema)
       Just (funtys, _) ->
         do let funsu = listParamSubst funtys
            let funtype = apSubst funsu (CT.sType funschema)
            let randArgTypes = funTypeTake randCount funtype
            randArgs <- traverse randTermOfType randArgTypes
            fixedArgs <- traverse getExpr rawArgs
            let appExpr = mkEApp fun $ randArgs <> fixedArgs
            evalExpression' appExpr

data CallRandomParams
  = CallRandomParams Expression Int [Expression]

instance FromJSON CallRandomParams where
  parseJSON =
    withObject "params for \"call_random\"" $
    \o -> CallRandomParams <$> o .: "function" <*> o .: "random" <*> o .: "arguments"

instance Doc.DescribedMethod CallRandomParams JSON.Value where
  parameterFieldDescription =
    [("function",
      Doc.Paragraph [Doc.Text "The function being called."])
    , ("random",
      Doc.Paragraph [Doc.Text "The number of random arguments the function is being applied to."])
    , ("arguments",
      Doc.Paragraph [Doc.Text "The non-random arguments the function is being applied to."])
    ]

  resultFieldDescription =
    [ ("value",
      Doc.Paragraph [ Doc.Text "A "
                    , Doc.Link (Doc.TypeDesc (typeRep (Proxy @Expression))) "JSON Cryptol expression"
                    , Doc.Text " that denotes the value"
                    ])
    , ("type",
      Doc.Paragraph [ Doc.Text " A"
                    , Doc.Link (Doc.TypeDesc (typeRep (Proxy @JSONSchema))) "JSON Cryptol type"
                    , Doc.Text " that denotes the result type"
                    ])
    , ("type string",
      Doc.Paragraph [Doc.Text "A human-readable representation of the result type"])
    ]
