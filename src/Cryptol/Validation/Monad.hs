-- |
-- Module      :  Cryptol.Validation.Monad
-- Copyright   :  (c) 2013-2023 Galois, Inc.
-- License     :  BSD3
-- Maintainer  :  cryptol@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE FlexibleInstances #-}

module Cryptol.Validation.Monad where

import qualified Control.Monad.State.Strict as State
import           Control.Monad.State.Strict (StateT)
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Data.Map (Map)
import           Data.Set (Set)
import           Data.List(find, foldl')
import           Data.Maybe(mapMaybe,fromMaybe)
import qualified Cryptol.Parser.AST as P


--Validation Monad-------------------------------------------------------------------
type Validation a = StateT ValidationState a

--Validation Environment Interaction ------------------------------------------------

-- | User modifiable validation environment, for things like SMT solver, number of tests, etc.
type ValidationEnv = Map.Map String ValidationVal

data ValidationVal
  = ValidationString String
  | ValidationNum    !Int
  | ValidationBool   Bool
    deriving (Show)

mkValidationEnv :: P.PropertyOptions -> ValidationEnv
mkValidationEnv opts = undefined


-- | Validaiton State
data ValidationState = ValidationState
  {
    validationEnv     :: ValidationEnv
    -- ^ Validation settings
  }
-- | Set a validation option.
setValidationSetting :: String -> String -> Validation ()
setValidationSetting name val = undefined


-- | Get a validation setting, using Maybe for failure.
tryGetValidationSetting :: String -> Validation (Maybe ValidationVal)
tryGetValidationSetting name = undefined

-- | Get a validation setting, when it's known to exist.  Fail with panic when it
-- doesn't.
getValidationSetting :: String -> Validation ValidationVal
getValidationSetting name = undefined

setValidationSettingWithVal :: String -> ValidationVal -> Validation ()
setValidationSettingWithVal optName val = undefined

getKnownValidationSetting :: IsValidationVal a => String -> Validation a
getKnownValidationSetting x = fromValidaitonVal <$> getValidationSetting x

class IsValidationVal a where
  fromValidationVal :: ValidationVal -> a

instance IsValidationVal Bool where
  fromValidationVal x = case x of
                   ValidationBool b -> b
                   _         -> badIsValidation "Bool"

instance IsValidationVal Int where
  fromValidationVal x = case x of
                   ValidationNum b -> b
                   _         -> badIsValidation "Num"

instance IsValidationVal String where
  fromValidationVal x = case x of
                   ValidationString b -> b
                   _           -> badIsValidation "String"


badIsValidation :: String -> a
badIsValidation x = panic "fromValidationVal" [ "[Validation] Expected a `" ++ x ++ "` value." ]

