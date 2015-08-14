{-# LANGUAGE DeriveGeneric #-}
module Cryptol.ModuleSystem.Name where

import GHC.Generics (Generic)
import Control.DeepSeq

-- | Module names are just namespaces.
--
-- INVARIANT: the list of strings should never be empty in a valid module name.
newtype ModName = ModName [String]
                  deriving (Eq,Ord,Show,Generic)

instance NFData ModName

data Name     = Name String
              | NewName Pass Int
               deriving (Eq,Ord,Show,Generic)

instance NFData Name

data QName    = QName (Maybe ModName) Name
               deriving (Eq,Ord,Show,Generic)

instance NFData QName

-- XXX It would be nice to also mark this as a name that doesn't need to be
-- resolved, if it's going to be created before renaming.
mkPrim :: String -> QName
mkPrim n = mkQual (ModName ["Cryptol"]) (Name n)

mkQual :: ModName -> Name -> QName
mkQual  = QName . Just

mkUnqual :: Name -> QName
mkUnqual  = QName Nothing

unqual :: QName -> Name
unqual (QName _ n) = n


data Pass = NoPat | MonoValues
  deriving (Eq,Ord,Show,Generic)

instance NFData Pass
