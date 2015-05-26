module Cryptol.ModuleSystem.Name where


-- | Module names are just namespaces.
--
-- INVARIANT: the list of strings should never be empty in a valid module name.
newtype ModName = ModName [String]
                  deriving (Eq,Ord,Show)

data Name     = Name String
              | NewName Pass Int
               deriving (Eq,Ord,Show)

data QName    = QName (Maybe ModName) Name
               deriving (Eq,Ord,Show)

mkQual :: ModName -> Name -> QName
mkQual  = QName . Just

mkUnqual :: Name -> QName
mkUnqual  = QName Nothing

unqual :: QName -> Name
unqual (QName _ n) = n


data Pass     = NoPat | MonoValues
               deriving (Eq,Ord,Show)
