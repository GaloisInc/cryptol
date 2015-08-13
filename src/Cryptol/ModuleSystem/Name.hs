module Cryptol.ModuleSystem.Name where

type Ident = String

pack :: String -> Ident
pack = id

unpack :: Ident -> String
unpack = id

-- | Module names are just namespaces.
--
-- INVARIANT: the list of strings should never be empty in a valid module name.
newtype ModName = ModName [Ident]
                  deriving (Eq,Ord,Show)

data Name     = Name Ident
              | NewName Pass Int
               deriving (Eq,Ord,Show)

data QName    = QName (Maybe ModName) Name
               deriving (Eq,Ord,Show)

unModName :: ModName -> [String]
unModName (ModName ns) = map unpack ns

mkModName :: [String] -> ModName
mkModName ns = ModName (map pack ns)

mkName :: String -> Name
mkName n = Name (pack n)

-- XXX It would be nice to also mark this as a name that doesn't need to be
-- resolved, if it's going to be created before renaming.
mkPrim :: String -> QName
mkPrim n = mkQual (ModName [pack "Cryptol"]) (Name (pack n))

asPrim :: QName -> Maybe String
asPrim (QName (Just (ModName [m])) (Name n))
  | m == pack "Cryptol" = Just (unpack n)
asPrim _ = Nothing

mkQual :: ModName -> Name -> QName
mkQual  = QName . Just

mkUnqual :: Name -> QName
mkUnqual  = QName Nothing

unqual :: QName -> Name
unqual (QName _ n) = n


data Pass     = NoPat | MonoValues
               deriving (Eq,Ord,Show)
