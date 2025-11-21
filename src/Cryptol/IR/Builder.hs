module Cryptol.IR.Builder
  ( 
    -- * Using built-ins
    makePrim,
    prelPrim,
    floatPrim,

    -- * Helpers
    number,
    char,
    string,

    -- * Types
    TParam,
    AST.Schema(..),
    Type,
    Kind(..),

    -- ** Numeric types
    AST.tNum, 
    AST.tInf,

    -- ** Value types    
    AST.tBit,     
    AST.tInteger, 
    AST.tRational,
    AST.tFloat,    
    AST.tIntMod,   
    AST.tWord,    
    AST.tSeq,     
    AST.tChar,    
    AST.tString,  
    AST.tRec,     
    AST.tTuple,   
    AST.tFun,     
    AST.tNominal,

    -- * Name Generation
    newSchemaParam,
    newTopNameIn,
    newTopName,
    newLocalName,
    

  ) where


import Data.Text(Text)

import qualified Cryptol.Parser.Position as Position
import Cryptol.Parser.Name (NameSource(..))
import           Cryptol.Utils.Ident(PrimIdent,Ident,ModPath(..))
import qualified Cryptol.Utils.Ident as Ident
import           Cryptol.TypeCheck.AST(Expr(..), Type, Kind(..), TParam(..))
import qualified Cryptol.TypeCheck.AST as AST
import qualified Cryptol.TypeCheck.Monad as TCM
import           Cryptol.ModuleSystem.Monad(ModuleM)
import qualified Cryptol.ModuleSystem.Monad as M
import           Cryptol.ModuleSystem.Name(Name,Namespace(..))
import qualified Cryptol.ModuleSystem.Name as Name
import qualified Cryptol.ModuleSystem.Base as Base




--------------------------------------------------------------------------------
-- Working with Primitives
--------------------------------------------------------------------------------

-- | Helper for making primtiives
withPrimMap :: (Name.PrimMap -> a) -> ModuleM a
withPrimMap k = k <$> Base.getPrimMap

-- | Lookup a value level primitive
makePrim :: PrimIdent -> ModuleM Expr
makePrim p = withPrimMap (\pm -> AST.ePrim pm p)

-- | Lookup a value level primitive from module `Cryptol`
prelPrim :: Text -> ModuleM Expr
prelPrim = makePrim . Ident.prelPrim

-- | Lookup a value level primtitive from module `Float`
floatPrim :: Text -> ModuleM Expr
floatPrim = makePrim . Ident.floatPrim

-- | Create a numeric literal
number :: Integer -> Type -> ModuleM Expr
number n t = withPrimMap (\pm -> AST.eNumber pm n t)

-- | Create a character literal 
char :: Char -> ModuleM Expr
char c = withPrimMap (\pm -> AST.eChar pm c)

-- | Create a string literal
string :: String -> ModuleM Expr
string s = withPrimMap (\pm -> AST.eString pm s)



--------------------------------------------------------------------------------
-- Name generation
--------------------------------------------------------------------------------

-- | Generate a fresh top-level name in the given namespace
newTopNameIn :: Namespace -> ModPath -> Ident -> ModuleM Name
newTopNameIn ns mpath i =
  Name.liftSupply
    (Name.mkDeclared ns mpath SystemName i Nothing Position.emptyRange)

-- | Generate a fresh top-level name in the value namespace
newTopName :: ModPath -> Ident -> ModuleM Name
newTopName = newTopNameIn NSValue

-- | Generate a fresh local name in the value name space
newLocalName :: Ident -> ModuleM Name
newLocalName i =
  Name.liftSupply (Name.mkLocal SystemName NSValue i Position.emptyRange)

-- | Generate a fresh type binder to be used in the type signature for the
-- given name.
newSchemaParam :: Name -> Kind -> ModuleM TParam
newSchemaParam nm k =
  do
    tcnames <- M.getNameSeeds
    let u = TCM.seedTVar tcnames
    let tp =
          TParam {
            tpUnique = u,
            tpKind   = k,
            tpFlav   = AST.TPSchemaParam nm,
            tpInfo   =
              AST.TVarInfo {
                AST.tvarDesc   = AST.TVFromSignature nm,
                AST.tvarSource = Position.emptyRange
            }
          }
    M.setNameSeeds tcnames { TCM.seedTVar = u + 1 }
    pure tp



--------------------------------------------------------------------------------
