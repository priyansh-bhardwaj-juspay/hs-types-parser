module Types where

import GHC.Generics
import qualified Data.HashMap.Strict as HM
import Data.Hashable
import Data.Aeson
import Control.Lens (Lens', (^.))
import Data.Generics.Labels ()

data ImportItemIncludes = All | Some [String] | None
  deriving (Show, Generic)

data ImportItem = ImportItem
  { name :: String
  , includes :: ImportItemIncludes
  }
  deriving (Show, Generic)

data SpecsList = Include [ImportItem] | Hide [ImportItem]
  deriving (Show, Generic)

data Import = Import
  { _module :: String
  , qualified :: Bool
  , alias :: Maybe String
  , specsList :: SpecsList
  }
  deriving (Show, Generic)

data TypeInfo = TypeInfo
  { pos :: ((Int, Int), (Int, Int))
  , name :: String
  , stringified :: String
  , constructors :: [String]
  }
  deriving (Show, Generic)

data ModuleT = ModuleT
  { name :: String
  , imports :: [Import]
  , types :: [TypeInfo]
  }
  deriving (Show, Generic)

data EntityDef = EntityDef
  { _module :: String
  , name :: String
  }
  deriving (Show, Generic, Eq, Hashable)

instance ToJSON EntityDef where
  toJSON EntityDef {..} = object ["module" .= _module, "name" .= name]

data Entity = Type EntityDef | Function EntityDef
  deriving (Show, Generic, Eq, Hashable)

name_ :: Lens' Entity String
name_ f (Type def) = (\ name' -> Type $ def { name = name' }) <$> f (def ^. #name)
name_ f (Function def) = (\ name' -> Function $ def { name = name' }) <$> f (def ^. #name)

module_ :: Lens' Entity String
module_ f (Type def) = (\ module' -> Type $ def { _module = module' }) <$> f (def ^. #_module)
module_ f (Function def) = (\ module' -> Function $ def { _module = module' }) <$> f (def ^. #_module)

type Map = HM.HashMap

type Payload = (Map String ModuleT, [Import], String)

data TypeDump = TypeDump
  { name :: String
  , srcLoc :: String
  , _module :: String
  , stringified :: String
  }
  deriving (Show, Generic, Eq)

instance ToJSON TypeDump where
  toJSON TypeDump {..} = object
    [ "name" .= name
    , "src_loc" .= srcLoc
    , "module" .= _module
    , "stringified_code" .= stringified
    ]
