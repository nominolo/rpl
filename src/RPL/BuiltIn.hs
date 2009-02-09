module RPL.BuiltIn where

import RPL.Names
import RPL.Type
import RPL.Utils.Unique

typeInt :: Type
typeInt = TyCon (Id (uniqueFromInt 1) "Int") 0

typeChar :: Type
typeChar = TyCon (Id (uniqueFromInt 2) "Char") 0

typeMaybe :: Type
typeMaybe = TyCon (Id (uniqueFromInt 3) "Maybe") 1
