module RPL.BuiltIn where

import RPL.Names
import RPL.Type
import RPL.Utils.Unique

typeInt :: TyCon
typeInt = MkTyCon (Id (uniqueFromInt 1) "Int") 0

typeChar :: TyCon
typeChar = MkTyCon (Id (uniqueFromInt 2) "Char") 0

typeMaybe :: TyCon
typeMaybe = MkTyCon (Id (uniqueFromInt 3) "Maybe") 1
