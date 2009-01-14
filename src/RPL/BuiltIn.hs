module RPL.BuiltIn where

import RPL.Names
import RPL.Type
import RPL.Utils.Unique

typeInt :: Type
typeInt = TyCon (Id (uniqueFromInt 1) "Int") []

typeChar :: Type
typeChar = TyCon (Id (uniqueFromInt 2) "Char") []
