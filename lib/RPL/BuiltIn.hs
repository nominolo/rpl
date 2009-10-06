module RPL.BuiltIn where

import RPL.Names
import RPL.Type
import RPL.Utils.Unique
import RPL.Typecheck.Subst

import Data.List ( foldl' )

intTyCon :: TyCon
intTyCon = MkTyCon (Id (uniqueFromInt 0) "Int") 0

charTyCon :: TyCon
charTyCon = MkTyCon (Id (uniqueFromInt 0) "Char") 0

maybeTyCon :: TyCon
maybeTyCon = MkTyCon (Id (uniqueFromInt 0) "Maybe") 1


typeInt :: Type
typeInt = TyCon intTyCon

typeChar :: Type
typeChar = TyCon charTyCon

initialTypeEnv :: Env Id TyCon
initialTypeEnv =
  foldl' (\e -> uncurry (extendEnv e)) emptyEnv
    [ (tyConName tc, tc) | tc <- [ intTyCon, charTyCon ] ]

typeMaybe :: Type
typeMaybe = TyCon maybeTyCon
