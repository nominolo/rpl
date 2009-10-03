module RPL.BuiltIn where

import RPL.Names
import RPL.Type
import RPL.Utils.Unique
import RPL.Typecheck.Subst

import Data.List ( foldl' )

typeInt :: TyCon
typeInt = MkTyCon (Id (uniqueFromInt 0) "Int") 0

typeChar :: TyCon
typeChar = MkTyCon (Id (uniqueFromInt 0) "Char") 0

initialTypeEnv :: Env Id TyCon
initialTypeEnv =
  foldl' (\e -> uncurry (extendEnv e)) emptyEnv
    [ (tyConName tc, tc) | tc <- [ typeInt, typeChar ] ]

typeMaybe :: TyCon
typeMaybe = MkTyCon (Id (uniqueFromInt 0) "Maybe") 1

