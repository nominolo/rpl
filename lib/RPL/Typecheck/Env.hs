{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module RPL.Typecheck.Env where

import RPL.Type
import RPL.Names
import RPL.BuiltIn ( initialTypeEnv )
import RPL.Error
import RPL.Typecheck.Subst
import RPL.Typecheck.Utils ( fromUserType )
import qualified RPL.Syntax as Syn
import RPL.Utils.Monads
import RPL.Utils.Pretty

import Control.Monad.Error
import qualified Data.Set as S

data GlobalEnv = GlobalEnv
  { gblTypeEnv :: {-# UNPACK #-} !TypeEnv
  , gblNameEnv :: {-# UNPACK #-} !NameEnv }

type TypeEnv = Env Id TyCon
type NameEnv = Env Id TypeScheme

emptyGlobalEnv :: GlobalEnv
emptyGlobalEnv = GlobalEnv initialTypeEnv emptyEnv

extendNameEnv :: GlobalEnv -> Id -> TypeScheme -> GlobalEnv
extendNameEnv env x ts =
  env { gblNameEnv = extendEnv (gblNameEnv env) x ts }

lookupNameEnv :: GlobalEnv -> Id -> Maybe TypeScheme
lookupNameEnv env x = lookupEnv (gblNameEnv env) x

-- newtype CheckM a = CheckM (ErrorT SourceError IO a)
--   deriving (Functor, Applicative, Monad, MonadError SourceError)

checkDecls :: (Applicative m, MonadError SourceError m) => 
              [Syn.Decl] -> m GlobalEnv
checkDecls = foldM checkDecl emptyGlobalEnv

checkDecl :: (Applicative m, MonadError SourceError m) =>
             GlobalEnv -> Syn.Decl -> m GlobalEnv
checkDecl env (Syn.DataDecl _ tycon_name vars datacons) = do
  let tyvars = map mkTyVar vars
  let tycon = MkTyCon { tyConName = tycon_name
                      , tyConArity = length tyvars }
  let env' = env { gblTypeEnv = extendEnv (gblTypeEnv env) tycon_name tycon }
  foldM (checkDataConDecl tycon tyvars) env' datacons

checkDataConDecl :: (Applicative m, MonadError SourceError m) =>
                    TyCon -> [TyVar] -> GlobalEnv -> Syn.DataConDecl
                 -> m GlobalEnv
checkDataConDecl tycon qvars env (Syn.DataConDecl loc data_con user_ty) = do
  ForAll user_qvars ctrts ty <- fromUserType (gblTypeEnv env) user_ty
  let unqual = tsFTV (ForAll (qvars ++ user_qvars) ctrts ty)
  -- Result must be of the form "C a_1 .. a_n" where "a_i" are
  -- quantified at the top-level and "n" is 
  let (c:args) = viewApp $ last $ viewFun ty

  check_result_tycon c
  check_result_tyargs args

  let ty_scheme = ForAll (qvars ++ user_qvars ++ S.toList unqual) ctrts ty

  return $ env { gblNameEnv = extendEnv (gblNameEnv env) data_con ty_scheme }

 where
   check_result_tycon (TyCon tc)
     | tc == tycon = return ()
     | otherwise =
         throwMsg loc $ DeclError $
           fsep (textWords "Result type of constructor" ++
                 [char '`' <> colour1 (ppr data_con) <> char '\''] ++
                 textWords "does not match declared type.") $+$
           nest 4 (text "Declared type:" <+> ppr tycon) $+$
           nest 4 (text "Result type:  " <+> ppr tc)
   check_result_tycon bad =
     throwMsg loc $ DeclError $
       wrappingText "Result type of data constructor does not match declared type." $+$
       nest 4 (text "Expected:" <+> withDebugStyle (ppr (tyConApp tycon (map TyVar qvars))) $+$
               text "Got:     " <+> withDebugStyle (ppr bad))

   check_result_tyargs args
     | all is_tyvar args = return ()
     | otherwise = throwMsg loc $ DeclError $
        wrappingText ("Result type of data constructor is applied " ++
                      "to non-variable arguments. " ++ 
                      "(GADTs are not currently supported.)") $+$
        nest 4 (text "Expected:" <+> ppr (tyConApp tycon (map TyVar qvars)) $+$
                text "Got:     " <+> ppr (tyConApp tycon args))
   
   is_tyvar (TyVar _) = True
   is_tyvar _ = False 
{-
  let 
  case c of
    TyCon tc | tc == tycon -> return ()
  case () of
    _ | TyCon tc <- c, tc == tycon, all is_tyvar args -> do
      let ty_scheme = ForAll (qvars ++ unqual ++ user_qvars) ctrts ty
      return $ extendEnv env data_con 
  return env
-}