module RPL.Typecheck.GrTy 
  ( tcExpr, ConstrType(..), SolveOpts(..), defaultSolveOpts )
where

import RPL.Typecheck.GrTy.Types
import RPL.Typecheck.GrTy.Translate
import RPL.Typecheck.GrTy.Constraint
import RPL.Typecheck.GrTy.Syntactic
import RPL.Typecheck.GrTy.Solve

import qualified RPL.Syntax as Syn
import RPL.Type

tcExpr :: SolveOpts -> ConstrType -> Syn.Expr -> IO (Either String Type)
tcExpr opts ctype expr =
  runGTM $ do
    cstore <- translate ctype [] expr
    cstore' <- solve opts [] cstore
    let root_gen_node = cstore_root cstore'
    [root_type] <- nodeChildren root_gen_node
    expr_typ <- toType root_type
    return expr_typ
