module Parser.Raw

import Core.TT
import Core.RawContext
import TTImp.TTImp

import public Parser.Support
import public Text.Parser
import Data.List.Views

%default total

atom : Rule (RawImp ())
atom
    = do x <- constant
         pure (IPrimVal () x)
  <|> do keyword "Type"
         pure (IType ())
  <|> do symbol "_"
         pure (Implicit ())
  <|> do x <- name
         pure (IVar () x)

mutual
  bracketed : Rule (RawImp ())
  bracketed
      = do keyword "%pi"
           commit
           b <- binder
           scope <- expr
           pure (IPi () Explicit (fst b) (snd b) scope)
    <|> do keyword "%imppi"
           commit
           b <- binder
           scope <- expr
           pure (IPi () Implicit (fst b) (snd b) scope)
    <|> do keyword "%lam"
           commit
           b <- binder
           scope <- expr
           pure (ILam () (fst b) (snd b) scope)
    <|> do keyword "%let"
           commit
           symbol "("
           n <- name
           ty <- expr
           val <- expr
           symbol ")"
           scope <- expr
           pure (ILet () n ty val scope)
    <|> do f <- expr
           args <- some expr
           pure (apply f args)

  binder : Rule (Name, RawImp ())
  binder
      = do symbol "("
           n <- name
           t <- expr
           symbol ")"
           pure (n, t)

  export
  expr : Rule (RawImp ())
  expr
      = atom
    <|> do symbol "("
           e <- bracketed
           symbol ")"
           pure e

