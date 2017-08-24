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
  <|> do symbol "$"
         x <- unqualifiedName
         pure (IBindVar () x)
  <|> do x <- name
         pure (IVar () x)

mutual
  appExpr : Rule (RawImp ())
  appExpr
      = do f <- simpleExpr
           args <- many simpleExpr
           pure (apply f args)

  simpleExpr : Rule (RawImp ())
  simpleExpr
      = atom
    <|> binder
    <|> do symbol "("
           e <- expr
           symbol ")"
           pure e

  explicitPi : Rule (RawImp ())
  explicitPi
      = do symbol "("
           n <- name
           symbol ":"
           commit
           ty <- expr
           symbol ")"
           symbol "->"
           scope <- typeExpr
           pure (IPi () Explicit (Just n) ty scope)

  implicitPi : Rule (RawImp ())
  implicitPi
      = do symbol "{"
           n <- name
           symbol ":"
           commit
           ty <- expr
           symbol "}"
           symbol "->"
           scope <- typeExpr
           pure (IPi () Implicit (Just n) ty scope)

  lam : Rule (RawImp ())
  lam
      = do symbol "\\"
           n <- name
           ty <- optional 
                    (do symbol ":"
                        expr)
                    (Implicit ())
           symbol "=>"
           scope <- typeExpr
           pure (ILam () n ty scope)

  let_ : Rule (RawImp ())
  let_
      = do keyword "let"
           n <- name
           ty <- optional 
                    (do symbol ":"
                        expr)
                    (Implicit ())
           symbol "="
           val <- expr
           keyword "in"
           scope <- typeExpr
           pure (ILet () n ty val scope)

  binder : Rule (RawImp ())
  binder
      = implicitPi
    <|> explicitPi
    <|> lam
    <|> let_

  typeExpr : Rule (RawImp ())
  typeExpr
      = do arg <- appExpr
           (do symbol "->"
               rest <- sepBy (symbol "->") appExpr
               pure (mkPi arg rest))
             <|> pure arg
    where
      mkPi : RawImp () -> List (RawImp ()) -> RawImp ()
      mkPi arg [] = arg
      mkPi arg (a :: as) = IPi () Explicit Nothing arg (mkPi a as)

  export
  expr : Rule (RawImp ())
  expr = typeExpr

