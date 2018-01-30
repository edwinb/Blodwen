module Parser.RawImp

import Core.TT
import Core.RawContext
import TTImp.TTImp

import public Parser.Support
import public Text.Parser
import Parser.Lexer
import Data.List.Views

import Debug.Trace

%default covering

-- Forward declare since they're used in the parser
topDecl : IndentInfo -> Rule (ImpDecl ())
collectDefs : List (ImpDecl ()) -> List (ImpDecl ())

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
  <|> do symbol "?"
         x <- unqualifiedName
         pure (IHole () x)
  <|> do symbol "%"
         exactIdent "search"
         pure (ISearch () 1000)
  <|> do x <- name
         pure (IVar () x)

mutual
  appExpr : IndentInfo -> Rule (RawImp ())
  appExpr indents
      = do f <- simpleExpr indents
           args <- many (argExpr indents)
           pure (applyExpImp f args)
    where
      applyExpImp : RawImp () -> 
                    List (Either (RawImp ()) (Name, RawImp ())) -> 
                    RawImp ()
      applyExpImp f [] = f
      applyExpImp f (Left exp :: args)
          = applyExpImp (IApp () f exp) args
      applyExpImp f (Right (n, imp) :: args) 
          = applyExpImp (IImplicitApp () f n imp) args

  argExpr : IndentInfo -> Rule (Either (RawImp ()) (Name, RawImp ()))
  argExpr indents
      = do continue indents
           arg <- simpleExpr indents
           pure (Left arg)
    <|> do continue indents
           arg <- implicitArg indents
           pure (Right arg)

  implicitArg : IndentInfo -> Rule (Name, RawImp ())
  implicitArg indents
      = do symbol "{"
           x <- unqualifiedName
           symbol "="
           commit
           tm <- expr indents
           symbol "}"
           pure (UN x, tm)

  simpleExpr : IndentInfo -> Rule (RawImp ())
  simpleExpr indents
      = do x <- unqualifiedName
           symbol "@"
           commit
           expr <- simpleExpr indents
           pure (IAs () x expr)
    <|> atom 
    <|> binder indents
    <|> do symbol ".("
           commit
           e <- expr indents
           symbol ")"
           pure (IMustUnify () e)
    <|> do symbol "(|"
           commit
           alts <- sepBy1 (symbol ",") (expr indents)
           symbol "|)"
           pure (IAlternative () True alts)
    <|> do symbol "("
           e <- expr indents
           symbol ")"
           pure e

  explicitPi : IndentInfo -> Rule (RawImp ())
  explicitPi indents
      = do symbol "("
           n <- name
           symbol ":"
           commit
           ty <- expr indents
           symbol ")"
           symbol "->"
           scope <- typeExpr indents
           pure (IPi () Explicit (Just n) ty scope)

  autoImplicitPi : IndentInfo -> Rule (RawImp ())
  autoImplicitPi indents
      = do symbol "{"
           keyword "auto"
           commit
           n <- name
           symbol ":"
           ty <- expr indents
           symbol "}"
           symbol "->"
           scope <- typeExpr indents
           pure (IPi () AutoImplicit (Just n) ty scope)

  implicitPi : IndentInfo -> Rule (RawImp ())
  implicitPi indents
      = do symbol "{"
           n <- name
           symbol ":"
           commit
           ty <- expr indents
           symbol "}"
           symbol "->"
           scope <- typeExpr indents
           pure (IPi () Implicit (Just n) ty scope)

  lam : IndentInfo -> Rule (RawImp ())
  lam indents
      = do symbol "\\"
           n <- name
           ty <- option 
                    (Implicit ())
                    (do symbol ":"
                        expr indents)
           symbol "=>"
           continue indents
           scope <- typeExpr indents
           pure (ILam () Explicit n ty scope)

  let_ : IndentInfo -> Rule (RawImp ())
  let_ indents
      = do keyword "let"
           n <- name
           symbol "="
           commit
           val <- expr indents
           continue indents
           keyword "in"
           scope <- typeExpr indents
           pure (ILet () n (Implicit ()) val scope)
    <|> do keyword "let"
           ds <- block topDecl
           continue indents
           keyword "in"
           scope <- typeExpr indents
           pure (ILocal () (collectDefs ds) scope)

  case_ : IndentInfo -> Rule (RawImp ())
  case_ indents
      = do keyword "case"
           scr <- expr indents
           keyword "of"
           alts <- block caseAlt
           pure (ICase () scr alts)

  caseAlt : IndentInfo -> Rule (ImpClause ())
  caseAlt indents
      = do lhs <- expr indents
           caseRHS indents lhs
          
  caseRHS : IndentInfo -> RawImp () -> Rule (ImpClause ())
  caseRHS indents lhs
      = do symbol "=>"
           continue indents
           rhs <- expr indents
           atEnd indents 
           pure (PatClause () (mkLCPatVars lhs) rhs)
    <|> do keyword "impossible"
           atEnd indents
           pure (ImpossibleClause () (mkLCPatVars lhs))

  binder : IndentInfo -> Rule (RawImp ())
  binder indents
      = autoImplicitPi indents
    <|> implicitPi indents
    <|> explicitPi indents
    <|> lam indents
    <|> let_ indents
    <|> case_ indents

  typeExpr : IndentInfo -> Rule (RawImp ())
  typeExpr indents
      = do arg <- appExpr indents
           (do symbol "->"
               rest <- sepBy (symbol "->") (appExpr indents)
               pure (mkPi arg rest))
             <|> pure arg
    where
      mkPi : RawImp () -> List (RawImp ()) -> RawImp ()
      mkPi arg [] = arg
      mkPi arg (a :: as) = IPi () Explicit Nothing arg (mkPi a as)

  export
  expr : IndentInfo -> Rule (RawImp ())
  expr = typeExpr

tyDecl : IndentInfo -> Rule (ImpTy ())
tyDecl indents
    = do n <- name
         symbol ":"
         ty <- expr indents
         atEnd indents
         pure (MkImpTy () n ty)

parseRHS : IndentInfo -> (lhs : RawImp ()) -> Rule (Name, ImpClause ())
parseRHS indents lhs
     = do symbol "="
          commit
          rhs <- expr indents
          atEnd indents
          fn <- getFn lhs
          -- Turn lower case names on lhs into IBindVar pattern variables
          -- before returning
          pure (fn, PatClause () (mkLCPatVars lhs) rhs)
   <|> do keyword "impossible"
          atEnd indents
          fn <- getFn lhs
          pure (fn, ImpossibleClause () (mkLCPatVars lhs))
  where
    getFn : RawImp annot -> EmptyRule Name
    getFn (IVar _ n) = pure n
    getFn (IApp _ f a) = getFn f
    getFn (IImplicitApp _ f _ a) = getFn f
    getFn _ = fail "Not a function application" 


clause : IndentInfo -> Rule (Name, ImpClause ())
clause indents
    = do lhs <- expr indents
         parseRHS indents lhs

dataDecl : IndentInfo -> Rule (ImpData ())
dataDecl indents
    = do keyword "data"
         n <- name
         symbol ":"
         ty <- expr indents
         keyword "where"
         cs <- block tyDecl 
         pure (MkImpData () n ty cs)

implicitsDecl : IndentInfo -> Rule (List (String, RawImp ()))
implicitsDecl indents
    = do keyword "implicit"
         commit
         ns <- sepBy1 (symbol ",") impDecl
         atEnd indents
         pure ns
  where
    impDecl : Rule (String, RawImp ())
    impDecl 
        = do x <- unqualifiedName
             ty <- option (Implicit ())
                          (do symbol ":"
                              expr indents)
             pure (x, ty)

namespaceDecl : IndentInfo -> Rule (List String)
namespaceDecl indents
    = do keyword "namespace"
         commit
         ns <- namespace_
         atEnd indents
         pure ns

directive : IndentInfo -> Rule (ImpDecl ())
directive indents
    = do exactIdent "logging"
         lvl <- intLit
         atEnd indents
         pure (ILog (cast lvl))
  <|> do exactIdent "hint"
         h <- name
         ty <- option Nothing
                      (do n <- name
                          pure (Just n))
         atEnd indents
         pure (IHint () h ty)

-- Declared at the top
-- topDecl : Rule (ImpDecl ())
topDecl indents
    = do dat <- dataDecl indents
         pure (IData () dat)
  <|> do ns <- namespaceDecl indents
         ds <- assert_total (nonEmptyBlock topDecl)
         pure (INamespace () ns ds)
  <|> do ns <- implicitsDecl indents
         pure (ImplicitNames () ns)
  <|> do symbol "%"; commit
         directive indents
  <|> do claim <- tyDecl indents
         pure (IClaim () claim)
  <|> do nd <- clause indents
         pure (IDef () (fst nd) [snd nd])

-- All the clauses get parsed as one-clause definitions. Collect any
-- neighbouring clauses with the same function name into one definition.
-- Declared at the top.
-- collectDefs : List (ImpDecl ()) -> List (ImpDecl ())
collectDefs [] = []
collectDefs (IDef annot fn cs :: ds)
    = let (cs', rest) = spanMap (isClause fn) ds in
          IDef annot fn (cs ++ cs') :: assert_total (collectDefs rest)
  where
    spanMap : (a -> Maybe (List b)) -> List a -> (List b, List a)
    spanMap f [] = ([], [])
    spanMap f (x :: xs) = case f x of
                               Nothing => ([], x :: xs)
                               Just y => case spanMap f xs of
                                              (ys, zs) => (y ++ ys, zs)

    isClause : Name -> ImpDecl () -> Maybe (List (ImpClause ()))
    isClause n (IDef annot n' cs) 
        = if n == n' then Just cs else Nothing
    isClause n _ = Nothing
collectDefs (d :: ds)
    = d :: collectDefs ds

export
prog : Rule (List (ImpDecl ()))
prog 
    = do ds <- nonEmptyBlock topDecl
         pure (collectDefs ds)

