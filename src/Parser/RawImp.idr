module Parser.RawImp

import Core.TT
import Core.RawContext
import TTImp.TTImp

import public Parser.Support
import public Text.Parser
import Data.List.Views

%default covering

-- Forward declare since they're used in the parser
topDecl : Int -> Rule (ImpDecl ())
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

column : EmptyRule Int
column
    = do (line, col) <- location
         pure col

-- Return whether we're at the end of a block entry, given the start column
-- of the block.
-- It's the end if we have a semicolon, or the next token starts in or before
-- startcol
atEnd : (startcol : Int) -> EmptyRule Bool
atEnd startcol
    = do symbol ";"
         pure True
  <|> do eof
         pure True
  <|> do col <- column
         pure (col <= startcol)

-- Fail if this is the end of a block entry or end of file
continueApp : (startcol : Int) -> EmptyRule ()
continueApp startcol
    = if !column > startcol
         then pure ()
         else fail "No more apps"

-- Parse an entry in a block - the parser for the entry takes the start 
-- column of the block
blockEntry : Int -> (Int -> Rule ty) -> Rule ty
blockEntry startcol rule
    = if !column < startcol
         then fail "End of block"
         else rule startcol

block : (Int -> Rule ty) -> EmptyRule (List ty)
block item
    = do symbol "{"
         commit
         ps <- many (blockEntry 0 item)
         symbol "}"
         pure ps
  <|> many (blockEntry !column item)
         
nonEmptyBlock : (Int -> Rule ty) -> Rule (List ty)
nonEmptyBlock item
    = do symbol "{"
         ps <- many (blockEntry 0 item)
         symbol "}"
         pure ps
  <|> some (blockEntry !column item)
         

mutual
  appExpr : Int -> Rule (RawImp ())
  appExpr startcol
      = do f <- simpleExpr startcol
           args <- many (argExpr startcol)
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

  argExpr : Int -> Rule (Either (RawImp ()) (Name, RawImp ()))
  argExpr startcol
      = do continueApp startcol
           arg <- simpleExpr startcol
           pure (Left arg)
    <|> do continueApp startcol
           arg <- implicitArg startcol
           pure (Right arg)

  implicitArg : Int -> Rule (Name, RawImp ())
  implicitArg startcol
      = do symbol "{"
           x <- unqualifiedName
           symbol "="
           commit
           tm <- expr startcol
           symbol "}"
           pure (UN x, tm)

  simpleExpr : Int -> Rule (RawImp ())
  simpleExpr startcol
      = do x <- unqualifiedName
           symbol "@"
           commit
           expr <- simpleExpr startcol
           pure (IAs () x expr)
    <|> atom 
    <|> binder startcol
    <|> do symbol ".("
           commit
           e <- expr startcol
           symbol ")"
           pure (IMustUnify () e)
    <|> do symbol "(|"
           commit
           alts <- sepBy1 (symbol ",") (expr startcol)
           symbol "|)"
           pure (IAlternative () True alts)
    <|> do symbol "("
           e <- expr startcol
           symbol ")"
           pure e

  explicitPi : Int -> Rule (RawImp ())
  explicitPi startcol
      = do symbol "("
           n <- name
           symbol ":"
           commit
           ty <- expr startcol
           symbol ")"
           symbol "->"
           scope <- typeExpr startcol
           pure (IPi () Explicit (Just n) ty scope)

  autoImplicitPi : Int -> Rule (RawImp ())
  autoImplicitPi startcol
      = do symbol "{"
           keyword "auto"
           commit
           n <- name
           symbol ":"
           ty <- expr startcol
           symbol "}"
           symbol "->"
           scope <- typeExpr startcol
           pure (IPi () AutoImplicit (Just n) ty scope)

  implicitPi : Int -> Rule (RawImp ())
  implicitPi startcol
      = do symbol "{"
           n <- name
           symbol ":"
           commit
           ty <- expr startcol
           symbol "}"
           symbol "->"
           scope <- typeExpr startcol
           pure (IPi () Implicit (Just n) ty scope)

  lam : Int -> Rule (RawImp ())
  lam startcol
      = do symbol "\\"
           n <- name
           ty <- option 
                    (Implicit ())
                    (do symbol ":"
                        expr startcol)
           symbol "=>"
           scope <- typeExpr startcol
           pure (ILam () Explicit n ty scope)

  let_ : Int -> Rule (RawImp ())
  let_ startcol
      = do keyword "let"
           n <- name
           commit
           ty <- option 
                    (Implicit ())
                    (do symbol ":"
                        expr startcol)
           symbol "="
           val <- expr startcol
           keyword "in"
           scope <- typeExpr startcol
           pure (ILet () n ty val scope)
    <|> do keyword "let"
           ds <- block topDecl
           keyword "in"
           scope <- typeExpr startcol
           pure (ILocal () (collectDefs ds) scope)
  
  case_ : Int -> Rule (RawImp ())
  case_ startcol
      = do keyword "case"
           scr <- expr startcol
           keyword "of"
           alts <- block caseAlt
           pure (ICase () scr alts)

  caseAlt : Int -> Rule (ImpClause ())
  caseAlt startcol
      = do lhs <- expr startcol
           caseRHS startcol lhs
          
  caseRHS : Int -> RawImp () -> Rule (ImpClause ())
  caseRHS startcol lhs
      = do symbol "=>"
           rhs <- expr (startcol + 1)
           atEnd startcol 
           pure (PatClause () (mkLCPatVars lhs) rhs)
    <|> do keyword "impossible"
           atEnd startcol
           pure (ImpossibleClause () (mkLCPatVars lhs))

  binder : Int -> Rule (RawImp ())
  binder startcol
      = autoImplicitPi startcol
    <|> implicitPi startcol
    <|> explicitPi startcol
    <|> lam startcol
    <|> let_ startcol
    <|> case_ startcol

  typeExpr : Int -> Rule (RawImp ())
  typeExpr startcol
      = do arg <- appExpr startcol
           (do symbol "->"
               rest <- sepBy (symbol "->") (appExpr startcol)
               pure (mkPi arg rest))
             <|> pure arg
    where
      mkPi : RawImp () -> List (RawImp ()) -> RawImp ()
      mkPi arg [] = arg
      mkPi arg (a :: as) = IPi () Explicit Nothing arg (mkPi a as)

  export
  expr : Int -> Rule (RawImp ())
  expr = typeExpr

tyDecl : Int -> Rule (ImpTy ())
tyDecl startcol
    = do n <- name
         symbol ":"
         ty <- expr startcol
         atEnd startcol
         pure (MkImpTy () n ty)

parseRHS : Int -> (lhs : RawImp ()) -> Rule (Name, ImpClause ())
parseRHS startcol lhs
     = do symbol "="
          commit
          rhs <- expr (startcol + 1)
          atEnd startcol
          fn <- getFn lhs
          -- Turn lower case names on lhs into IBindVar pattern variables
          -- before returning
          pure (fn, PatClause () (mkLCPatVars lhs) rhs)
   <|> do keyword "impossible"
          atEnd startcol
          fn <- getFn lhs
          pure (fn, ImpossibleClause () (mkLCPatVars lhs))
  where
    getFn : RawImp annot -> EmptyRule Name
    getFn (IVar _ n) = pure n
    getFn (IApp _ f a) = getFn f
    getFn (IImplicitApp _ f _ a) = getFn f
    getFn _ = fail "Not a function application" 


clause : Int -> Rule (Name, ImpClause ())
clause startcol
    = do lhs <- expr startcol
         parseRHS startcol lhs

dataDecl : Int -> Rule (ImpData ())
dataDecl startcol
    = do keyword "data"
         n <- name
         symbol ":"
         ty <- expr startcol
         keyword "where"
         cs <- block tyDecl 
         pure (MkImpData () n ty cs)

implicitsDecl : Int -> Rule (List (String, RawImp ()))
implicitsDecl startcol
    = do keyword "implicit"
         commit
         ns <- sepBy1 (symbol ",") impDecl
         atEnd startcol
         pure ns
  where
    impDecl : Rule (String, RawImp ())
    impDecl 
        = do x <- unqualifiedName
             ty <- option (Implicit ())
                          (do symbol ":"
                              expr startcol)
             pure (x, ty)

namespaceDecl : Int -> Rule (List String)
namespaceDecl startcol
    = do keyword "namespace"
         commit
         ns <- namespace_
         atEnd startcol
         pure ns

directive : Int -> Rule (ImpDecl ())
directive startcol
    = do exactIdent "logging"
         lvl <- intLit
         atEnd startcol
         pure (ILog (cast lvl))
  <|> do exactIdent "hint"
         h <- name
         ty <- option Nothing
                      (do n <- name
                          pure (Just n))
         atEnd startcol
         pure (IHint () h ty)

-- Declared at the top
-- topDecl : Rule (ImpDecl ())
topDecl startcol
    = do dat <- dataDecl startcol
         pure (IData () dat)
  <|> do ns <- namespaceDecl startcol
         pure (INamespace () ns)
  <|> do ns <- implicitsDecl startcol
         pure (ImplicitNames () ns)
  <|> do symbol "%"; commit
         directive startcol
  <|> do claim <- tyDecl startcol
         pure (IClaim () claim)
  <|> do nd <- clause startcol
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
