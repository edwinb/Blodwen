module Parser.RawImp

import Core.TT
import Core.Context
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
export
collectDefs : List (ImpDecl annot) -> List (ImpDecl annot)

expandInt : RawImp () -> RawImp ()
expandInt (IPrimVal () (BI x)) 
    = IAlternative () (UniqueDefault (IPrimVal () (BI x)))
                             [IPrimVal () (BI x),
                              IPrimVal () (I (fromInteger x))]
expandInt x = x

atom : Rule (RawImp ())
atom
    = do x <- constant
         pure (expandInt (IPrimVal () x))
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
         exactIdent "MkWorld"
         pure (IPrimVal () WorldVal)
  <|> do symbol "%"
         exactIdent "World"
         pure (IPrimVal () WorldType)
  <|> do symbol "%"
         exactIdent "search"
         pure (ISearch () 1000)
  <|> do x <- name
         pure (IVar () x)

mutual
  appExpr : IndentInfo -> Rule (RawImp ())
  appExpr indents
      = case_ indents
    <|> do f <- simpleExpr indents
           args <- many (argExpr indents)
           pure (applyExpImp f args)
    where
      applyExpImp : RawImp () -> 
                    List (Either (RawImp ()) (Maybe Name, RawImp ())) -> 
                    RawImp ()
      applyExpImp f [] = f
      applyExpImp f (Left exp :: args)
          = applyExpImp (IApp () f exp) args
      applyExpImp f (Right (n, imp) :: args) 
          = applyExpImp (IImplicitApp () f n imp) args

  argExpr : IndentInfo -> Rule (Either (RawImp ()) (Maybe Name, RawImp ()))
  argExpr indents
      = do continue indents
           arg <- simpleExpr indents
           pure (Left arg)
    <|> do continue indents
           arg <- implicitArg indents
           pure (Right arg)

  implicitArg : IndentInfo -> Rule (Maybe Name, RawImp ())
  implicitArg indents
      = do symbol "{"
           x <- unqualifiedName
           symbol "="
           commit
           tm <- expr indents
           symbol "}"
           pure (Just (UN x), tm)
    <|> do symbol "@{"
           commit
           tm <- expr indents
           symbol "}"
           pure (Nothing, tm)

  simpleExpr : IndentInfo -> Rule (RawImp ())
  simpleExpr indents
      = do x <- unqualifiedName
           symbol "@"
           commit
           expr <- simpleExpr indents
           pure (IAs () (UN x) expr)
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
           pure (IAlternative () FirstSuccess alts)
    <|> do symbol "("
           e <- expr indents
           symbol ")"
           pure e

  getMult : Constant -> EmptyRule RigCount
  getMult (BI 0) = pure Rig0
  getMult (BI 1) = pure Rig1
  getMult _ = fail "Invalid multiplicity"

  multiplicity : EmptyRule RigCount
  multiplicity
      = do c <- constant
           getMult c
    <|> pure RigW

  explicitPi : IndentInfo -> Rule (RawImp ())
  explicitPi indents
      = do symbol "("
           rig <- multiplicity
           n <- name
           symbol ":"
           commit
           ty <- expr indents
           symbol ")"
           symbol "->"
           scope <- typeExpr indents
           pure (IPi () rig Explicit (Just n) ty scope)

  autoImplicitPi : IndentInfo -> Rule (RawImp ())
  autoImplicitPi indents
      = do symbol "{"
           keyword "auto"
           commit
           rig <- multiplicity
           n <- name
           symbol ":"
           ty <- expr indents
           symbol "}"
           symbol "->"
           scope <- typeExpr indents
           pure (IPi () rig AutoImplicit (Just n) ty scope)

  implicitPi : IndentInfo -> Rule (RawImp ())
  implicitPi indents
      = do symbol "{"
           rig <- multiplicity
           n <- name
           symbol ":"
           commit
           ty <- expr indents
           symbol "}"
           symbol "->"
           scope <- typeExpr indents
           pure (IPi () rig Implicit (Just n) ty scope)

  lam : IndentInfo -> Rule (RawImp ())
  lam indents
      = do symbol "\\"
           rig <- multiplicity
           n <- name
           ty <- option 
                    (Implicit ())
                    (do symbol ":"
                        expr indents)
           symbol "=>"
           continue indents
           scope <- typeExpr indents
           pure (ILam () rig Explicit (Just n) ty scope)

  let_ : IndentInfo -> Rule (RawImp ())
  let_ indents
      = do keyword "let"
           rig <- multiplicity
           n <- name
           symbol "="
           commit
           val <- expr indents
           continue indents
           keyword "in"
           scope <- typeExpr indents
           pure (ILet () rig n (Implicit ()) val scope)
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
           pure (ICase () scr (Implicit ()) alts)

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
      mkPi arg (a :: as) = IPi () RigW Explicit Nothing arg (mkPi a as)

  export
  expr : IndentInfo -> Rule (RawImp ())
  expr = typeExpr 

visibility : EmptyRule Visibility
visibility
    = do keyword "public"
         keyword "export"
         pure Public
  <|> do keyword "export"
         pure Export
  <|> do keyword "private"
         pure Private
  <|> pure Private

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
         pure (MkImpData () n ty [] cs)

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

namespaceDecl : Rule (List String)
namespaceDecl
    = do keyword "namespace"
         commit
         ns <- namespace_
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
    = do vis <- visibility
         dat <- dataDecl indents
         pure (IData () vis dat)
  <|> do ns <- namespaceDecl
         ds <- assert_total (nonEmptyBlock topDecl)
         pure (INamespace () ns ds)
  <|> do ns <- implicitsDecl indents
         pure (ImplicitNames () ns)
  <|> do symbol "%"; commit
         directive indents
  <|> do vis <- visibility
         claim <- tyDecl indents
         pure (IClaim () vis [] claim)
  <|> do nd <- clause indents
         pure (IDef () (fst nd) [snd nd])

-- All the clauses get parsed as one-clause definitions. Collect any
-- neighbouring clauses with the same function name into one definition.
-- Declared at the top.
-- collectDefs : List (ImpDecl ()) -> List (ImpDecl ())
collectDefs [] = []
collectDefs (IDef loc fn cs :: ds)
    = let (cs', rest) = spanMap (isClause fn) ds in
          IDef loc fn (cs ++ cs') :: assert_total (collectDefs rest)
  where
    spanMap : (a -> Maybe (List b)) -> List a -> (List b, List a)
    spanMap f [] = ([], [])
    spanMap f (x :: xs) = case f x of
                               Nothing => ([], x :: xs)
                               Just y => case spanMap f xs of
                                              (ys, zs) => (y ++ ys, zs)

    isClause : Name -> ImpDecl annot -> Maybe (List (ImpClause annot))
    isClause n (IDef _ n' cs) 
        = if n == n' then Just cs else Nothing
    isClause n _ = Nothing
collectDefs (INamespace annot ns nds :: ds)
    = INamespace annot ns (collectDefs nds) :: collectDefs ds
collectDefs (d :: ds)
    = d :: collectDefs ds

export
prog : Rule (List (ImpDecl ()))
prog 
    = do ds <- nonEmptyBlock topDecl
         pure (collectDefs ds)

