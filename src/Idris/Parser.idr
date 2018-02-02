module Idris.Parser

import public Parser.Support
import Parser.Lexer
import Idris.Syntax

import public Text.Parser
import Data.List.Views

%default covering

-- Forward declare since they're used in the parser
topDecl : FileName -> IndentInfo -> Rule (List PDecl)
collectDefs : List PDecl -> List PDecl

atom : FileName -> Rule PTerm
atom fname
    = do start <- location
         x <- constant
         end <- location
         pure (PPrimVal (MkFC fname start end) x)
  <|> do start <- location
         keyword "Type"
         end <- location
         pure (PType (MkFC fname start end))
  <|> do start <- location
         symbol "_"
         end <- location
         pure (PImplicit (MkFC fname start end))
  <|> do start <- location
         symbol "?"
         x <- unqualifiedName
         end <- location
         pure (PHole (MkFC fname start end) x)
  <|> do start <- location
         symbol "%"
         exactIdent "search"
         end <- location
         pure (PSearch (MkFC fname start end) 1000)
  <|> do start <- location
         x <- name
         end <- location
         pure (PRef (MkFC fname start end) x)

mutual
  appExpr : FileName -> IndentInfo -> Rule PTerm
  appExpr fname indents
      = do start <- location
           f <- simpleExpr fname indents
           args <- many (argExpr fname indents)
           end <- location
           pure (applyExpImp start end f args)
    <|> do start <- location
           op <- operator
           arg <- expr fname indents
           end <- location
           pure (PPrefixOp (MkFC fname start end) op arg)
    where
      applyExpImp : FilePos -> FilePos -> PTerm -> 
                    List (Either PTerm (Name, PTerm)) -> 
                    PTerm
      applyExpImp start end f [] = f
      applyExpImp start end f (Left exp :: args)
          = applyExpImp start end (PApp (MkFC fname start end) f exp) args
      applyExpImp start end f (Right (n, imp) :: args) 
          = applyExpImp start end (PImplicitApp (MkFC fname start end) f n imp) args

  argExpr : FileName -> IndentInfo -> 
            Rule (Either PTerm (Name, PTerm))
  argExpr fname indents
      = do continue indents
           arg <- simpleExpr fname indents
           pure (Left arg)
    <|> do continue indents
           arg <- implicitArg fname indents
           pure (Right arg)

  implicitArg : FileName -> IndentInfo -> Rule (Name, PTerm)
  implicitArg fname indents
      = do symbol "{"
           x <- unqualifiedName
           symbol "="
           commit
           tm <- expr fname indents
           symbol "}"
           pure (UN x, tm)

  opExpr : FileName -> IndentInfo -> Rule PTerm
  opExpr fname indents
      = do start <- location
           l <- appExpr fname indents
           (do continue indents
               op <- operator
               r <- opExpr fname indents
               end <- location
               pure (POp (MkFC fname start end) op l r))
             <|> pure l

  bracketedExpr : FileName -> FilePos -> IndentInfo -> Rule PTerm
  bracketedExpr fname start indents
      -- left section. This may also be a prefix operator, but we'll sort
      -- that out when desugaring: if the operator is infix, treat it as a
      -- section otherwise treat it as prefix
      = do op <- operator
           e <- expr fname indents
           symbol ")"
           end <- location
           pure (PSectionL (MkFC fname start end) op e)
      -- bracketed expression or right section
    <|> do e <- expr fname indents
           (do op <- operator
               symbol ")"
               end <- location
               pure (PSectionR (MkFC fname start end) e op)
             <|>
            do symbol ")"
               end <- location
               pure (PBracketed (MkFC fname start end) e))

  simpleExpr : FileName -> IndentInfo -> Rule PTerm
  simpleExpr fname indents
      = do start <- location
           x <- unqualifiedName
           symbol "@"
           commit
           expr <- simpleExpr fname indents
           end <- location
           pure (PAs (MkFC fname start end) x expr)
    <|> atom fname
    <|> binder fname indents
    <|> do start <- location
           symbol ".("
           commit
           e <- expr fname indents
           symbol ")"
           end <- location
           pure (PDotted (MkFC fname start end) e)
    <|> do start <- location
           symbol "("
           bracketedExpr fname start indents

  explicitPi : FileName -> IndentInfo -> Rule PTerm
  explicitPi fname indents
      = do start <- location
           symbol "("
           n <- name
           symbol ":"
           commit
           ty <- expr fname indents
           symbol ")"
           symbol "->"
           scope <- typeExpr fname indents
           end <- location
           pure (PPi (MkFC fname start end) RigW Explicit (Just n) ty scope)

  autoImplicitPi : FileName -> IndentInfo -> Rule PTerm
  autoImplicitPi fname indents
      = do start <- location
           symbol "{"
           keyword "auto"
           commit
           n <- name
           symbol ":"
           ty <- expr fname indents
           symbol "}"
           symbol "->"
           scope <- typeExpr fname indents
           end <- location
           pure (PPi (MkFC fname start end) RigW AutoImplicit (Just n) ty scope)

  implicitPi : FileName -> IndentInfo -> Rule PTerm
  implicitPi fname indents
      = do start <- location
           symbol "{"
           n <- name
           symbol ":"
           commit
           ty <- expr fname indents
           symbol "}"
           symbol "->"
           scope <- typeExpr fname indents
           end <- location
           pure (PPi (MkFC fname start end) RigW Implicit (Just n) ty scope)

  lam : FileName -> IndentInfo -> Rule PTerm
  lam fname indents
      = do start <- location
           symbol "\\"
           n <- name
           ty <- option 
                    (PImplicit (MkFC fname start start))
                    (do symbol ":"
                        expr fname indents)
           symbol "=>"
           continue indents
           scope <- typeExpr fname indents
           end <- location
           pure (PLam (MkFC fname start end) RigW Explicit n ty scope)

  let_ : FileName -> IndentInfo -> Rule PTerm
  let_ fname indents
      = do start <- location
           keyword "let"
           n <- name
           symbol "="
           commit
           val <- expr fname indents
           continue indents
           keyword "in"
           scope <- typeExpr fname indents
           end <- location
           pure (PLet (MkFC fname start end) RigW n (PImplicit (MkFC fname start end)) val scope)
    <|> do start <- location
           keyword "let"
           ds <- block (topDecl fname)
           continue indents
           keyword "in"
           scope <- typeExpr fname indents
           end <- location
           pure (PLocal (MkFC fname start end) (collectDefs (concat ds)) scope)

  case_ : FileName -> IndentInfo -> Rule PTerm
  case_ fname indents
      = do start <- location
           keyword "case"
           scr <- expr fname indents
           keyword "of"
           alts <- block (caseAlt fname)
           end <- location
           pure (PCase (MkFC fname start end) scr alts)

  caseAlt : FileName -> IndentInfo -> Rule PClause
  caseAlt fname indents
      = do start <- location
           lhs <- expr fname indents
           caseRHS fname start indents lhs
          
  caseRHS : FileName -> FilePos -> IndentInfo -> PTerm -> Rule PClause
  caseRHS fname start indents lhs
      = do symbol "=>"
           continue indents
           rhs <- expr fname indents
           atEnd indents 
           end <- location
           pure (MkPatClause (MkFC fname start end) lhs rhs)
    <|> do keyword "impossible"
           atEnd indents
           end <- location
           pure (MkImpossible (MkFC fname start end) lhs)

  binder : FileName -> IndentInfo -> Rule PTerm
  binder fname indents
      = autoImplicitPi fname indents
    <|> implicitPi fname indents
    <|> explicitPi fname indents
    <|> lam fname indents
    <|> let_ fname indents
    <|> case_ fname indents

  typeExpr : FileName -> IndentInfo -> Rule PTerm
  typeExpr fname indents
      = do start <- location
           arg <- opExpr fname indents
           (do symbol "->"
               rest <- sepBy (symbol "->") (opExpr fname indents)
               end <- location
               pure (mkPi start end arg rest))
             <|> pure arg
    where
      mkPi : FilePos -> FilePos -> PTerm -> List PTerm -> PTerm
      mkPi start end arg [] = arg
      mkPi start end arg (a :: as) 
            = PPi (MkFC fname start end) RigW Explicit Nothing arg 
                  (mkPi start end a as)

  export
  expr : FileName -> IndentInfo -> Rule PTerm
  expr = typeExpr

tyDecl : FileName -> IndentInfo -> Rule PTypeDecl
tyDecl fname indents
    = do start <- location
         n <- name
         symbol ":"
         ty <- expr fname indents
         end <- location
         atEnd indents
         pure (MkPTy (MkFC fname start end) n ty)

parseRHS : FileName -> FilePos -> IndentInfo -> (lhs : PTerm) -> Rule (Name, PClause)
parseRHS fname start indents lhs
     = do symbol "="
          commit
          rhs <- expr fname indents
          atEnd indents
          fn <- getFn lhs
          end <- location
          pure (fn, MkPatClause (MkFC fname start end) lhs rhs)
   <|> do keyword "impossible"
          atEnd indents
          fn <- getFn lhs
          end <- location
          pure (fn, MkImpossible (MkFC fname start end) lhs)
  where
    getFn : PTerm -> EmptyRule Name
    getFn (PRef _ n) = pure n
    getFn (PApp _ f a) = getFn f
    getFn (PImplicitApp _ f _ a) = getFn f
    getFn _ = fail "Not a function application" 


clause : FileName -> IndentInfo -> Rule (Name, PClause)
clause fname indents
    = do start <- location
         lhs <- expr fname indents
         parseRHS fname start indents lhs

dataDecl : FileName -> IndentInfo -> Rule PDataDecl
dataDecl fname indents
    = do start <- location
         keyword "data"
         n <- name
         symbol ":"
         ty <- expr fname indents
         keyword "where"
         cs <- block (tyDecl fname)
         end <- location
         pure (MkPData (MkFC fname start end) n ty cs)

directive : IndentInfo -> Rule Directive
directive indents
    = do exactIdent "logging"
         lvl <- intLit
         atEnd indents
         pure (Logging (cast lvl))

fixDecl : Rule Fixity
fixDecl
    = do keyword "infixl"; pure InfixL
  <|> do keyword "infixr"; pure InfixR
  <|> do keyword "infix"; pure Infix
  <|> do keyword "prefix"; pure Prefix

namespaceDecl : Rule (List String)
namespaceDecl 
    = do keyword "namespace"
         commit
         ns <- namespace_
         pure ns

-- Declared at the top
-- topDecl : FileName -> IndentInfo -> Rule (List PDecl)
topDecl fname indents
    = do start <- location
         dat <- dataDecl fname indents
         end <- location
         pure [PData (MkFC fname start end) dat]
  <|> do start <- location
         ns <- namespaceDecl
         end <- location
         ds <- assert_total (nonEmptyBlock (topDecl fname))
         pure [PNamespace (MkFC fname start end) ns (concat ds)]
  <|> do start <- location
         symbol "%"; commit
         d <- directive indents
         end <- location
         pure [PDirective (MkFC fname start end) d]
  <|> do start <- location
         fixity <- fixDecl
         commit
         prec <- intLit
         ops <- sepBy1 (symbol ",") operator
         end <- location
         pure (map (PFixity (MkFC fname start end) fixity (cast prec)) ops)
  <|> do start <- location
         claim <- tyDecl fname indents
         end <- location
         pure [PClaim (MkFC fname start end) claim]
  <|> do start <- location
         nd <- clause fname indents
         end <- location
         pure [PDef (MkFC fname start end) (fst nd) [snd nd]]

-- All the clauses get parsed as one-clause definitions. Collect any
-- neighbouring clauses with the same function name into one definition.
-- Declared at the top.
-- collectDefs : List PDecl -> List PDecl
collectDefs [] = []
collectDefs (PDef annot fn cs :: ds)
    = let (cs', rest) = spanMap (isClause fn) ds in
          PDef annot fn (cs ++ cs') :: assert_total (collectDefs rest)
  where
    spanMap : (a -> Maybe (List b)) -> List a -> (List b, List a)
    spanMap f [] = ([], [])
    spanMap f (x :: xs) = case f x of
                               Nothing => ([], x :: xs)
                               Just y => case spanMap f xs of
                                              (ys, zs) => (y ++ ys, zs)

    isClause : Name -> PDecl -> Maybe (List PClause)
    isClause n (PDef annot n' cs) 
        = if n == n' then Just cs else Nothing
    isClause n _ = Nothing
collectDefs (PNamespace annot ns nds :: ds)
    = PNamespace annot ns (collectDefs nds) :: collectDefs ds
collectDefs (d :: ds)
    = d :: collectDefs ds

export
prog : FileName -> Rule Module
prog fname
    = do nspace <- option ["Main"]
                      (do keyword "module"
                          namespace_)
         l <- location
         ds <- nonEmptyBlock (topDecl fname)
         pure (MkModule nspace [] (collectDefs (concat ds)))

export
command : Rule REPLCmd
command
    = do symbol ":"; exactIdent "t"
         tm <- expr "(interactive)" init
         pure (Check tm)
  <|> do symbol ":"; exactIdent "s"
         n <- name
         pure (ProofSearch n)
  <|> do symbol ":"; exactIdent "di"
         n <- name
         pure (DebugInfo n)
  <|> do symbol ":"; exactIdent "q"
         pure Quit
  <|> do tm <- expr "(interactive)" init
         pure (Eval tm)
