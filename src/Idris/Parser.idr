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
      = case_ fname indents
    <|> doBlock fname indents
    <|> do start <- location
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
      = do start <- location
           symbol "{"
           x <- unqualifiedName
           (do symbol "="
               commit
               tm <- expr fname indents
               symbol "}"
               pure (UN x, tm))
             <|> (do symbol "}"
                     end <- location
                     pure (UN x, PRef (MkFC fname start end) (UN x)))
           

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
      -- unit type/value
    <|> do symbol ")"
           end <- location
           pure (PUnit (MkFC fname start end))
      -- right section (1-tuple is just an expression)
    <|> do e <- expr fname indents
           (do op <- operator
               symbol ")"
               end <- location
               pure (PSectionR (MkFC fname start end) e op)
             <|>
            -- all the other bracketed expressions
            tuple fname start indents e)

  -- A pair, dependent pair, or just a single expression
  tuple : FileName -> FilePos -> IndentInfo -> PTerm -> Rule PTerm
  tuple fname start indents e
      = do rest <- some (do symbol ","
                            estart <- location
                            el <- expr fname indents
                            pure (estart, el))
           symbol ")"
           end <- location
           pure (PPair (MkFC fname start end) e
                       (mergePairs end rest))
     <|> do symbol ")"
            end <- location
            pure (PBracketed (MkFC fname start end) e)
    where
      mergePairs : FilePos -> List (FilePos, PTerm) -> PTerm
      mergePairs end [] = PUnit (MkFC fname start end)
      mergePairs end [(estart, exp)] = exp
      mergePairs end ((estart, exp) :: rest)
          = PPair (MkFC fname estart end) exp (mergePairs end rest)

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
  
  getMult : Constant -> EmptyRule RigCount
  getMult (BI 0) = pure Rig0
  getMult (BI 1) = pure Rig1
  getMult _ = fail "Invalid multiplicity"

  multiplicity : EmptyRule RigCount
  multiplicity
      = do c <- constant
           getMult c
    <|> pure RigW
       
  pibindAll : FC -> PiInfo -> List (RigCount, Maybe Name, PTerm) -> 
              PTerm -> PTerm
  pibindAll fc p [] scope = scope
  pibindAll fc p ((rig, n, ty) :: rest) scope
           = PPi fc rig p n ty (pibindAll fc p rest scope)

  bindList : FileName -> FilePos -> IndentInfo -> 
             Rule (List (RigCount, Name, PTerm))
  bindList fname start indents
      = sepBy1 (symbol ",")
               (do rig <- multiplicity
                   n <- name
                   ty <- option 
                            (PImplicit (MkFC fname start start))
                            (do symbol ":"
                                expr fname indents)
                   pure (rig, n, ty))

  pibindList : FileName -> FilePos -> IndentInfo -> 
               Rule (List (RigCount, Maybe Name, PTerm))
  pibindList fname start indents
       = do rig <- multiplicity
            ns <- sepBy (symbol ",") name
            symbol ":"
            ty <- expr fname indents
            atEnd indents
            pure (map (\n => (rig, Just n, ty)) ns)
     <|> sepBy1 (symbol ",")
                (do rig <- multiplicity
                    n <- name
                    symbol ":"
                    ty <- expr fname indents
                    pure (rig, Just n, ty))

  explicitPi : FileName -> IndentInfo -> Rule PTerm
  explicitPi fname indents
      = do start <- location
           symbol "("
           binders <- pibindList fname start indents
           symbol ")"
           symbol "->"
           scope <- typeExpr fname indents
           end <- location
           pure (pibindAll (MkFC fname start end) Explicit binders scope)

  autoImplicitPi : FileName -> IndentInfo -> Rule PTerm
  autoImplicitPi fname indents
      = do start <- location
           symbol "{"
           keyword "auto"
           commit
           binders <- pibindList fname start indents
           symbol "}"
           symbol "->"
           scope <- typeExpr fname indents
           end <- location
           pure (pibindAll (MkFC fname start end) AutoImplicit binders scope)

  implicitPi : FileName -> IndentInfo -> Rule PTerm
  implicitPi fname indents
      = do start <- location
           symbol "{"
           binders <- pibindList fname start indents
           symbol "}"
           symbol "->"
           scope <- typeExpr fname indents
           end <- location
           pure (pibindAll (MkFC fname start end) Implicit binders scope)

  lam : FileName -> IndentInfo -> Rule PTerm
  lam fname indents
      = do start <- location
           symbol "\\"
           binders <- bindList fname start indents
           symbol "=>"
           continue indents
           scope <- typeExpr fname indents
           end <- location
           pure (bindAll (MkFC fname start end) binders scope)
     where
       bindAll : FC -> List (RigCount, Name, PTerm) -> PTerm -> PTerm
       bindAll fc [] scope = scope
       bindAll fc ((rig, n, ty) :: rest) scope
           = PLam fc rig Explicit n ty (bindAll fc rest scope)

  let_ : FileName -> IndentInfo -> Rule PTerm
  let_ fname indents
      = do start <- location
           keyword "let"
           rig <- multiplicity
           n <- name
           symbol "="
           commit
           val <- expr fname indents
           continue indents
           keyword "in"
           scope <- typeExpr fname indents
           end <- location
           pure (PLet (MkFC fname start end) rig n (PImplicit (MkFC fname start end)) val scope)
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

  doBlock : FileName -> IndentInfo -> Rule PTerm
  doBlock fname indents
      = do start <- location
           keyword "do"
           actions <- block (doAct fname)
           end <- location
           pure (PDoBlock (MkFC fname start end) actions)

  lowerFirst : String -> Bool
  lowerFirst "" = False
  lowerFirst str = assert_total (isLower (strHead str))

  validPatternVar : Name -> EmptyRule ()
  validPatternVar (UN n)
      = if lowerFirst n then pure ()
                        else fail "Not a pattern variable"
  validPatternVar _ = fail "Not a pattern variable"

  doAct : FileName -> IndentInfo -> Rule PDo
  doAct fname indents
      = do start <- location
           n <- name
           -- If the name doesn't begin with a lower case letter, we should
           -- treat this as a pattern, so fail
           validPatternVar n
           symbol "<-"
           val <- expr fname indents
           atEnd indents
           end <- location
           pure (DoBind (MkFC fname start end) n val)
    <|> do start <- location
           keyword "let"
           rig <- multiplicity
           n <- name
           validPatternVar n
           commit
           symbol "="
           val <- expr fname indents
           atEnd indents
           end <- location
           pure (DoLet (MkFC fname start end) n rig val)
    <|> do start <- location
           keyword "let"
           e <- expr fname indents
           symbol "="
           val <- expr fname indents
           alts <- block (patAlt fname)
           atEnd indents
           end <- location
           pure (DoLetPat (MkFC fname start end) e val alts)
    <|> do start <- location
           e <- expr fname indents
           (do atEnd indents
               end <- location
               pure (DoExp (MkFC fname start end) e))
             <|> (do symbol "<-"
                     val <- expr fname indents
                     alts <- block (patAlt fname)
                     atEnd indents
                     end <- location
                     pure (DoBindPat (MkFC fname start end) e val alts))

  patAlt : FileName -> IndentInfo -> Rule PClause
  patAlt fname indents
      = do symbol "|"
           caseAlt fname indents

  binder : FileName -> IndentInfo -> Rule PTerm
  binder fname indents
      = autoImplicitPi fname indents
    <|> implicitPi fname indents
    <|> explicitPi fname indents
    <|> lam fname indents
    <|> let_ fname indents

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

mkTyConType : FC -> List Name -> PTerm
mkTyConType fc [] = PType fc
mkTyConType fc (x :: xs) 
   = PPi fc Rig1 Explicit Nothing (PType fc) (mkTyConType fc xs)

mkDataConType : FC -> PTerm -> List (Either PTerm (Name, PTerm)) -> PTerm
mkDataConType fc ret [] = ret
mkDataConType fc ret (Left x :: xs)
    = PPi fc Rig1 Explicit Nothing x (mkDataConType fc ret xs)
mkDataConType fc ret (Right (n, PRef fc' x) :: xs)
    = if n == x
         then PPi fc Rig1 Implicit (Just n) (PType fc') 
                          (mkDataConType fc ret xs)
         else PPi fc Rig1 Implicit (Just n) (PRef fc' x) 
                          (mkDataConType fc ret xs)
mkDataConType fc ret (Right (n, x) :: xs)
    = PPi fc Rig1 Implicit (Just n) x (mkDataConType fc ret xs)

simpleCon : FileName -> PTerm -> IndentInfo -> Rule PTypeDecl
simpleCon fname ret indents
    = do start <- location
         cname <- name
         params <- many (argExpr fname indents)
         atEnd indents
         end <- location
         let cfc = MkFC fname start end
         pure (MkPTy cfc cname (mkDataConType cfc ret params)) 

simpleData : FileName -> FilePos -> Name -> IndentInfo -> Rule PDataDecl
simpleData fname start n indents
    = do params <- many name
         tyend <- location
         let tyfc = MkFC fname start tyend
         symbol "="
         let conRetTy = papply tyfc (PRef tyfc n)
                           (map (PRef tyfc) params)
         cons <- sepBy1 (symbol "|") 
                        (simpleCon fname conRetTy indents)
         end <- location
         pure (MkPData (MkFC fname start end) n
                       (mkTyConType tyfc params) cons)

gadtData : FileName -> FilePos -> Name -> IndentInfo -> Rule PDataDecl
gadtData fname start n indents
    = do symbol ":"
         commit
         ty <- expr fname indents
         keyword "where"
         cs <- block (tyDecl fname)
         end <- location
         pure (MkPData (MkFC fname start end) n ty cs)

dataDecl : FileName -> IndentInfo -> Rule PDataDecl
dataDecl fname indents
    = do start <- location
         keyword "data"
         n <- name
         simpleData fname start n indents 
           <|> gadtData fname start n indents

directive : IndentInfo -> Rule Directive
directive indents
    = do exactIdent "logging"
         lvl <- intLit
         atEnd indents
         pure (Logging (cast lvl))
  <|> do exactIdent "lazy"
         ty <- name
         f <- name
         d <- name
         atEnd indents
         pure (LazyNames ty f d)

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
         vis <- visibility
         dat <- dataDecl fname indents
         end <- location
         pure [PData (MkFC fname start end) vis dat]
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
         vis <- visibility
         claim <- tyDecl fname indents
         end <- location
         pure [PClaim (MkFC fname start end) vis claim]
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
import_ : FileName -> IndentInfo -> Rule Import
import_ fname indents
    = do start <- location
         keyword "import"
         reexp <- option False (do keyword "public"
                                   pure True)
         ns <- namespace_
         nsAs <- option ns (do exactIdent "as"
                               namespace_)
         end <- location
         atEnd indents
         pure (MkImport (MkFC fname start end) reexp ns nsAs)

export
prog : FileName -> Rule Module
prog fname
    = do start <- location
         nspace <- option ["Main"]
                      (do keyword "module"
                          namespace_)
         end <- location
         imports <- block (import_ fname)
         ds <- nonEmptyBlock (topDecl fname)
         pure (MkModule (MkFC fname start end)
                        nspace imports (collectDefs (concat ds)))

export
progHdr : FileName -> EmptyRule Module
progHdr fname
    = do start <- location
         nspace <- option ["Main"]
                      (do keyword "module"
                          namespace_)
         end <- location
         imports <- block (import_ fname)
         pure (MkModule (MkFC fname start end)
                        nspace imports [])

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
