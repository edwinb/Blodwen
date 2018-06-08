module Idris.Parser

import Idris.Syntax
import public Parser.Support
import Parser.Lexer
import TTImp.TTImp

import public Text.Parser
import Data.List.Views

%default covering

-- Forward declare since they're used in the parser
topDecl : FileName -> IndentInfo -> Rule (List PDecl)
collectDefs : List PDecl -> List PDecl

public export
data EqOp = NoEq | EqOK

export
Eq EqOp where
  NoEq == NoEq = True
  EqOK == EqOK = True
  _ == _ = False

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
         exactIdent "MkWorld"
         end <- location
         pure (PPrimVal (MkFC fname start end) WorldVal)
  <|> do start <- location
         symbol "%"
         exactIdent "World"
         end <- location
         pure (PPrimVal (MkFC fname start end) WorldType)
  <|> do start <- location
         symbol "%"
         exactIdent "search"
         end <- location
         pure (PSearch (MkFC fname start end) 1000)
  <|> do start <- location
         x <- name
         end <- location
         pure (PRef (MkFC fname start end) x)
  
whereBlock : FileName -> Rule (List PDecl)
whereBlock fname
    = do keyword "where"
         ds <- block (topDecl fname)
         pure (collectDefs (concat ds))


mutual
  appExpr : FileName -> IndentInfo -> Rule PTerm
  appExpr fname indents
      = case_ fname indents
    <|> if_ fname indents
    <|> doBlock fname indents
    <|> do start <- location
           f <- simpleExpr fname indents
           args <- many (argExpr fname indents)
           end <- location
           pure (applyExpImp start end f args)
    <|> do start <- location
           op <- operator
           arg <- expr EqOK fname indents
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
               tm <- expr EqOK fname indents
               symbol "}"
               pure (UN x, tm))
             <|> (do symbol "}"
                     end <- location
                     pure (UN x, PRef (MkFC fname start end) (UN x)))
           

  opExpr : EqOp -> FileName -> IndentInfo -> Rule PTerm
  opExpr q fname indents
      = do start <- location
           l <- appExpr fname indents
           (do continue indents
               op <- operator
               r <- opExpr q fname indents
               end <- location
               pure (POp (MkFC fname start end) op l r))
             <|> (if q == EqOK
                     then do continue indents
                             symbol "=" 
                             r <- opExpr EqOK fname indents
                             end <- location
                             pure (PEq (MkFC fname start end) l r)
                     else fail "= not allowed")
               <|> pure l

  bracketedExpr : FileName -> FilePos -> IndentInfo -> Rule PTerm
  bracketedExpr fname start indents
      -- left section. This may also be a prefix operator, but we'll sort
      -- that out when desugaring: if the operator is infix, treat it as a
      -- section otherwise treat it as prefix
      = do op <- operator
           e <- expr EqOK fname indents
           symbol ")"
           end <- location
           pure (PSectionL (MkFC fname start end) op e)
      -- unit type/value
    <|> do symbol ")"
           end <- location
           pure (PUnit (MkFC fname start end))
      -- right section (1-tuple is just an expression)
    <|> do e <- expr EqOK fname indents
           (do op <- operator
               symbol ")"
               end <- location
               pure (PSectionR (MkFC fname start end) e op)
             <|>
            -- all the other bracketed expressions
            tuple fname start indents e)

  listExpr : FileName -> FilePos -> IndentInfo -> Rule PTerm
  listExpr fname start indents
      = do xs <- sepBy (symbol ",") (expr EqOK fname indents)
           symbol "]"
           end <- location
           pure (PList (MkFC fname start end) xs)

  -- A pair, dependent pair, or just a single expression
  tuple : FileName -> FilePos -> IndentInfo -> PTerm -> Rule PTerm
  tuple fname start indents e
      = do rest <- some (do symbol ","
                            estart <- location
                            el <- expr EqOK fname indents
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
           e <- expr EqOK fname indents
           symbol ")"
           end <- location
           pure (PDotted (MkFC fname start end) e)
    <|> do start <- location
           symbol "`("
           e <- expr EqOK fname indents
           symbol ")"
           end <- location
           pure (PQuote (MkFC fname start end) e)
    <|> do start <- location
           symbol "~"
           e <- simpleExpr fname indents
           end <- location
           pure (PUnquote (MkFC fname start end) e)
    <|> do start <- location
           symbol "("
           bracketedExpr fname start indents
    <|> do start <- location
           symbol "["
           listExpr fname start indents
  
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
                                expr EqOK fname indents)
                   pure (rig, n, ty))

  pibindList : FileName -> FilePos -> IndentInfo -> 
               Rule (List (RigCount, Maybe Name, PTerm))
  pibindList fname start indents
       = do rig <- multiplicity
            ns <- sepBy (symbol ",") name
            symbol ":"
            ty <- expr EqOK fname indents
            atEnd indents
            pure (map (\n => (rig, Just n, ty)) ns)
     <|> sepBy1 (symbol ",")
                (do rig <- multiplicity
                    n <- name
                    symbol ":"
                    ty <- expr EqOK fname indents
                    pure (rig, Just n, ty))

  explicitPi : FileName -> IndentInfo -> Rule PTerm
  explicitPi fname indents
      = do start <- location
           symbol "("
           binders <- pibindList fname start indents
           symbol ")"
           symbol "->"
           scope <- typeExpr EqOK fname indents
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
           scope <- typeExpr EqOK fname indents
           end <- location
           pure (pibindAll (MkFC fname start end) AutoImplicit binders scope)

  implicitPi : FileName -> IndentInfo -> Rule PTerm
  implicitPi fname indents
      = do start <- location
           symbol "{"
           binders <- pibindList fname start indents
           symbol "}"
           symbol "->"
           scope <- typeExpr EqOK fname indents
           end <- location
           pure (pibindAll (MkFC fname start end) Implicit binders scope)

  lam : FileName -> IndentInfo -> Rule PTerm
  lam fname indents
      = do start <- location
           symbol "\\"
           binders <- bindList fname start indents
           symbol "=>"
           continue indents
           scope <- typeExpr EqOK fname indents
           end <- location
           pure (bindAll (MkFC fname start end) binders scope)
     where
       bindAll : FC -> List (RigCount, Name, PTerm) -> PTerm -> PTerm
       bindAll fc [] scope = scope
       bindAll fc ((rig, n, ty) :: rest) scope
           = PLam fc rig Explicit n ty (bindAll fc rest scope)

  letBinder : FileName -> IndentInfo -> 
              Rule (FilePos, FilePos, RigCount, PTerm, PTerm, List PClause)
  letBinder fname indents
      = do start <- location
           rig <- multiplicity
           pat <- expr NoEq fname indents
           symbol "="
           val <- expr EqOK fname indents
           alts <- block (patAlt fname)
           end <- location
           pure (start, end, rig, pat, val, alts)

  buildLets : FileName ->
              List (FilePos, FilePos, RigCount, PTerm, PTerm, List PClause) ->
              PTerm -> PTerm
  buildLets fname [] sc = sc
  buildLets fname ((start, end, rig, pat, val, alts) :: rest) sc
      = let fc = MkFC fname start end in
            PLet fc rig pat (PImplicit fc) val 
                 (buildLets fname rest sc) alts

  buildDoLets : FileName ->
                List (FilePos, FilePos, RigCount, PTerm, PTerm, List PClause) ->
                List PDo
  buildDoLets fname [] = []
  buildDoLets fname ((start, end, rig, PRef fc' (UN n), val, []) :: rest)
      = let fc = MkFC fname start end in
            if lowerFirst n
               then DoLet fc (UN n) rig val :: buildDoLets fname rest
               else DoLetPat fc (PRef fc' (UN n)) val [] 
                         :: buildDoLets fname rest
  buildDoLets fname ((start, end, rig, pat, val, alts) :: rest)
      = let fc = MkFC fname start end in
            DoLetPat fc pat val alts :: buildDoLets fname rest

  let_ : FileName -> IndentInfo -> Rule PTerm
  let_ fname indents
      = do start <- location
           keyword "let"
           res <- block (letBinder fname) 
           continue indents
           keyword "in"
           scope <- typeExpr EqOK fname indents
           end <- location
           pure (buildLets fname res scope)
                
    <|> do start <- location
           keyword "let"
           ds <- block (topDecl fname)
           continue indents
           keyword "in"
           scope <- typeExpr EqOK fname indents
           end <- location
           pure (PLocal (MkFC fname start end) (collectDefs (concat ds)) scope)

  case_ : FileName -> IndentInfo -> Rule PTerm
  case_ fname indents
      = do start <- location
           keyword "case"
           scr <- expr EqOK fname indents
           keyword "of"
           alts <- block (caseAlt fname)
           end <- location
           pure (PCase (MkFC fname start end) scr alts)

  caseAlt : FileName -> IndentInfo -> Rule PClause
  caseAlt fname indents
      = do start <- location
           lhs <- expr NoEq fname indents
           caseRHS fname start indents lhs
          
  caseRHS : FileName -> FilePos -> IndentInfo -> PTerm -> Rule PClause
  caseRHS fname start indents lhs
      = do symbol "=>"
           continue indents
           rhs <- expr EqOK fname indents
           atEnd indents 
           end <- location
           pure (MkPatClause (MkFC fname start end) lhs rhs [])
    <|> do keyword "impossible"
           atEnd indents
           end <- location
           pure (MkImpossible (MkFC fname start end) lhs)

  if_ : FileName -> IndentInfo -> Rule PTerm
  if_ fname indents
      = do start <- location
           keyword "if"
           x <- expr EqOK fname indents
           keyword "then"
           t <- expr EqOK fname indents
           keyword "else"
           e <- expr EqOK fname indents
           atEnd indents
           end <- location
           pure (PIfThenElse (MkFC fname start end) x t e)

  doBlock : FileName -> IndentInfo -> Rule PTerm
  doBlock fname indents
      = do start <- location
           keyword "do"
           actions <- block (doAct fname)
           end <- location
           pure (PDoBlock (MkFC fname start end) (concat actions))

  lowerFirst : String -> Bool
  lowerFirst "" = False
  lowerFirst str = assert_total (isLower (strHead str))

  validPatternVar : Name -> EmptyRule ()
  validPatternVar (UN n)
      = if lowerFirst n then pure ()
                        else fail "Not a pattern variable"
  validPatternVar _ = fail "Not a pattern variable"

  doAct : FileName -> IndentInfo -> Rule (List PDo)
  doAct fname indents
      = do start <- location
           n <- name
           -- If the name doesn't begin with a lower case letter, we should
           -- treat this as a pattern, so fail
           validPatternVar n
           symbol "<-"
           val <- expr EqOK fname indents
           atEnd indents
           end <- location
           pure [DoBind (MkFC fname start end) n val]
    <|> do keyword "let"
           res <- block (letBinder fname)
           atEnd indents
           pure (buildDoLets fname res)
    <|> do start <- location
           keyword "let"
           res <- block (topDecl fname)
           end <- location
           atEnd indents
           pure [DoLetLocal (MkFC fname start end) (concat res)]
    <|> do start <- location
           e <- expr NoEq fname indents
           (do atEnd indents
               end <- location
               pure [DoExp (MkFC fname start end) e])
             <|> (do symbol "<-"
                     val <- expr EqOK fname indents
                     alts <- block (patAlt fname)
                     atEnd indents
                     end <- location
                     pure [DoBindPat (MkFC fname start end) e val alts])

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

  typeExpr : EqOp -> FileName -> IndentInfo -> Rule PTerm
  typeExpr q fname indents
      = do start <- location
           arg <- opExpr q fname indents
           (do symbol "->"
               rest <- sepBy (symbol "->") (opExpr EqOK fname indents)
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
  expr : EqOp -> FileName -> IndentInfo -> Rule PTerm
  expr = typeExpr

visOption : Rule Visibility
visOption
    = do keyword "public"
         keyword "export"
         pure Public
  <|> do keyword "export"
         pure Export
  <|> do keyword "private"
         pure Private

visibility : EmptyRule Visibility
visibility
    = visOption
  <|> pure Private

tyDecl : FileName -> IndentInfo -> Rule PTypeDecl
tyDecl fname indents
    = do start <- location
         n <- name
         symbol ":"
         ty <- expr EqOK fname indents
         end <- location
         atEnd indents
         pure (MkPTy (MkFC fname start end) n ty)

parseRHS : FileName -> FilePos -> IndentInfo -> (lhs : PTerm) -> Rule (Name, PClause)
parseRHS fname start indents lhs
     = do symbol "="
          commit
          rhs <- expr EqOK fname indents
          ws <- option [] (whereBlock fname)
          atEnd indents
          fn <- getFn lhs
          end <- location
          pure (fn, MkPatClause (MkFC fname start end) lhs rhs ws)
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
         lhs <- expr NoEq fname indents
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
                       (mkTyConType tyfc params) [] cons)

dataOpt : Rule DataOpt
dataOpt
    = do exactIdent "noHints"
         pure NoHints
  <|> do exactIdent "search"
         ns <- some name
         pure (SearchBy ns)

dataBody : FileName -> FilePos -> Name -> IndentInfo -> PTerm -> 
           EmptyRule PDataDecl
dataBody fname start n indents ty
    = do atEnd indents
         end <- location
         pure (MkPLater (MkFC fname start end) n ty)
  <|> do keyword "where"
         opts <- option [] (do symbol "["
                               dopts <- sepBy1 (symbol ",") dataOpt
                               symbol "]"
                               pure dopts)
         cs <- block (tyDecl fname)
         end <- location
         pure (MkPData (MkFC fname start end) n ty opts cs)

gadtData : FileName -> FilePos -> Name -> IndentInfo -> Rule PDataDecl
gadtData fname start n indents
    = do symbol ":"
         commit
         ty <- expr EqOK fname indents
         dataBody fname start n indents ty

dataDeclBody : FileName -> IndentInfo -> Rule PDataDecl
dataDeclBody fname indents
    = do start <- location
         keyword "data"
         n <- name
         simpleData fname start n indents 
           <|> gadtData fname start n indents

dataDecl : FileName -> IndentInfo -> Rule PDecl
dataDecl fname indents
    = do start <- location
         vis <- visibility
         dat <- dataDeclBody fname indents
         end <- location
         pure (PData (MkFC fname start end) vis dat)

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

fix : Rule Fixity
fix
    = do keyword "infixl"; pure InfixL
  <|> do keyword "infixr"; pure InfixR
  <|> do keyword "infix"; pure Infix
  <|> do keyword "prefix"; pure Prefix

namespaceHead : Rule (List String)
namespaceHead 
    = do keyword "namespace"
         commit
         ns <- namespace_
         pure ns

namespaceDecl : FileName -> IndentInfo -> Rule PDecl
namespaceDecl fname indents
    = do start <- location
         ns <- namespaceHead
         end <- location
         ds <- assert_total (nonEmptyBlock (topDecl fname))
         pure (PNamespace (MkFC fname start end) ns (concat ds))

fnOpt : Rule FnOpt
fnOpt
    = do exactIdent "hint"
         pure Hint
  <|> do exactIdent "globalhint"
         pure GlobalHint
  <|> do exactIdent "inline"
         pure Inline

visOpt : Rule (Either Visibility FnOpt)
visOpt
    = do vis <- visOption
         pure (Left vis)
  <|> do symbol "%"
         opt <- fnOpt
         pure (Right opt)

getVisibility : Maybe Visibility -> List (Either Visibility FnOpt) -> 
                EmptyRule Visibility
getVisibility Nothing [] = pure Private
getVisibility (Just vis) [] = pure vis
getVisibility Nothing (Left x :: xs) = getVisibility (Just x) xs
getVisibility (Just vis) (Left x :: xs)
   = fail $ "Multiple visibility modifiers"
getVisibility v (_ :: xs) = getVisibility v xs

getRight : Either a b -> Maybe b
getRight (Left _) = Nothing
getRight (Right v) = Just v

constraints : FileName -> IndentInfo -> EmptyRule (List (Maybe Name, PTerm))
constraints fname indents
    = do tm <- expr EqOK fname indents
         symbol "=>"
         more <- constraints fname indents
         pure ((Nothing, tm) :: more)
  <|> do symbol "("
         n <- name
         symbol ":"
         tm <- expr EqOK fname indents
         symbol ")"
         symbol "=>"
         more <- constraints fname indents
         pure ((Just n, tm) :: more)
  <|> pure []

ifaceParam : FileName -> IndentInfo -> Rule (Name, PTerm)
ifaceParam fname indents
    = do symbol "("
         n <- name
         symbol ":"
         tm <- expr EqOK fname indents
         symbol ")"
         pure (n, tm)
  <|> do start <- location
         n <- name
         end <- location
         pure (n, PImplicit (MkFC fname start end))

ifaceDecl : FileName -> IndentInfo -> Rule PDecl
ifaceDecl fname indents
    = do start <- location
         vis <- visibility
         keyword "interface"
         commit
         cons <- constraints fname indents
         n <- name
         params <- many (ifaceParam fname indents)
         det <- option [] (do symbol "|"
                              sepBy (symbol ",") name)
         keyword "where"
         dc <- option Nothing (do exactIdent "constructor"
                                  n <- name
                                  pure (Just n))
         body <- assert_total (nonEmptyBlock (topDecl fname))
         end <- location
         pure (PInterface (MkFC fname start end) 
                      vis cons n params det dc (collectDefs (concat body)))

implDecl : FileName -> IndentInfo -> Rule PDecl
implDecl fname indents
    = do start <- location
         vis <- visibility
         cons <- constraints fname indents
         option () (keyword "implementation")
         iname <- option Nothing (do symbol "["
                                     iname <- name
                                     symbol "]"
                                     pure (Just iname))
         n <- name
         params <- many (simpleExpr fname indents)
         keyword "where"
         body <- assert_total (nonEmptyBlock (topDecl fname))
         end <- location
         pure (PImplementation (MkFC fname start end)
                         vis cons n params iname (collectDefs (concat body)))

claim : FileName -> IndentInfo -> Rule PDecl
claim fname indents
    = do start <- location
         visOpts <- many visOpt
         vis <- getVisibility Nothing visOpts
         let opts = mapMaybe getRight visOpts
         cl <- tyDecl fname indents
         end <- location
         pure (PClaim (MkFC fname start end) vis opts cl)
         
definition : FileName -> IndentInfo -> Rule PDecl
definition fname indents
    = do start <- location
         nd <- clause fname indents
         end <- location
         pure (PDef (MkFC fname start end) (fst nd) [snd nd])

fixDecl : FileName -> IndentInfo -> Rule (List PDecl)
fixDecl fname indents
    = do start <- location
         fixity <- fix
         commit
         prec <- intLit
         ops <- sepBy1 (symbol ",") operator
         end <- location
         pure (map (PFixity (MkFC fname start end) fixity (cast prec)) ops)

directiveDecl : FileName -> IndentInfo -> Rule PDecl
directiveDecl fname indents
    = do start <- location
         symbol "%" 
         (do d <- directive indents
             end <- location
             pure (PDirective (MkFC fname start end) d))
           <|>
          (do exactIdent "runElab"
              tm <- expr EqOK fname indents
              end <- location
              atEnd indents
              pure (PReflect (MkFC fname start end) tm))

-- Declared at the top
-- topDecl : FileName -> IndentInfo -> Rule (List PDecl)
topDecl fname indents
    = do d <- dataDecl fname indents
         pure [d]
  <|> do d <- namespaceDecl fname indents
         pure [d]
  <|> do d <- directiveDecl fname indents
         pure [d]
  <|> fixDecl fname indents
  <|> do d <- ifaceDecl fname indents
         pure [d]
  <|> do d <- implDecl fname indents
         pure [d]
  <|> do d <- claim fname indents
         pure [d]
  <|> do d <- definition fname indents
         pure [d]

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

parseMode : Rule REPLEval
parseMode
     = do exactIdent "typecheck"
          pure EvalTC
   <|> do exactIdent "normalise"
          pure NormaliseAll
   <|> do exactIdent "normalize" -- oh alright then
          pure NormaliseAll
   <|> do exactIdent "execute"
          pure Execute

setOption : Bool -> Rule REPLOpt
setOption set
    = do exactIdent "showimplicits"
         pure (ShowImplicits set)
  <|> do exactIdent "showtypes"
         pure (ShowTypes set)
  <|> if set
         then do exactIdent "eval"
                 mode <- parseMode
                 pure (EvalMode mode)
         else fail "Invalid option"

export
command : Rule REPLCmd
command
    = do symbol ":"; exactIdent "t"
         tm <- expr EqOK "(interactive)" init
         pure (Check tm)
  <|> do symbol ":"; exactIdent "s"
         n <- name
         pure (ProofSearch n)
  <|> do symbol ":"; exactIdent "di"
         n <- name
         pure (DebugInfo n)
  <|> do symbol ":"; exactIdent "q"
         pure Quit
  <|> do symbol ":"; exactIdent "set"
         opt <- setOption True
         pure (SetOpt opt)
  <|> do symbol ":"; exactIdent "unset"
         opt <- setOption False
         pure (SetOpt opt)
  <|> do tm <- expr EqOK "(interactive)" init
         pure (Eval tm)
