module Compiler.Chez

import Compiler.Common
import Compiler.CompileExpr

import Core.Context
import Core.Name
import Core.TT

import Data.List
import Data.Vect
import System
import System.Info

%default covering

firstExists : List String -> IO (Maybe String)
firstExists [] = pure Nothing
firstExists (x :: xs) = if !(exists x) then pure (Just x) else firstExists xs

findChez : IO String
findChez 
    = do e <- firstExists [p ++ x | p <- ["/usr/bin/", "/usr/local/bin/"],
                                    x <- ["scheme", "chez"]]
         maybe (pure "/usr/bin/scheme") pure e

schHeader : String -> String
schHeader chez
  = "#!" ++ chez ++ " --script\n\n" ++
    "(let ()\n" ++
    "(define blodwen-read-args (lambda (desc)\n" ++
    "  (case (vector-ref desc 0)\n" ++
    "    ((0) '())\n" ++
    "    ((1) (cons (vector-ref desc 2)\n" ++
    "               (blodwen-read-args (vector-ref desc 3)))))))\n" ++
    "(define b+ (lambda (x y bits) (remainder (+ x y) (expt 2 bits))))\n" ++
    "(define b- (lambda (x y bits) (remainder (- x y) (expt 2 bits))))\n" ++
    "(define b* (lambda (x y bits) (remainder (* x y) (expt 2 bits))))\n" ++
    "(define b/ (lambda (x y bits) (remainder (/ x y) (expt 2 bits))))\n" ++
    "(define get-tag (lambda (x) (vector-ref x 0)))\n\n"

schFooter : String
schFooter = ")"

schString : String -> String
schString s = concatMap okchar (unpack s)
  where
    okchar : Char -> String
    okchar c = if isAlphaNum c || c =='_'
                  then cast c
                  else "C-" ++ show (cast {to=Int} c)

mutual
  schName : Name -> String
  schName (UN n) = schString n
  schName (MN n i) = schString n ++ "-" ++ show i
  schName (NS ns n) = showSep "-" ns ++ "-" ++ schName n
  schName (HN n i) = schString n ++ "--" ++ show i
  schName (PV n) = "pat--" ++ schName n
  schName (GN g) = schGName g

  schGName : GenName -> String
  schGName (Nested o i) = schName o ++ "--in--" ++ schName i
  schGName (CaseBlock n i) = "case--" ++ schName n ++ "-" ++ show i
  schGName (WithBlock n i) = "with--" ++ schName n ++ "-" ++ show i

-- local variable names as scheme names - we need to invent new names for the locals
-- because there might be shadows in the original expression which can't be resolved
-- by the same scoping rules. (e.g. something that computes \x, x => x + x where the
-- names are the same but refer to different bindings in the scope)
data SVars : List Name -> Type where
     Nil : SVars []
     (::) : (svar : String) -> SVars ns -> SVars (n :: ns)

extendSVars : (xs : List Name) -> SVars ns -> SVars (xs ++ ns)
extendSVars {ns} xs vs = extSVars' (cast (length ns)) xs vs
  where 
    extSVars' : Int -> (xs : List Name) -> SVars ns -> SVars (xs ++ ns)
    extSVars' i [] vs = vs
    extSVars' i (x :: xs) vs = schName (MN "v" i) :: extSVars' (i + 1) xs vs

initSVars : (xs : List Name) -> SVars xs
initSVars xs = rewrite sym (appendNilRightNeutral xs) in extendSVars xs []

lookupSVar : Elem x xs -> SVars xs -> String
lookupSVar Here (n :: ns) = n
lookupSVar (There p) (n :: ns) = lookupSVar p ns

schConstructor : Int -> List String -> String
schConstructor t args = "(vector " ++ show t ++ " " ++ showSep " " args ++ ")"

op : String -> List String -> String
op o args = "(" ++ o ++ " " ++ showSep " " args ++ ")"

boolop : String -> List String -> String
boolop o args = "(or (and " ++ op o args ++ " 1) 0)"

schOp : PrimFn arity -> Vect arity String -> String
schOp (Add IntType) [x, y] = op "b+" [x, y, "63"]
schOp (Sub IntType) [x, y] = op "b-" [x, y, "63"]
schOp (Mul IntType) [x, y] = op "b*" [x, y, "63"]
schOp (Div IntType) [x, y] = op "b/" [x, y, "63"]
schOp (Add ty) [x, y] = op "+" [x, y]
schOp (Sub ty) [x, y] = op "-" [x, y]
schOp (Mul ty) [x, y] = op "*" [x, y]
schOp (Div ty) [x, y] = op "/" [x, y]
schOp (Mod ty) [x, y] = op "remainder" [x, y]
schOp (Neg ty) [x] = op "-" ["0", x]
schOp (LT ty) [x, y] = boolop "<" [x, y]
schOp (LTE ty) [x, y] = boolop "<=" [x, y]
schOp (EQ ty) [x, y] = boolop "=" [x, y]
schOp (GTE ty) [x, y] = boolop ">=" [x, y]
schOp (GT ty) [x, y] = boolop ">" [x, y]
schOp StrLength [x] = op "string-length" [x]
schOp StrHead [x] = op "string-rev" [x, "0"]
schOp StrTail [x] = op "substring/shared" [x, "1"]
schOp StrAppend [x, y] = op "string-append" [x, y]
schOp StrReverse [x] = op "string-reverse" [x]
schOp (Cast IntType StringType) [x] = op "number->string" [x]
schOp (Cast IntegerType StringType) [x] = op "number->string" [x]
schOp (Cast DoubleType StringType) [x] = op "number->string" [x]
schOp (Cast from to) [x] = "(error \"Invalid cast " ++ show from ++ "->" ++ show to ++ ")"

data ExtPrim = CCall | SchemeCall | PutStr | GetStr | Unknown Name

toPrim : Name -> ExtPrim
toPrim pn@(NS _ n) 
    = cond [(n == UN "prim__schemeCall", SchemeCall),
            (n == UN "prim__cCall", CCall),
            (n == UN "prim__putStr", PutStr),
            (n == UN "prim__getStr", GetStr)]
           (Unknown pn)
toPrim pn = Unknown pn

mkWorld : String -> String
mkWorld res = schConstructor 0 ["#f", res, "#f"] -- MkIORes

schConstant : Constant -> String
schConstant (I x) = show x
schConstant (BI x) = show x
schConstant (Str x) = show x
schConstant (Ch x) = "#\\" ++ show x
schConstant (Db x) = show x
schConstant WorldVal = "#f"
schConstant IntType = "#t"
schConstant IntegerType = "#t"
schConstant StringType = "#t"
schConstant CharType = "#t"
schConstant DoubleType = "#t"
schConstant WorldType = "#t"

schCaseDef : Maybe String -> String
schCaseDef Nothing = ""
schCaseDef (Just tm) = "(else " ++ tm ++ ")"
  
mutual
  -- Need to convert the argument (a list of scheme arguments that may
  -- have been constructed at run time) to a scheme list to be passed to apply
  readArgs : SVars vars -> CExp vars -> String
  readArgs vs tm = "(blodwen-read-args " ++ schExp vs tm ++ ")"

  schExtPrim : SVars vars -> ExtPrim -> List (CExp vars) -> String
  schExtPrim vs SchemeCall [ret, CPrimVal (Str fn), args, world]
     = mkWorld ("(apply " ++ fn ++") "
                  ++ readArgs vs args ++ ")")
  schExtPrim vs SchemeCall [ret, fn, args, world]
     = mkWorld ("(apply (eval (string->symbol " ++ schExp vs fn ++")) "
                  ++ readArgs vs args ++ ")")
  schExtPrim vs PutStr [arg, world] 
      = "(display " ++ schExp vs arg ++ ") " ++ mkWorld "0" -- 0 is the code for MkUnit
  schExtPrim vs GetStr [world] 
      = mkWorld "(get-line (current-input-port))"
  schExtPrim vs (Unknown n) args = "(error \"Unknown external primitive " ++ show n ++ ")"
  schExtPrim vs _ args = "(error \"Badly formed external primitive\")"

  schConAlt : SVars vars -> String -> CConAlt vars -> String
  schConAlt {vars} vs target (MkConAlt n tag args sc)
      = let vs' = extendSVars args vs in
            "((" ++ show tag ++ ") "
                 ++ bindArgs 1 args vs' (schExp vs' sc) ++ ")"
    where
      bindArgs : Int -> (ns : List Name) -> SVars (ns ++ vars) -> String -> String
      bindArgs i [] vs body = body
      bindArgs i (n :: ns) (v :: vs) body 
          = "(let ((" ++ v ++ " " ++ "(vector-ref " ++ target ++ " " ++ show i ++ "))) "
                  ++ bindArgs (i + 1) ns vs body ++ ")"

  schConstAlt : SVars vars -> CConstAlt vars -> String
  schConstAlt vs (MkConstAlt c exp)
      = "((" ++ schConstant c ++ ") " ++ schExp vs exp ++ ")"

  schExp : SVars vars -> CExp vars -> String
  schExp vs (CLocal el) = lookupSVar el vs
  schExp vs (CRef n) = schName n
  schExp vs (CLam x sc) 
     = let vs' = extendSVars [x] vs 
           sc' = schExp vs' sc in
           "(lambda (" ++ lookupSVar Here vs' ++ ") " ++ sc' ++ ")"
  schExp vs (CLet x val sc) 
     = let vs' = extendSVars [x] vs
           val' = schExp vs val
           sc' = schExp vs' sc in
           "(let ((" ++ lookupSVar Here vs' ++ " " ++ val' ++ ")) " ++ sc' ++ ")"
  schExp vs (CApp x []) 
      = "(" ++ schExp vs x ++ ")"
  schExp vs (CApp x args) 
      = "(" ++ schExp vs x ++ " " ++ showSep " " (map (schExp vs) args) ++ ")"
  schExp vs (CCon x tag args) = schConstructor tag (map (schExp vs) args)
  schExp vs (COp op args) = schOp op (map (schExp vs) args)
  schExp vs (CExtPrim p args) = schExtPrim vs (toPrim p) args
  schExp vs (CForce t) = "(force " ++ schExp vs t ++ ")"
  schExp vs (CDelay t) = "(delay " ++ schExp vs t ++ ")"
  schExp vs (CConCase sc alts def) 
      = let tcode = schExp vs sc in
            "(case (get-tag " ++ tcode ++ ") "
                   ++ showSep " " (map (schConAlt vs tcode) alts)
                   ++ schCaseDef (map (schExp vs) def) ++ ")"
  schExp vs (CConstCase sc alts def) 
      = "(case " ++ schExp vs sc ++ " " 
                 ++ showSep " " (map (schConstAlt vs) alts)
                 ++ schCaseDef (map (schExp vs) def) ++ ")"
  schExp vs (CPrimVal c) = schConstant c
  schExp vs CErased = "9999"
  schExp vs (CCrash msg) = "(error " ++ show msg ++ ")"

schArgs : SVars ns -> String
schArgs [] = ""
schArgs [x] = x
schArgs (x :: xs) = x ++ " " ++ schArgs xs

schDef : Name -> CDef -> String
schDef n (MkFun args exp)
   = let vs = initSVars args in
         "(define " ++ schName n ++ " (lambda (" ++ schArgs vs ++ ") "
                    ++ schExp vs exp ++ "))\n"
schDef n (MkError exp)
   = "(define (" ++ schName n ++ " . any-args) " ++ schExp [] exp ++ ")\n"
schDef n (MkCon t a) = "" -- Nothing to compile here

-- Convert the name to scheme code
-- (There may be no code generated, for example if it's a constructor)
getScheme : Defs -> Name -> Either (Error annot) String
getScheme defs n
    = case lookupGlobalExact n (gamma defs) of
           Nothing => Left (InternalError ("Compiling undefined name " ++ show n))
           Just d => case compexpr d of
                          Nothing =>
                             Left (InternalError ("No compiled definition for " ++ show n))
                          Just d => Right (schDef n d)

getSchemes : Defs -> List Name -> Either (Error annot) String
getSchemes defs [] = pure ""
getSchemes defs (n :: ns)
    = do ncomp <- getScheme defs n
         nscomp <- getSchemes defs ns
         pure (ncomp ++ nscomp)

export
compileExpr : {auto c : Ref Ctxt Defs} ->
              ClosedTerm -> (outfile : String) -> Core annot ()
compileExpr {annot} tm outfile
    = do ns <- findUsedNames tm
         defs <- get Ctxt
         let Right code = getSchemes {annot} defs ns
            | Left err => throw err
         let main = schExp [] !(compileExp tm)
         chez <- coreLift findChez
         let scm = schHeader chez ++ code ++ main ++ schFooter
         Right () <- coreLift $ writeFile outfile scm
            | Left err => throw (FileErr outfile err)
         coreLift $ chmod outfile 0o755
         pure ()

export
executeExpr : {auto c : Ref Ctxt Defs} -> ClosedTerm -> Core annot ()
executeExpr tm
    = do tmp <- coreLift $ tmpName
         let outn = tmp ++ ".ss"
         compileExpr tm outn
         chez <- coreLift findChez
         coreLift $ system (chez ++ " --script " ++ outn)
         pure ()

