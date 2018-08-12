module Compiler.Chez

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Inline

import Core.Context
import Core.Directory
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
         maybe (pure "/usr/bin/env scheme") pure e

schHeader : String -> String
schHeader chez
  = "#!" ++ chez ++ " --script\n\n" ++
    "(case (machine-type)\n" ++
    "  [(i3le ti3le a6le ta6le) (load-shared-object \"libc.so.6\")]\n" ++
    "  [(i3osx ti3osx a6osx ta6osx) (load-shared-object \"libc.dylib\")]\n" ++
    "  [else (load-shared-object \"libc.so\")])\n\n" ++
    "(let ()\n"

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
schOp (Neg ty) [x] = op "-" [x]
schOp (LT CharType) [x, y] = boolop "char<?" [x, y]
schOp (LTE CharType) [x, y] = boolop "char<=?" [x, y]
schOp (EQ CharType) [x, y] = boolop "char=?" [x, y]
schOp (GTE CharType) [x, y] = boolop "char>=?" [x, y]
schOp (GT CharType) [x, y] = boolop "char>?" [x, y]
schOp (LT ty) [x, y] = boolop "<" [x, y]
schOp (LTE ty) [x, y] = boolop "<=" [x, y]
schOp (EQ ty) [x, y] = boolop "=" [x, y]
schOp (GTE ty) [x, y] = boolop ">=" [x, y]
schOp (GT ty) [x, y] = boolop ">" [x, y]
schOp StrLength [x] = op "string-length" [x]
schOp StrHead [x] = op "string-ref" [x, "0"]
schOp StrTail [x] = op "substring" [x, "1", op "string-length" [x]]
schOp StrCons [x, y] = op "string-cons" [x, y]
schOp StrAppend [x, y] = op "string-append" [x, y]
schOp StrReverse [x] = op "string-reverse" [x]

schOp (Cast IntType StringType) [x] = op "number->string" [x]
schOp (Cast IntegerType StringType) [x] = op "number->string" [x]
schOp (Cast DoubleType StringType) [x] = op "number->string" [x]
schOp (Cast CharType StringType) [x] = op "string" [x]

schOp (Cast IntType IntegerType) [x] = x
schOp (Cast DoubleType IntegerType) [x] = op "floor" [x]
schOp (Cast CharType IntegerType) [x] = op "char->integer" [x]
schOp (Cast StringType IntegerType) [x] = op "cast-string-int" [x]

schOp (Cast IntegerType IntType) [x] = x
schOp (Cast DoubleType IntType) [x] = op "floor" [x]
schOp (Cast StringType IntType) [x] = op "cast-string-int" [x]
schOp (Cast CharType IntType) [x] = op "char->integer" [x]

schOp (Cast IntegerType DoubleType) [x] = x
schOp (Cast IntType DoubleType) [x] = x
schOp (Cast StringType DoubleType) [x] = op "cast-string-double" [x]

schOp (Cast IntType CharType) [x] = op "integer->char" [x]

schOp (Cast from to) [x] = "(error \"Invalid cast " ++ show from ++ "->" ++ show to ++ "\")"

data ExtPrim = CCall | SchemeCall | PutStr | GetStr | Unknown Name

Show ExtPrim where
  show CCall = "CCall"
  show SchemeCall = "SchemeCall"
  show PutStr = "PutStr"
  show GetStr = "GetStr"
  show (Unknown n) = "Unknown " ++ show n

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
schConstant (Ch x) = "#\\" ++ cast x
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
  readArgs : SVars vars -> CExp vars -> Core annot String
  readArgs vs tm = pure $ "(blodwen-read-args " ++ !(schExp vs tm) ++ ")"

  tySpec : CExp vars -> Core annot String
  tySpec (CPrimVal IntType) = pure "int"
  tySpec (CPrimVal StringType) = pure "string"
  tySpec (CPrimVal DoubleType) = pure "double"
  tySpec (CCon unit _ []) 
     = if dropNS unit == UN "Unit"
          then pure "void"
          else throw (InternalError ("Can't pass argument of type " ++ show unit ++ " to foreign function"))
  tySpec ty = throw (InternalError ("Can't pass argument of type " ++ show ty ++ " to foreign function"))

  handleRet : String -> String -> String
  handleRet "void" op = op ++ " " ++ mkWorld (schConstructor 0 [])
  handleRet _ op = mkWorld op

  getFArgs : CExp vars -> Core annot (List (CExp vars, CExp vars))
  getFArgs (CCon _ 0 _) = pure []
  getFArgs (CCon _ 1 [ty, val, rest]) = pure $ (ty, val) :: !(getFArgs rest)
  getFArgs arg = throw (InternalError ("Badly formed c call argument list " ++ show arg))

  schExtPrim : SVars vars -> ExtPrim -> List (CExp vars) -> Core annot String
  schExtPrim vs SchemeCall [ret, CPrimVal (Str fn), args, world]
     = pure $ mkWorld ("(apply " ++ fn ++" "
                  ++ !(readArgs vs args) ++ ")")
  schExtPrim vs SchemeCall [ret, fn, args, world]
     = pure $ mkWorld ("(apply (eval (string->symbol " ++ !(schExp vs fn) ++")) "
                  ++ !(readArgs vs args) ++ ")")
  schExtPrim vs CCall [ret, CPrimVal (Str fn), fargs, world]
      = do args <- getFArgs fargs
           argTypes <- traverse tySpec (map fst args)
           retType <- tySpec ret
           argsc <- traverse (schExp vs) (map snd args)
           pure $ handleRet retType ("((foreign-procedure #f " ++ show fn ++ " ("
                    ++ showSep " " argTypes ++ ") " ++ retType ++ ") "
                    ++ showSep " " argsc ++ ")")
  schExtPrim vs CCall [ret, fn, args, world]
      = pure "(error \"bad ffi call\")"
      -- throw (InternalError ("C FFI calls must be to statically known functions (" ++ show fn ++ ")"))
  schExtPrim vs PutStr [arg, world] 
      = pure $ "(display " ++ !(schExp vs arg) ++ ") " ++ mkWorld (schConstructor 0 []) -- code for MkUnit
  schExtPrim vs GetStr [world] 
      = pure $ mkWorld "(get-line (current-input-port))"
  schExtPrim vs (Unknown n) args 
      = throw (InternalError ("Can't compile unknown external primitive " ++ show n))
  schExtPrim vs prim args 
      = throw (InternalError ("Badly formed external primitive " ++ show prim))

  schConAlt : SVars vars -> String -> CConAlt vars -> Core annot String
  schConAlt {vars} vs target (MkConAlt n tag args sc)
      = let vs' = extendSVars args vs in
            pure $ "((" ++ show tag ++ ") "
                        ++ bindArgs 1 args vs' !(schExp vs' sc) ++ ")"
    where
      bindArgs : Int -> (ns : List Name) -> SVars (ns ++ vars) -> String -> String
      bindArgs i [] vs body = body
      bindArgs i (n :: ns) (v :: vs) body 
          = "(let ((" ++ v ++ " " ++ "(vector-ref " ++ target ++ " " ++ show i ++ "))) "
                  ++ bindArgs (i + 1) ns vs body ++ ")"

  schConstAlt : SVars vars -> CConstAlt vars -> Core annot String
  schConstAlt vs (MkConstAlt c exp)
      = pure $ "((" ++ schConstant c ++ ") " ++ !(schExp vs exp) ++ ")"

  schExp : SVars vars -> CExp vars -> Core annot String
  schExp vs (CLocal el) = pure $ lookupSVar el vs
  schExp vs (CRef n) = pure $ schName n
  schExp vs (CLam x sc) 
     = do let vs' = extendSVars [x] vs 
          sc' <- schExp vs' sc
          pure $ "(lambda (" ++ lookupSVar Here vs' ++ ") " ++ sc' ++ ")"
  schExp vs (CLet x val sc) 
     = do let vs' = extendSVars [x] vs
          val' <- schExp vs val
          sc' <- schExp vs' sc
          pure $ "(let ((" ++ lookupSVar Here vs' ++ " " ++ val' ++ ")) " ++ sc' ++ ")"
  schExp vs (CApp x []) 
      = pure $ "(" ++ !(schExp vs x) ++ ")"
  schExp vs (CApp x args) 
      = pure $ "(" ++ !(schExp vs x) ++ " " ++ showSep " " !(traverse (schExp vs) args) ++ ")"
  schExp vs (CCon x tag args) 
      = pure $ schConstructor tag !(traverse (schExp vs) args)
  schExp {vars} vs (COp op args) 
      = pure $ schOp op !(schArgs args)
    where -- oops, no traverse for Vect in Core
      schArgs : Vect n (CExp vars) -> Core annot (Vect n String)
      schArgs [] = pure []
      schArgs (arg :: args) = pure $ !(schExp vs arg) :: !(schArgs args)
  schExp vs (CExtPrim p args) 
      = schExtPrim vs (toPrim p) args
  schExp vs (CForce t) = pure $ "(force " ++ !(schExp vs t) ++ ")"
  schExp vs (CDelay t) = pure $ "(delay " ++ !(schExp vs t) ++ ")"
  schExp vs (CConCase sc alts def) 
      = do tcode <- schExp vs sc
           defc <- maybe (pure Nothing) (\v => pure (Just !(schExp vs v))) def
           pure $ "(let ((sc " ++ tcode ++ ")) (case (get-tag sc) "
                   ++ showSep " " !(traverse (schConAlt vs "sc") alts)
                   ++ schCaseDef defc ++ "))"
  schExp vs (CConstCase sc alts def) 
      = do defc <- maybe (pure Nothing) (\v => pure (Just !(schExp vs v))) def
           pure $ "(case " ++ !(schExp vs sc) ++ " " 
                    ++ showSep " " !(traverse (schConstAlt vs) alts)
                    ++ schCaseDef defc ++ ")"
  schExp vs (CPrimVal c) = pure $ schConstant c
  schExp vs CErased = pure "9999"
  schExp vs (CCrash msg) = pure $ "(error " ++ show msg ++ ")"

schArgs : SVars ns -> String
schArgs [] = ""
schArgs [x] = x
schArgs (x :: xs) = x ++ " " ++ schArgs xs

schDef : Name -> CDef -> Core annot String
schDef n (MkFun args exp)
   = let vs = initSVars args in
         pure $ "(define " ++ schName n ++ " (lambda (" ++ schArgs vs ++ ") "
                    ++ !(schExp vs exp) ++ "))\n"
schDef n (MkError exp)
   = pure $ "(define (" ++ schName n ++ " . any-args) " ++ !(schExp [] exp) ++ ")\n"
schDef n (MkCon t a) = pure "" -- Nothing to compile here

-- Convert the name to scheme code
-- (There may be no code generated, for example if it's a constructor)
getScheme : Defs -> Name -> Core annot String
getScheme defs n
    = case lookupGlobalExact n (gamma defs) of
           Nothing => throw (InternalError ("Compiling undefined name " ++ show n))
           Just d => case compexpr d of
                          Nothing =>
                             throw (InternalError ("No compiled definition for " ++ show n))
                          Just d => schDef n d

export
compileExpr : {auto c : Ref Ctxt Defs} ->
              ClosedTerm -> (outfile : String) -> Core annot ()
compileExpr {annot} tm outfile
    = do ns <- findUsedNames tm
         defs <- get Ctxt
         compdefs <- traverse (getScheme defs) ns
         let code = concat compdefs
         main <- schExp [] !(compileExp tm)
         chez <- coreLift findChez
         support <- readDataFile "chez/support.ss"
         let scm = schHeader chez ++ support ++ code ++ main ++ schFooter
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

