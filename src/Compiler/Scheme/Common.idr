module Compiler.Scheme.Common

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Inline

import Core.Context
import Core.Name
import Core.TT

import Data.List
import Data.Vect

%default covering

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
  schName (PV n d) = "pat--" ++ schName n
  schName (DN _ n) = schName n
  schName (GN g) = schGName g

  schGName : GenName -> String
  schGName (Nested o i) = schName i ++ "--in--" ++ schName o
  schGName (CaseBlock n i) = "case--" ++ schName n ++ "-" ++ show i
  schGName (WithBlock n i) = "with--" ++ schName n ++ "-" ++ show i

-- local variable names as scheme names - we need to invent new names for the locals
-- because there might be shadows in the original expression which can't be resolved
-- by the same scoping rules. (e.g. something that computes \x, x => x + x where the
-- names are the same but refer to different bindings in the scope)
public export
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

export
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
schOp StrIndex [x, i] = op "string-ref" [x, i]
schOp StrCons [x, y] = op "string-cons" [x, y]
schOp StrAppend [x, y] = op "string-append" [x, y]
schOp StrReverse [x] = op "string-reverse" [x]
schOp StrSubstr [x, y, z] = op "string-substr" [x, y, z]

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

public export
data ExtPrim = CCall | SchemeCall | PutStr | GetStr 
             | FileOpen | FileClose | FileReadLine | FileWriteLine | FileEOF
             | NewIORef | ReadIORef | WriteIORef
             | Unknown Name

export
Show ExtPrim where
  show CCall = "CCall"
  show SchemeCall = "SchemeCall"
  show PutStr = "PutStr"
  show GetStr = "GetStr"
  show FileOpen = "FileOpen"
  show FileClose = "FileClose"
  show FileReadLine = "FileReadLine"
  show FileWriteLine = "FileWriteLine"
  show FileEOF = "FileEOF"
  show NewIORef = "NewIORef"
  show ReadIORef = "ReadIORef"
  show WriteIORef = "WriteIORef"
  show (Unknown n) = "Unknown " ++ show n

toPrim : Name -> ExtPrim
toPrim pn@(NS _ n) 
    = cond [(n == UN "prim__schemeCall", SchemeCall),
            (n == UN "prim__cCall", CCall),
            (n == UN "prim__putStr", PutStr),
            (n == UN "prim__getStr", GetStr),
            (n == UN "prim__open", FileOpen),
            (n == UN "prim__close", FileClose),
            (n == UN "prim__readLine", FileReadLine),
            (n == UN "prim__writeLine", FileWriteLine),
            (n == UN "prim__eof", FileEOF),
            (n == UN "prim__newIORef", NewIORef),
            (n == UN "prim__readIORef", ReadIORef),
            (n == UN "prim__writeIORef", WriteIORef)
            ]
           (Unknown pn)
toPrim pn = Unknown pn

export
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

parameters (schExtPrim : {vars : _} -> SVars vars -> ExtPrim -> List (CExp vars) -> Core annot String)
  mutual
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

    schConstAlt : SVars vars -> String -> CConstAlt vars -> Core annot String
    schConstAlt vs target (MkConstAlt c exp)
        = pure $ "((equal? " ++ target ++ " " ++ schConstant c ++ ") " ++ !(schExp vs exp) ++ ")"
      
    -- oops, no traverse for Vect in Core
    schArgs : SVars vars -> Vect n (CExp vars) -> Core annot (Vect n String)
    schArgs vs [] = pure []
    schArgs vs (arg :: args) = pure $ !(schExp vs arg) :: !(schArgs vs args)

    export
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
    schExp vs (COp op args) 
        = pure $ schOp op !(schArgs vs args)
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
             tcode <- schExp vs sc
             pure $ "(let ((sc " ++ tcode ++ ")) (cond " -- ++ !(schExp vs sc) ++ " " 
                      ++ showSep " " !(traverse (schConstAlt vs "sc") alts)
                      ++ schCaseDef defc ++ "))"
    schExp vs (CPrimVal c) = pure $ schConstant c
    schExp vs CErased = pure "'()"
    schExp vs (CCrash msg) = pure $ "(error " ++ show msg ++ ")"

  -- Need to convert the argument (a list of scheme arguments that may
  -- have been constructed at run time) to a scheme list to be passed to apply
  readArgs : SVars vars -> CExp vars -> Core annot String
  readArgs vs tm = pure $ "(blodwen-read-args " ++ !(schExp vs tm) ++ ")"

  fileOp : String -> String
  fileOp op = "(blodwen-file-op (lambda () " ++ op ++ "))"

  -- External primitives which are common to the scheme codegens (they can be
  -- overridden)
  export
  schExtCommon : SVars vars -> ExtPrim -> List (CExp vars) -> Core annot String
  schExtCommon vs SchemeCall [ret, CPrimVal (Str fn), args, world]
     = pure $ mkWorld ("(apply " ++ fn ++" "
                  ++ !(readArgs vs args) ++ ")")
  schExtCommon vs SchemeCall [ret, fn, args, world]
       = pure $ mkWorld ("(apply (eval (string->symbol " ++ !(schExp vs fn) ++")) "
                    ++ !(readArgs vs args) ++ ")")
  schExtCommon vs PutStr [arg, world] 
      = pure $ "(display " ++ !(schExp vs arg) ++ ") " ++ mkWorld (schConstructor 0 []) -- code for MkUnit
  schExtCommon vs GetStr [world] 
      = pure $ mkWorld "(blodwen-get-line (current-input-port))"
  schExtCommon vs FileOpen [file, mode, bin, world]
      = pure $ mkWorld $ fileOp $ "(blodwen-open " 
                                      ++ !(schExp vs file) ++ " "
                                      ++ !(schExp vs mode) ++ " "
                                      ++ !(schExp vs bin) ++ ")"
  schExtCommon vs FileClose [file, world]
      = pure $ "(blodwen-close-port " ++ !(schExp vs file) ++ ") " ++ mkWorld (schConstructor 0 [])
  schExtCommon vs FileReadLine [file, world]
      = pure $ mkWorld $ fileOp $ "(blodwen-get-line " ++ !(schExp vs file) ++ ")"
  schExtCommon vs FileWriteLine [file, str, world]
      = pure $ mkWorld $ fileOp $ "(blodwen-putstring " 
                                        ++ !(schExp vs file) ++ " "
                                        ++ !(schExp vs str) ++ ")"
  schExtCommon vs FileEOF [file, world]
      = pure $ mkWorld $ "(blodwen-eof " ++ !(schExp vs file) ++ ")"
  schExtCommon vs NewIORef [_, val, world]
      = pure $ mkWorld $ "(box " ++ !(schExp vs val) ++ ")"
  schExtCommon vs ReadIORef [_, ref, world]
      = pure $ mkWorld $ "(unbox " ++ !(schExp vs ref) ++ ")"
  schExtCommon vs WriteIORef [_, ref, val, world]
      = pure $ mkWorld $ "(set-box! " 
                           ++ !(schExp vs ref) ++ " " 
                           ++ !(schExp vs val) ++ ")"
  schExtCommon vs (Unknown n) args 
      = throw (InternalError ("Can't compile unknown external primitive " ++ show n))
  schExtCommon vs prim args 
      = throw (InternalError ("Badly formed external primitive " ++ show prim
                                ++ " " ++ show args))

  schArglist : SVars ns -> String
  schArglist [] = ""
  schArglist [x] = x
  schArglist (x :: xs) = x ++ " " ++ schArglist xs

  schDef : Name -> CDef -> Core annot String
  schDef n (MkFun args exp)
     = let vs = initSVars args in
           pure $ "(define " ++ schName n ++ " (lambda (" ++ schArglist vs ++ ") "
                      ++ !(schExp vs exp) ++ "))\n"
  schDef n (MkError exp)
     = pure $ "(define (" ++ schName n ++ " . any-args) " ++ !(schExp [] exp) ++ ")\n"
  schDef n (MkCon t a) = pure "" -- Nothing to compile here
  
-- Convert the name to scheme code
-- (There may be no code generated, for example if it's a constructor)
export
getScheme : (schExtPrim : {vars : _} -> SVars vars -> ExtPrim -> List (CExp vars) -> Core annot String) ->
            Defs -> Name -> Core annot String
getScheme schExtPrim defs n
    = case lookupGlobalExact n (gamma defs) of
           Nothing => throw (InternalError ("Compiling undefined name " ++ show n))
           Just d => case compexpr d of
                          Nothing =>
                             throw (InternalError ("No compiled definition for " ++ show n))
                          Just d => schDef schExtPrim n d



