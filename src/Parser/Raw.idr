module Parser.Raw

import Core.TT
import Core.RawContext
import public Parser.Support
import public Text.Parser

%default total

export
Show RawTy where
  show (MkRawTy n ty) = show n ++ " : " ++ show ty

export
Show RawData where
  show (MkRawData ty cons) = "data " ++ show ty ++ " " ++ show cons

export
Show RawClause where
  show (MkRawClause pvs lhs rhs)
       = show pvs ++ " . " ++ show lhs ++ " = " ++ show rhs

export
Show RawFnDef where
  show (MkRawFn n ty cs) = show n ++ " : " ++ show ty ++ " " ++ show cs

export
Show RawDecl where
  show (FnDecl fn) = show fn
  show (DataDecl d) = show d

mutual
  rawAtom : Rule Raw
  rawAtom 
      = do symbol "\\"; n <- name; symbol ":"; commit
           ty <- raw; symbol "=>"; sc <- raw
           pure (RBind n (Lam ty) sc)
    <|> do symbol "("; n <- name; symbol ":"; commit; 
           ty <- raw; symbol ")"
           symbol "->"; sc <- raw
           pure (RBind n (Pi Explicit ty) sc)
    <|> do symbol "{"; n <- name; symbol ":"; commit; 
           ty <- raw; symbol "}"
           symbol "->"; sc <- raw
           pure (RBind n (Pi Implicit ty) sc)
    <|> do keyword "let"; commit
           n <- name; symbol ":"; ty <- raw
           symbol "="; val <- raw
           keyword "in"; sc <- raw
           pure (RBind n (Let val ty) sc)
    <|> do symbol "("; commit; 
           tm <- raw; symbol ")"
           pure tm
    <|> do keyword "Type"
           pure RType
    <|> do c <- constant
           pure (RPrimVal c)
    <|> do n <- name
           pure (RVar n)

  export
  raw : Rule Raw
  raw 
      = do f <- rawAtom
           args <- many rawAtom
           pure (rawApply f args)

tyDecl : Rule (Name, Raw)
tyDecl
    = do n <- name; symbol ":"; commit
         ty <- raw
         pure (n, ty)

patList : Rule (List (Name, Raw))
patList
    = do symbol "["
         ps <- sepBy (symbol ",") tyDecl
         symbol "]"
         pure ps

clause : Rule RawClause
clause 
    = do ps <- patList
         lhs <- raw
         symbol "="
         rhs <- raw
         symbol ";"
         pure (MkRawClause ps lhs rhs)


dataDecl : Rule RawData
dataDecl 
    = do keyword "data"; commit
         d <- tyDecl
         keyword "where"
         symbol "{"
         cons <- sepBy (symbol "|") tyDecl 
         symbol "}"
         pure (MkRawData (MkRawTy (fst d) (snd d))
                  (map (\ (n, ty) => MkRawTy n ty) cons))
           
fnDecl : Rule RawFnDef
fnDecl
    = do td <- tyDecl; symbol ";"
         cs <- many clause
         pure (MkRawFn (fst td) (snd td) cs)

rawDecl : Rule RawDecl
rawDecl
    = do d <- dataDecl
         pure (DataDecl d)
  <|> do f <- fnDecl
         pure (FnDecl f)

export
prog : Rule (List RawDecl)
prog = some rawDecl 

