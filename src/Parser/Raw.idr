module Parser.Raw

import Core.TT
import public Parser.Lexer
import public Parser.Combinators
import Data.List.Views

%default total

public export
Rule : Type -> Type
Rule ty = Grammar (TokenData Token) True ty

public export
EmptyRule : Type -> Type
EmptyRule ty = Grammar (TokenData Token) False ty

public export
data ParseError = ParseFail String (Maybe (Int, Int)) (List Token)
                | LexFail (Int, Int, String)

export
Show ParseError where
  show (ParseFail err loc toks)
      = "Parse error: " ++ err ++ " at " ++ show loc ++ "\n" ++ show toks
  show (LexFail (c, l, str)) 
      = "Lex error at " ++ show (c, l) ++ " input: " ++ str

export
runParser : String -> Rule ty -> Either ParseError ty
runParser str p 
    = case lex str of
           Left err => Left $ LexFail err
           Right toks => 
              case parse toks (do res <- p; eof; pure res) of
                   Left (Error err []) => 
                          Left $ ParseFail err Nothing []
                   Left (Error err (t :: ts)) => 
                          Left $ ParseFail err (Just (line t, col t))
                                               (map tok (t :: ts))
                   Right val => Right val

export
location : EmptyRule (Int, Int)
location 
    = do tok <- nextToken
         pure (line tok, col tok)

export
constant : Rule Constant
constant 
    = terminal (\x => case tok x of
                           Literal i => Just (I i)
                           Keyword "Int" => Just IntType
                           _ => Nothing)

export
symbol : String -> Rule ()
symbol req
    = terminal (\x => case tok x of
                           Symbol s => if s == req then Just ()
                                                   else Nothing
                           _ => Nothing)

export
keyword : String -> Rule ()
keyword req
    = terminal (\x => case tok x of
                           Keyword s => if s == req then Just ()
                                                    else Nothing
                           _ => Nothing)

operator : Rule String
operator
    = terminal (\x => case tok x of
                           Symbol s => Just s
                           _ => Nothing)

identPart : Rule String
identPart 
    = terminal (\x => case tok x of
                           Ident str => Just str
                           _ => Nothing)

namespace_ : Rule (List String)
namespace_ = sepBy1 (symbol ".") identPart

export
name : Rule Name
name 
    = do ns <- namespace_ 
         (do symbol ".("
             op <- operator
             symbol ")"
             pure (NS ns (UN op))) <|>
           (pure (mkFullName ns))
  <|> do symbol "("
         op <- operator
         symbol ")"
         pure (UN op)
 where
   mkFullName : List String -> Name
   mkFullName xs with (snocList xs)
     mkFullName [] | Empty = UN "NONE" -- Can't happen :)
     mkFullName ([] ++ [n]) | (Snoc rec) = UN n
     mkFullName (ns ++ [n]) | (Snoc rec) = NS ns (UN n)

mutual
  rawAtom : Rule Raw
  rawAtom 
      = do symbol "\\"; n <- name; symbol ":"; commit
           ty <- raw; symbol "=>"; sc <- raw
           pure (RBind n (Lam ty) sc)
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
