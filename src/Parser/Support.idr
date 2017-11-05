module Parser.Support

import public Text.Lexer
import public Parser.Lexer
import public Text.Parser

import Core.TT
import Data.List.Views

public export
Rule : Type -> Type
Rule ty = Grammar (TokenData Token) True ty

public export
EmptyRule : Type -> Type
EmptyRule ty = Grammar (TokenData Token) False ty

public export
data ParseError = ParseFail String (Maybe (Int, Int)) (List Token)
                | LexFail (Int, Int, String)
                | FileFail FileError

export
Show ParseError where
  show (ParseFail err loc toks)
      = "Parse error: " ++ err ++ " at " ++ show loc ++ "\n" ++ show toks
  show (LexFail (c, l, str)) 
      = "Lex error at " ++ show (c, l) ++ " input: " ++ str
  show (FileFail err)
      = "File error: " ++ show err

export
runParser : String -> Rule ty -> Either ParseError ty
runParser str p 
    = case lex str of
           Left err => Left $ LexFail err
           Right toks => 
              case parse (do res <- p; eof; pure res) toks of
                   Left (Error err []) => 
                          Left $ ParseFail err Nothing []
                   Left (Error err (t :: ts)) => 
                          Left $ ParseFail err (Just (line t, col t))
                                               (map tok (t :: ts))
                   Right (val, _) => Right val

export
parseFile : (fn : String) -> Rule ty -> IO (Either ParseError ty)
parseFile fn p
    = do Right str <- readFile fn
             | Left err => pure (Left (FileFail err))
         pure (runParser str p)


-- Some basic parsers used by all the intermediate forms

export
location : EmptyRule (Int, Int)
location 
    = do tok <- peek
         pure (line tok, col tok)

export
constant : Rule Constant
constant 
    = terminal (\x => case tok x of
                           Literal i => Just (I i)
                           Keyword "Int" => Just IntType
                           _ => Nothing)

export
intLit : Rule Integer
intLit 
    = terminal (\x => case tok x of
                           Literal i => Just i
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

export
exactIdent : String -> Rule ()
exactIdent req
    = terminal (\x => case tok x of
                           Ident s => if s == req then Just ()
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
unqualifiedName : Rule String
unqualifiedName = identPart

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


