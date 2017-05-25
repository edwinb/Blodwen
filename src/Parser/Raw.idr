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
data ParseError = ParseFail String (Maybe (Int, Int))
                | LexFail (Int, Int, String)

export
runParser : String -> Rule ty -> Either ParseError ty
runParser str p 
    = case lex str of
           Left err => Left $ LexFail err
           Right toks => 
              case parse toks p of
                   Left (Error err []) => 
                          Left $ ParseFail err Nothing
                   Left (Error err (tok :: xs)) => 
                          Left $ ParseFail err (Just (line tok, col tok))
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

