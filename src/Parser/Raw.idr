module Parser.Raw

import Core.TT
import Parser.Lexer
import Parser.Combinators
import Data.Vect

%default total

export
Rule : Type -> Type
Rule ty = Grammar (TokenData Token) True ty

export
EmptyRule : Type -> Type
EmptyRule ty = Grammar (TokenData Token) False ty

public export
data ParseError = ParseFail String (Maybe (Int, Int))
                | LexFail (Int, Int, String)

runParser : String -> Rule a -> Either ParseError (a, List Token)
runParser str p 
    = case lex str of
           Left err => Left $ LexFail err
           Right toks => 
              case parse toks p of
                   Failure err [] => 
                          Left $ ParseFail err Nothing
                   Failure err (tok :: xs) => 
                          Left $ ParseFail err (Just (line tok, col tok))
                   NonEmptyRes val more => Right (val, map tok more)

location : EmptyRule (Int, Int)
location = do tok <- nextToken
              pure (line tok, col tok)

constant : Rule Constant
constant = terminal (\x => case tok x of
                           Literal i => Just (I i)
                           Keyword "Int" => Just IntType
                           _ => Nothing)

symbol : String -> Rule ()
symbol req = 
       terminal (\x => case tok x of
                            Symbol s => if s == req then Just ()
                                                    else Nothing
                            _ => Nothing)

term : Rule Integer
term = do t <- Terminal (isLiteral . tok)
          Empty t
  where
    isLiteral : Token -> Maybe Integer
    isLiteral (Literal i) = Just i
    isLiteral _ = Nothing

terms : Rule Integer
terms = do t <- term
           dbl <- pure (t * 2) -- gratuitous empty rule
           (do ts <- terms
               pure (t + ts)) <|> pure dbl


