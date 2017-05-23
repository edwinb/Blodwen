module Parser.Lexer

import Parser.Tokenise

%default total

public export
data Token = Ident String
           | Literal Integer
           | StrLit String
           | Symbol String
           | Keyword String
           | Comment String
         
comment : Lexer
comment = predList [is '-', is '-', someNot '\n', is '\n']

ident : Lexer
ident = predList [One startIdent, Many validIdent]
  where
    startIdent : Char -> Bool
    startIdent '_' = True
    startIdent x = isAlpha x

    validIdent : Char -> Bool
    validIdent '_' = True
    validIdent x = isAlphaNum x

keywords : List String
keywords = ["data", "module", "where"]

rawTokens : TokenMap Token
rawTokens = map (\x => (exact x, Keyword)) keywords ++
    [(digits, \x => Literal (cast x)),
     (stringLit, StrLit),
     (ident, Ident),
     (space, Comment),
     (comment, Comment),
     (symbol, Symbol)]

export
lex : String -> Either (Int, Int, String) (List (TokenData Token))
lex str = case Tokenise.lex rawTokens str of
               (tok, (_, _, "")) => Right (filter notComment tok)
               (_, fail) => Left fail
    where
      notComment : TokenData Token -> Bool
      notComment t = case tok t of
                          Comment _ => False
                          _ => True
