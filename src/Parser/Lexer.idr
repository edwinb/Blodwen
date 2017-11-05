module Parser.Lexer

import public Text.Lexer

%default total

public export
data Token = Ident String
           | Literal Integer
           | StrLit String
           | CharLit String
           | Symbol String
           | Keyword String
           | Unrecognised String
           | Comment String

export
Show Token where
  show (Ident x) = "Ident " ++ x
  show (Literal x) = "Lit " ++ show x
  show (StrLit x) = "Str " ++ show x
  show (CharLit x) = "Char " ++ show x
  show (Symbol x) = "Sym " ++ x
  show (Keyword x) = "Keyword " ++ x
  show (Unrecognised x) = "BAD_TOKEN " ++ x
  show (Comment x) = "Comment"

comment : Lexer
comment = is '-' <+> is '-' <+> some (isNot '\n') <+> is '\n'

ident : Lexer
ident = pred startIdent <+> many (pred validIdent)
  where
    startIdent : Char -> Bool
    startIdent '_' = True
    startIdent x = isAlpha x

    validIdent : Char -> Bool
    validIdent '_' = True
    validIdent x = isAlphaNum x

-- Reserved words
keywords : List String
keywords = ["data", "module", "where", "let", "in", 
            "implicit",
            "Type", "Int"]

-- Reserved words for internal syntax
special : List String
special = ["%lam", "%pi", "%imppi", "%let"]

-- Reserved symbols (thing which can't be used a a prefix of other symbols)
symbols : List String
symbols = [".(", -- for things such as Foo.Bar.(+)
           ".", "%",
           "(", ")", "{", "}", "[", "]", "`", ",", "|", ";", "_",
           "->", "=>"]

validSymbol : Lexer
validSymbol = some (oneOf ":!#$%&*+./<=>?@\\^|-~")

rawTokens : TokenMap Token
rawTokens = 
   map (\x => (exact x, Keyword)) special ++
   map (\x => (exact x, Symbol)) symbols ++
    [(intLit, \x => Literal (cast x)),
     (stringLit, StrLit),
     (charLit, CharLit),
     (ident, \x => if x `elem` keywords then Keyword x else Ident x),
     (space, Comment),
     (comment, Comment),
     (validSymbol, Symbol),
     (symbol, Unrecognised)]

export
lex : String -> Either (Int, Int, String) (List (TokenData Token))
lex str 
    = case lex rawTokens str of
           (tok, (_, _, "")) => Right (filter notComment tok)
           (_, fail) => Left fail
    where
      notComment : TokenData Token -> Bool
      notComment t = case tok t of
                          Comment _ => False
                          _ => True

