module Parser.Lexer

import public Text.Lexer

%default total

public export
data Token = Ident String
           | Literal Integer
           | StrLit String
           | CharLit String
           | DoubleLit Double
           | Symbol String
           | Keyword String
           | Unrecognised String
           | Comment String
           | EndInput

export
Show Token where
  show (Ident x) = "Ident " ++ x
  show (Literal x) = "Lit " ++ show x
  show (StrLit x) = "Str " ++ show x
  show (CharLit x) = "Char " ++ show x
  show (DoubleLit x) = "Double " ++ show x
  show (Symbol x) = "Sym " ++ x
  show (Keyword x) = "Keyword " ++ x
  show (Unrecognised x) = "BAD_TOKEN " ++ x
  show (Comment x) = "Comment"
  show EndInput = "EndInput"

export
Show (TokenData Token) where
  show t = show (line t, col t, tok t)

comment : Lexer
comment = is '-' <+> is '-' <+> some (isNot '\n') <+> is '\n'

toEndComment : (k : Nat) -> Recognise (k /= 0)
toEndComment Z = empty
toEndComment (S k) 
             = some (pred (\c => c /= '-' && c /= '{')) 
                      <+> toEndComment (S k)
           <|> is '{' <+> is '-' <+> toEndComment (S (S k))
           <|> is '-' <+> is '}' <+> toEndComment k
           <|> is '{' <+> toEndComment (S k)
           <|> is '-' <+> toEndComment (S k)

blockComment : Lexer
blockComment = is '{' <+> is '-' <+> toEndComment 1
              
ident : Lexer
ident = pred startIdent <+> many (pred validIdent)
  where
    startIdent : Char -> Bool
    startIdent '_' = True
    startIdent x = isAlpha x

    validIdent : Char -> Bool
    validIdent '_' = True
    validIdent '\'' = True
    validIdent x = isAlphaNum x

doubleLit : Lexer
doubleLit = digits <+> is '.' <+> digits <+> opt
               (is 'e' <+> opt (is '-' <|> is '+') <+> digits)

-- Reserved words
keywords : List String
keywords = ["data", "module", "where", "let", "in", "do", "record",
            "auto", "implicit", "namespace", "impossible", "case", "of",
            "using", "interface", "implementation", "open", "import",
            "public", "export", "private",
            "infixl", "infixr", "infix", "prefix",
            "Type", "Int", "Integer", "String", "Char", "Double"]

-- Reserved words for internal syntax
special : List String
special = ["%lam", "%pi", "%imppi", "%let"]

-- Special symbols - things which can't be a prefix of another symbol, and
-- don't match 'validSymbol'
export
symbols : List String
symbols 
    = [".(", -- for things such as Foo.Bar.(+)
       "(|", "|)",
       "(", ")", "{", "}", "[", "]", ",", ";", "_", 
       "`(", "`", "~"]

validSymbol : Lexer
validSymbol = some (oneOf ":!#$%&*+./<=>?@\\^|-~")

-- Valid symbols which have a special meaning so can't be operators
export
reservedSymbols : List String
reservedSymbols
    = symbols ++ ["=", "|", "<-", "->", "=>"]

symbolChar : Char -> Bool
symbolChar c = c `elem` unpack ":!#$%&*+./<=>?@\\^|-~"

rawTokens : TokenMap Token
rawTokens = 
    [(comment, Comment),
     (blockComment, Comment)] ++
    map (\x => (exact x, Symbol)) symbols ++
    [(doubleLit, \x => DoubleLit (cast x)),
     (digits, \x => Literal (cast x)),
     (stringLit, \x => StrLit (stripQuotes x)),
     (charLit, \x => CharLit (stripQuotes x)),
     (ident, \x => if x `elem` keywords then Keyword x else Ident x),
     (space, Comment),
     (validSymbol, Symbol),
     (symbol, Unrecognised)]
  where
    stripQuotes : String -> String
    -- ASSUMPTION! Only total because we know we're getting quoted strings.
    stripQuotes = assert_total (strTail . reverse . strTail . reverse)

export
lex : String -> Either (Int, Int, String) (List (TokenData Token))
lex str 
    = case lex rawTokens str of
           -- Add the EndInput token so that we'll have a line and column
           -- number to read when storing spans in the file
           (tok, (l, c, "")) => Right (filter notComment tok ++ 
                                      [MkToken l c EndInput])
           (_, fail) => Left fail
    where
      notComment : TokenData Token -> Bool
      notComment t = case tok t of
                          Comment _ => False
                          _ => True

testLex : String -> String
testLex inp = show (Lexer.lex inp)
