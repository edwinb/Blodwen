module Parser.Tokenise

%default total

export
data Recognise : (consumes : Bool) -> Type where
     Empty : Recognise False
     Fail : Recognise c
     Pred : (Char -> Bool) -> Recognise True
     SeqEat : Recognise True -> Inf (Recognise e) -> Recognise True
     SeqEmpty : Recognise e1 -> Recognise e2 -> Recognise (e1 || e2)
     Alt : Recognise e1 -> Recognise e2 -> Recognise (e1 && e2)

public export
Lexer : Type
Lexer = Recognise True

public export
inf : Bool -> Type -> Type
inf True t = Inf t
inf False t = t
  
export %inline
(<+>) : {c1 : Bool} -> 
        Recognise c1 -> inf c1 (Recognise c2) -> Recognise (c1 || c2)
(<+>) {c1 = False} = SeqEmpty
(<+>) {c1 = True} = SeqEat
     
export
(<|>) : Recognise c1 -> Recognise c2 -> Recognise (c1 && c2)
(<|>) = Alt

export
is : Char -> Lexer
is x = Pred (==x)

export
isNot : Char -> Lexer
isNot x = Pred (/=x)

export
some : Lexer -> Lexer
some l = l <+> (some l <|> Empty)

export
many : Lexer -> Recognise False
many l = some l <|> Empty

export
any : Lexer
any = Pred (const True)

export
empty : Recognise False
empty = Empty

export
pred : (Char -> Bool) -> Lexer
pred = Pred

export
oneOf : String -> Lexer
oneOf cs = pred (\x => x `elem` unpack cs)

-- If the string is recognised, returns the index at which the token
-- ends
scan : Recognise c -> Nat -> String -> Maybe Nat
scan Empty idx str = pure idx
scan Fail idx str = Nothing
scan (Pred f) idx str = assert_total $
      if idx >= length str
         then Nothing
         else if f (strIndex str (cast idx))
                 then Just (idx + 1)
                 else Nothing
scan (SeqEat r1 r2) idx str 
    = do idx' <- scan r1 idx str
         -- TODO: Can we prove totality instead by showing idx has increased?
         assert_total (scan r2 idx' str)
scan (SeqEmpty r1 r2) idx str 
    = do idx' <- scan r1 idx str
         scan r2 idx' str
scan (Alt r1 r2) idx str 
    = case scan r1 idx str of
           Nothing => scan r2 idx str
           Just idx => Just idx

takeToken : Lexer -> String -> Maybe (String, String)
takeToken lex str 
    = do i <- scan lex 0 str -- i must be > 0 if successful
         pure (substr 0 i str, substr i (length str) str)

export
digits : Lexer
digits = some (Pred isDigit)

export
exact : String -> Lexer
exact str with (unpack str)
  exact str | [] = Fail -- Not allowed, Lexer has to consume
  exact str | (x :: xs) 
      = foldl SeqEmpty (is x) (map is xs)

export
space : Lexer
space = some (pred isSpace)

export
symbol : Lexer
symbol = some (pred (\x => not (isAlphaNum x) && not (isSpace x)))

strChar : Lexer
strChar = (is '\\' <+> any) <|> isNot '"'

export
stringLit : Lexer
stringLit = is '"' <+> many strChar <+> is '"'

export
charLit : Lexer
charLit = is '\'' <+> strChar <+> is '\''

export
intLit : Lexer
intLit = (is '-' <|> Empty) <+> digits

public export
TokenMap : Type -> Type
TokenMap ty = List (Lexer, String -> ty)

public export
record TokenData a where
  constructor MkToken
  line : Int
  col : Int
  tok : a

tokenise : (line : Int) -> (col : Int) ->
           List (TokenData a) -> TokenMap a -> 
           String -> (List (TokenData a), (Int, Int, String))
tokenise line col acc tmap str 
    = case getFirstToken tmap str of
           Just (tok, line', col', rest) =>
           -- assert total because getFirstToken must consume something
                assert_total (tokenise line' col' (tok :: acc) tmap rest)
           Nothing => (reverse acc, (line, col, str))
  where
    countNLs : List Char -> Nat
    countNLs str = List.length (filter (== '\n') str)

    getCols : String -> Int -> Int
    getCols x c 
         = case span (/= '\n') (reverse x) of
                (incol, "") => c + cast (length incol)
                (incol, _) => cast (length incol)

    getFirstToken : TokenMap a -> String -> Maybe (TokenData a, Int, Int, String)
    getFirstToken [] str = Nothing
    getFirstToken ((lex, fn) :: ts) str
        = case takeToken lex str of
               Just (tok, rest) => Just (MkToken line col (fn tok),
                                         line + cast (countNLs (unpack tok)), 
                                         getCols tok col, rest)
               Nothing => getFirstToken ts str

export
lex : TokenMap a -> String -> (List (TokenData a), (Int, Int, String))
lex = tokenise 0 0 []

{-
testMap : TokenMap String
testMap = [(space, id),
           (charLit, show),
           (intLit, show),
           (stringLit, id)]
           -}

