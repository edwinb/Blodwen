module Parser.Tokenise

%default total -- we're going to have to assert to do this, but things are,
               -- as long as we only export 'Lexer' functions that guarantee
               -- to consume at least one character!

-- A lexer moves along a string until it hits a part of the string that
-- doesn't match the token we're looking for. It returns 'Nothing' if
-- the beginning of the string doesn't match that token at all.
--
-- The reason for implementing it this strange way is that it allows us
-- to use 'substr' to pull out the token and the tail, which means the tokens
-- will be represented at runtime as pointers into the original string,
-- so no allocation is needed.
LexerFn : Type
LexerFn = (idx : Nat) -> (input : String) -> 
        Maybe (String, String)

export
data Lexer = LF LexerFn

endLex : Nat -> String -> Maybe (String, String)
endLex Z str = Nothing
endLex i str = Just (substr 0 i str, substr i (length str) str)

runLex : Nat -> String -> 
         (ok : Char -> Maybe (String, String)) -> 
         (fail : Maybe (String, String)) ->
         Maybe (String, String)
runLex idx "" k fail = fail
runLex idx str k fail
    = if idx >= length str 
         then fail
         else assert_total (k (strIndex str (cast idx)))

predFn : (Char -> Bool) -> LexerFn
predFn p idx str
-- assert_total - we've checked the string isn't empty above, and we're
-- making progress by walking along the string
    = runLex idx str 
          (\c => if p c
                    then assert_total (predFn p (idx + 1) str)
                    else endLex idx str) (endLex idx str)

export
pred : (Char -> Bool) -> Lexer
pred p = LF (predFn p)

export
digits : Lexer
digits = pred isDigit

export
symbol : Lexer
symbol = pred (\x => not (isAlphaNum x) && not (isSpace x))

export
space : Lexer
space = pred isSpace

public export
data Pred = One (Char -> Bool)
          | Some (Char -> Bool)
          | Many (Char -> Bool)

-- keep matching according to a predicate. When one fails,
-- move on to the next. Stop when the predicates run out
-- (Not entirely unlike regular expressions in fact...)
predListFn : List Pred -> LexerFn
predListFn [] idx str = endLex idx str
-- assert_totals justified as above
predListFn (One p :: ps) idx str
    = runLex idx str (\c =>
          if p c
             then (predListFn ps (idx + 1) str)
             else Nothing) Nothing
predListFn (Many p :: ps) idx str
    = runLex idx str (\c =>
          if p c
             then assert_total (predListFn (Many p :: ps) (idx + 1) str)
             else predListFn ps idx str) (predListFn ps idx str)
predListFn (Some p :: ps) idx str
    = runLex idx str (\c =>
          if p c
             then assert_total (predListFn (Many p :: ps) (idx + 1) str)
             else Nothing) Nothing

export
predList : List Pred -> Lexer
predList p = LF (predListFn p)

export
string : Lexer
string = predList [One (== '\"'), Many (/= '\"'), One (== '\"')]

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
           String -> (List (TokenData a), String)
tokenise line col acc tmap str 
    = case getFirstToken tmap str of
           Just (tok, line', col', rest) =>
           -- assert total because getFirstToken must consume something
           -- given a valid lexer
                assert_total (tokenise line' col' (tok :: acc) tmap rest)
           Nothing => (reverse acc, str)
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
    getFirstToken ((LF lex, fn) :: ts) str
        = case lex 0 str of
               Just (tok, rest) => Just (MkToken line col (fn tok),
                                         line + cast (countNLs (unpack tok)), 
                                         getCols tok col, rest)
               Nothing => getFirstToken ts str

export
lex : TokenMap a -> String -> (List (TokenData a), String)
lex = tokenise 0 0 []

data Token = Ident String
           | Literal Integer
           | Symbol String
           | Keyword String
           | Comment String

testMap : TokenMap Token
testMap = [(digits, \x => Literal (cast x)),
           (symbol, Symbol),
           (space, Comment)]

testMap' : TokenMap String
testMap' = [(digits, id),
           (symbol, id),
           (space, id)]

