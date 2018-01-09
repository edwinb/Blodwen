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

export
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

export
IndentInfo : Type
IndentInfo = Int

export
init : IndentInfo
-- init = MkIndent [0] False
init = 0 -- MkIndent [0] False

column : EmptyRule Int
column
    = do (line, col) <- location
         pure col

-- -- Fail if this is the end of a block entry or end of file
export
continue : (indent : IndentInfo) -> EmptyRule ()
continue indent
    = do col <- column
         if (col <= indent)
            then fail "No more args"
            else pure ()

data ValidIndent 
     = AnyIndent -- In {}, entries can begin in any column
     | AtPos Int -- Entry must begin in a specific column
     | AfterPos Int -- Entry can begin in this column or later
     | EndOfBlock -- Block is finished

checkValid : ValidIndent -> Int -> EmptyRule ()
checkValid AnyIndent c = pure ()
checkValid (AtPos x) c = if c == x
                            then pure ()
                            else fail "Invalid indentation"
checkValid (AfterPos x) c = if c >= x
                               then pure ()
                               else fail "Invalid indentation"
checkValid EndOfBlock c = fail "End of block"

-- Any token which indicates the end of a statement/block
isTerminator : Token -> Bool
isTerminator (Symbol ";") = True
isTerminator (Symbol "}") = True
isTerminator (Keyword "in") = True
isTerminator _ = False

-- Check we're at the end of a block entry, given the start column
-- of the block.
-- It's the end if we have a terminating token, or the next token starts 
-- in or before indent. Works by looking ahead but not consuming.
export
atEnd : (indent : IndentInfo) -> EmptyRule ()
atEnd indent
    = eof
  <|> do nextIs (isTerminator . tok)
         pure ()
  <|> do col <- column
         if (col <= indent)
            then pure ()
            else fail "Not the end of a block entry"

-- Parse a terminator, return where the next block entry
-- must start, given where the current block entry started
terminator : ValidIndent -> Int -> EmptyRule ValidIndent
terminator valid laststart
    = do eof
         pure EndOfBlock
  <|> do symbol ";"
         pure (afterSemi valid)
  <|> do col <- column
         afterDedent valid col
  <|> pure EndOfBlock
 where
   -- Expected indentation for the next token can either be anything (if 
   -- we're inside a brace delimited block) or anywhere after the initial 
   -- column (if we're inside an indentation delimited block)
   afterSemi : ValidIndent -> ValidIndent
   afterSemi AnyIndent = AnyIndent -- in braces, anything goes
   afterSemi (AtPos c) = AfterPos c -- not in braces, after the last start position
   afterSemi (AfterPos c) = AfterPos c
   afterSemi EndOfBlock = EndOfBlock

   -- Expected indentation for the next token can either be anything (if 
   -- we're inside a brace delimited block) or in exactly the initial column 
   -- (if we're inside an indentation delimited block)
   afterDedent : ValidIndent -> Int -> EmptyRule ValidIndent
   afterDedent AnyIndent col
       = if col <= laststart
            then pure AnyIndent
            else fail "Not the end of a block entry"
   afterDedent (AfterPos c) col
       = if col <= laststart
            then pure (AtPos c)
            else fail "Not the end of a block entry"
   afterDedent (AtPos c) col
       = if col <= laststart
            then pure (AtPos c)
            else fail "Not the end of a block entry"
   afterDedent EndOfBlock col = pure EndOfBlock

-- Parse an entry in a block
blockEntry : ValidIndent -> (IndentInfo -> Rule ty) -> 
             Rule (ty, ValidIndent)
blockEntry valid rule
    = do col <- column
         checkValid valid col
         p <- rule col
         valid' <- terminator valid col
         pure (p, valid')

blockEntries : ValidIndent -> (IndentInfo -> Rule ty) ->
               EmptyRule (List ty)
blockEntries valid rule
    = do res <- blockEntry valid rule
         ts <- blockEntries (snd res) rule
         pure (fst res :: ts)
   <|> pure []

export
block : (IndentInfo -> Rule ty) -> EmptyRule (List ty)
block item
    = do symbol "{"
         commit
         ps <- blockEntries AnyIndent item
         symbol "}"
         pure ps
  <|> do col <- column
         blockEntries (AtPos col) item

export
nonEmptyBlock : (IndentInfo -> Rule ty) -> Rule (List ty)
nonEmptyBlock item
    = do symbol "{"
         commit
         res <- blockEntry AnyIndent item
         ps <- blockEntries (snd res) item
         symbol "}"
         pure (fst res :: ps)
  <|> do col <- column
         res <- blockEntry (AtPos col) item
         ps <- blockEntries (snd res) item
         pure (fst res :: ps)


