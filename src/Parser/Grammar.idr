module Parser.Grammar

%default total

-- TODO: Add some primitives for helping with error messages.
-- e.g. perhaps set a string to state what we're currently trying to 
-- parse, or to say what the next expected token is in words
export
data Grammar : (tok : Type) -> (consumes : Bool) -> Type -> Type where
     Empty : (val : ty) -> Grammar tok False ty
     Terminal : (tok -> Maybe a) -> Grammar tok True a
     Peek : (tok -> Bool) -> Grammar tok False tok
     EOF : Grammar tok False ()

     Fail : String -> Grammar tok c ty
     Commit : Grammar tok False ()

     SeqEat : Grammar tok True a -> Inf (a -> Grammar tok c2 b) ->
              Grammar tok True b
     SeqEmpty : Grammar tok c1 a -> (a -> Grammar tok c2 b) ->
                Grammar tok (c1 || c2) b
     Alt : Grammar tok c1 ty -> Grammar tok c2 ty -> 
           Grammar tok (c1 && c2) ty

public export
inf : Bool -> Type -> Type
inf True t = Inf t
inf False t = t
  
export %inline
(>>=) : Grammar tok c1 a -> inf c1 (a -> Grammar tok c2 b) ->
        Grammar tok (c1 || c2) b
(>>=) {c1 = False} = SeqEmpty
(>>=) {c1 = True} = SeqEat
     
export
(<|>) : Grammar tok c1 ty -> Grammar tok c2 ty -> 
        Grammar tok (c1 && c2) ty
(<|>) = Alt

export
pure : (val : ty) -> Grammar tok False ty
pure = Empty

export
peek : (tok -> Bool) -> Grammar tok False tok
peek = Peek

export
nextToken : Grammar tok False tok
nextToken = peek (const True)

export
terminal : (tok -> Maybe a) -> Grammar tok True a
terminal = Terminal

export
fail : String -> Grammar tok c ty
fail = Fail

export
eof : Grammar tok False ()
eof = EOF

-- Commit to an alternative; if the current branch of an alternative 
-- fails to parse, no more branches will be tried
export
commit : Grammar tok False ()
commit = Commit

data ParseResult : List tok -> (consumes : Bool) -> Type -> Type where
     Failure : {xs : List tok} -> 
               (committed : Bool) ->
               (err : String) -> (rest : List tok) -> ParseResult xs c ty
     EmptyRes : (committed : Bool) ->
                (val : ty) -> (more : List tok) -> ParseResult more False ty
     NonEmptyRes : (committed : Bool) ->
                   (val : ty) -> (more : List tok) ->
                   ParseResult (x :: xs ++ more) c ty 

weakenRes : ParseResult xs c ty -> ParseResult xs (whatever && c) ty
weakenRes (Failure com msg ts) = Failure com msg ts
weakenRes {whatever=True} (EmptyRes com val xs) = EmptyRes com val xs
weakenRes {whatever=False} (EmptyRes com val xs) = EmptyRes com val xs
weakenRes (NonEmptyRes com val more) = NonEmptyRes com val more

shorter : (more : List tok) -> (ys : List tok) -> 
          LTE (S (length more)) (S (length (ys ++ more)))
shorter more [] = lteRefl
shorter more (x :: xs) = LTESucc (lteSuccLeft (shorter more xs))

doParse : (commit : Bool) -> (xs : List tok) -> (act : Grammar tok c ty) -> 
          ParseResult xs c ty
doParse com xs act with (smallerAcc xs)
  doParse com xs (Empty val) | sml = EmptyRes com val xs
  doParse com [] (Fail str) | sml = Failure com str []
  doParse com (x :: xs) (Fail str) | sml = Failure com str (x :: xs)
  doParse com xs Commit | sml = EmptyRes True () xs

  doParse com [] (Terminal f) | sml = Failure com "End of input" []
  doParse com (x :: xs) (Terminal f) | sml 
        = maybe
             (Failure com "Unrecognised token" (x :: xs))
             (\a => NonEmptyRes com {xs=[]} a xs)
             (f x)
  doParse com [] EOF | sml = EmptyRes com () []
  doParse com (x :: xs) EOF | sml 
        = Failure com "Expected end of input" (x :: xs)
  doParse com [] (Peek f) | sml = Failure com "End of input" []
  doParse com (x :: xs) (Peek f) | sml 
        = if f x 
             then EmptyRes com x (x :: xs)
             else Failure com "Unrecognised token" (x :: xs)
  doParse com xs (Alt x y) | sml with (doParse False xs x | sml)
    doParse com xs (Alt x y) | sml | Failure com' msg ts
          = if com' -- If the alternative had committed, don't try the
                    -- other branch (and reset commit flag)
               then Failure com msg ts
               else weakenRes (doParse False xs y | sml)
    -- Successfully parsed the first option, so use the outer commit flag
    doParse com xs (Alt x y) | sml | (EmptyRes _ val xs) 
          = EmptyRes com val xs
    doParse com (z :: (ys ++ more)) (Alt x y) | sml | (NonEmptyRes _ val more) 
          = NonEmptyRes com val more
  doParse com xs (SeqEmpty act next) | (Access morerec)
          = case doParse com xs act | Access morerec of
                 Failure com msg ts => Failure com msg ts
                 EmptyRes com val xs => 
                       case doParse com xs (next val) | (Access morerec) of
                            Failure com' msg ts => Failure com' msg ts
                            EmptyRes com' val xs => EmptyRes com' val xs
                            NonEmptyRes com' val more => NonEmptyRes com' val more
                 NonEmptyRes {x} {xs=ys} com val more => 
                       case (doParse com more (next val) | morerec _ (shorter more ys)) of
                            Failure com' msg ts => Failure com' msg ts
                            EmptyRes com' val _ => NonEmptyRes com' val more
                            NonEmptyRes {x=x1} {xs=xs1} com' val more' =>
                                 rewrite appendAssociative (x :: ys) (x1 :: xs1) more' in
                                         NonEmptyRes com' val more'
  doParse com xs (SeqEat act next) | sml with (doParse com xs act | sml)
    doParse com xs (SeqEat act next) | sml | Failure com' msg ts 
         = Failure com' msg ts
    doParse com (x :: (ys ++ more)) (SeqEat act next) | (Access morerec) | (NonEmptyRes com' val more) 
         = case doParse com' more (next val) | morerec _ (shorter more ys) of
                Failure com' msg ts => Failure com' msg ts
                EmptyRes com' val _ => NonEmptyRes com' val more
                NonEmptyRes {x=x1} {xs=xs1} com' val more' => 
                     rewrite appendAssociative (x :: ys) (x1 :: xs1) more' in
                             NonEmptyRes com' val more'
  -- This next line is not strictly necessary, but it stops the coverage
  -- checker taking a really long time and eating lots of memory...
  doParse _ _ _ | sml = Failure True "Help the coverage checker!" []

public export
data ParseError tok = Error String (List tok)

export
parse : (xs : List tok) -> (act : Grammar tok c ty) -> 
        Either (ParseError tok) ty
parse xs act
    = case doParse False xs act of
           Failure _ msg ts => Left (Error msg ts)
           EmptyRes _ val _ => pure val
           NonEmptyRes _ val _ => pure val
