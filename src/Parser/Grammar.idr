module Parser.TT

import Parser.Lexer

%default total

public export
data Grammar : (tok : Type) -> (consumes : Bool) -> Type -> Type where
     Empty : (val : ty) -> Grammar tok False ty
     Terminal : (tok -> Bool) -> Grammar tok True tok

     (>>=) : Grammar tok True a -> Inf (a -> Grammar tok c2 b) ->
             Grammar tok True b
     (<|>) : Grammar tok c1 ty -> Grammar tok c2 ty -> 
             Grammar tok (c1 && c2) ty

public export
data ParseResult : List tok -> (consumes : Bool) -> Type -> Type where
     Failure : ParseResult xs c ty
     EmptyRes : (val : ty) -> (more : List tok) -> ParseResult more False ty
     NonEmptyRes : (val : ty) -> (more : List tok) ->
                   ParseResult (x :: xs ++ more) c ty 

weakenRes : ParseResult xs c ty -> ParseResult xs (whatever && c) ty
weakenRes Failure = Failure
weakenRes {whatever=True} (EmptyRes val xs) = EmptyRes val xs
weakenRes {whatever=False} (EmptyRes val xs) = EmptyRes val xs
weakenRes (NonEmptyRes val more) = NonEmptyRes val more

shorter : (more : List tok) -> (ys : List tok) -> 
          LTE (S (length more)) (S (length (ys ++ more)))
shorter more [] = lteRefl
shorter more (x :: xs) = LTESucc (lteSuccLeft (shorter more xs))

export total
parse : (xs : List tok) -> (act : Grammar tok c ty) -> ParseResult xs c ty
parse xs act with (smallerAcc xs)
  parse xs (Empty val) | smaller = EmptyRes val xs
  parse [] (Terminal f) | smaller = Failure
  parse (x :: xs) (Terminal f) | smaller 
        = if f x 
             then NonEmptyRes {xs=[]} x xs
             else Failure
  parse xs (x <|> y) | smaller with (parse xs x | smaller)
    parse xs (x <|> y) | smaller | Failure 
          = weakenRes (parse xs y | smaller)
    parse xs (x <|> y) | smaller | (EmptyRes val xs) 
          = EmptyRes val xs
    parse (z :: (ys ++ more)) (x <|> y) | smaller | (NonEmptyRes val more) 
          = NonEmptyRes val more
  parse xs (act >>= next) | smaller with (parse xs act | smaller)
    parse xs (act >>= next) | smaller | Failure = Failure
    parse (x :: (ys ++ more)) (act >>= next) | (Access morerec) | (NonEmptyRes val more) 
         = case parse more (next val) | morerec _ (shorter more ys) of
                Failure => Failure
                EmptyRes val _ => NonEmptyRes val more
                NonEmptyRes {x=x1} {xs=xs1} val more' => 
                     rewrite appendAssociative (x :: ys) (x1 :: xs1) more' in
                             NonEmptyRes val more'

