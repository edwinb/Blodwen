module Parser.Grammar

import Parser.Lexer

%default total

public export
data Grammar : (tok : Type) -> (consumes : Bool) -> Type -> Type where
     Empty : (val : ty) -> Grammar tok False ty
     Terminal : (tok -> Bool) -> Grammar tok True tok

     SeqEat : Grammar tok True a -> Inf (a -> Grammar tok c2 b) ->
              Grammar tok True b
     SeqEmpty : Grammar tok c1 a -> (a -> Grammar tok c2 b) ->
                Grammar tok (c1 || c2) b
     (<|>) : Grammar tok c1 ty -> Grammar tok c2 ty -> 
             Grammar tok (c1 && c2) ty

public export
inf : Bool -> Type -> Type
inf True t = Inf t
inf False t = t
  
public export %inline
(>>=) : Grammar tok c1 a -> inf c1 (a -> Grammar tok c2 b) ->
        Grammar tok (c1 || c2) b
(>>=) {c1 = False} = SeqEmpty
(>>=) {c1 = True} = SeqEat

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
  parse xs (Empty val) | sml = EmptyRes val xs
  parse [] (Terminal f) | sml = Failure
  parse (x :: xs) (Terminal f) | sml 
        = if f x 
             then NonEmptyRes {xs=[]} x xs
             else Failure
  parse xs (x <|> y) | sml with (parse xs x | sml)
    parse xs (x <|> y) | sml | Failure 
          = weakenRes (parse xs y | sml)
    parse xs (x <|> y) | sml | (EmptyRes val xs) 
          = EmptyRes val xs
    parse (z :: (ys ++ more)) (x <|> y) | sml | (NonEmptyRes val more) 
          = NonEmptyRes val more
  parse xs (SeqEmpty act next) | (Access morerec)
          = case parse xs act | Access morerec of
                 Failure => Failure
                 EmptyRes val xs => 
                       case parse xs (next val) | (Access morerec) of
                            Failure => Failure
                            EmptyRes val xs => EmptyRes val xs
                            NonEmptyRes val more => NonEmptyRes val more
                 NonEmptyRes {x} {xs=ys} val more => 
                       case (parse more (next val) | morerec _ (shorter more ys)) of
                            Failure => Failure
                            EmptyRes val _ => NonEmptyRes val more
                            NonEmptyRes {x=x1} {xs=xs1} val more' =>
                                 rewrite appendAssociative (x :: ys) (x1 :: xs1) more' in
                                         NonEmptyRes val more'
  parse xs (SeqEat act next) | sml with (parse xs act | sml)
    parse xs (SeqEat act next) | sml | Failure = Failure
    parse (x :: (ys ++ more)) (SeqEat act next) | (Access morerec) | (NonEmptyRes val more) 
         = case parse more (next val) | morerec _ (shorter more ys) of
                Failure => Failure
                EmptyRes val _ => NonEmptyRes val more
                NonEmptyRes {x=x1} {xs=xs1} val more' => 
                     rewrite appendAssociative (x :: ys) (x1 :: xs1) more' in
                             NonEmptyRes val more'

